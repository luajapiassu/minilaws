"""minilaws: a tiny dependent-type proof checker (Curry-Howard) for AI-edited code.

Types are statements, programs are proofs, type checking is proof checking.
Kernel: Pi types, a predicative universe hierarchy (Type i : Type i+1), and strictly
positive inductive types with generated recursors (= induction). Nat and Eq are ordinary
inductives in the prelude. No general recursion, so every term terminates and the checker
can't be fooled by a looping "proof".

Two layers:
  - elaborator (untrusted for proofs): fills in {implicit} arguments by unification;
  - kernel (trusted): re-checks the fully explicit result. A buggy elaborator can only
    cause a proof to be rejected, never accepted. It does elaborate the *statements*
    too, and the kernel only checks that a statement is well-formed, not that it says
    what was written: for statements, the elaborator is trusted.

File syntax:
    def name : T := t        -- definition (code)
    law name : T             -- obligation; must get a `proof` later
    proof name := t          -- discharges a law
    theorem name : T := t    -- law + proof in one go
    {x : A} -> B             -- implicit argument, inferred at use sites
    fun {x} => t             -- binds an implicit argument by name
    @f a b                   -- pass f's implicit arguments explicitly
"""
import ast
import io
import os
import re
import subprocess
import sys
import tarfile
import tempfile
import threading
import tomllib
from dataclasses import dataclass, field, replace
from pathlib import Path


# ---------- terms (de Bruijn indices) ----------

@dataclass(frozen=True)
class Var:
    i: int
    explicit: bool = field(default=False, compare=False)  # surface `@x`: pass x's implicits by hand

@dataclass(frozen=True)
class Sort:
    level: int

@dataclass(frozen=True)
class Const:
    name: str

@dataclass(frozen=True)
class Pi:
    name: str
    dom: object
    body: object
    implicit: bool = False

@dataclass(frozen=True)
class Lam:
    name: str
    dom: object  # None = unannotated, only allowed in checking position
    body: object
    implicit: bool = False

@dataclass(frozen=True)
class App:
    fn: object
    arg: object

@dataclass(frozen=True)
class Meta:
    """Unknown term the elaborator solves by unification. Never reaches the kernel."""
    i: int


class CheckError(Exception):
    pass


class Mismatch(CheckError):
    pass


class Stuck(Exception):
    """Unification needs a value that isn't known yet; the caller may retry later."""


def shift(t, d, cut=0):
    if d == 0:
        return t
    match t:
        case Var(i):
            return replace(t, i=i + d) if i >= cut else t
        case Pi(_, a, b) | Lam(_, a, b):
            return replace(t, dom=a and shift(a, d, cut), body=shift(b, d, cut + 1))
        case App(f, a):
            return App(shift(f, d, cut), shift(a, d, cut))
    return t


def instantiate(body, arg, j=0):
    """body with Var j := arg (j = binders crossed). Shifts arg only where it lands, so a
    big argument isn't copied at every beta step."""
    match body:
        case Var(i):
            if i == j:
                return shift(arg, j)
            return replace(body, i=i - 1) if i > j else body
        case Pi(_, a, b) | Lam(_, a, b):
            return replace(body, dom=a and instantiate(a, arg, j), body=instantiate(b, arg, j + 1))
        case App(f, a):
            return App(instantiate(f, arg, j), instantiate(a, arg, j))
    return body


def subterms(t, d=0):
    """Yield (subterm, binder depth) for every node, pre-order. An explicit stack, not
    `yield from`: that costs O(depth) per node, cubic on a deep literal like n + 1000."""
    todo = [(t, d)]
    while todo:
        t, d = todo.pop()
        yield t, d
        match t:
            case Pi(_, a, b) | Lam(_, a, b):
                todo.append((b, d + 1))
                if a is not None:
                    todo.append((a, d))
            case App(f, a):
                todo += [(a, d), (f, d)]


def has_meta(t):
    return any(isinstance(x, Meta) for x, _ in subterms(t))


def mentions(t, name):
    return any(x == Const(name) for x, _ in subterms(t))


def replace_consts(t, sub, d=0):
    """Replace constants by terms (shifted under binders). Used to close fresh names."""
    match t:
        case Const(n) if n in sub:
            return shift(sub[n], d)
        case Pi(_, a, b) | Lam(_, a, b):
            return replace(t, dom=a and replace_consts(a, sub, d), body=replace_consts(b, sub, d + 1))
        case App(f, a):
            return App(replace_consts(f, sub, d), replace_consts(a, sub, d))
    return t


def close_pi(binders, body):
    """Build a Pi telescope over fresh-constant binders [(fresh, name, dom, implicit)]."""
    for fresh, name, dom, implicit in reversed(binders):
        body = Pi(name, dom, replace_consts(body, {fresh: Var(0)}), implicit)
    return body


def spine(t):
    args = []
    while isinstance(t, App):
        args.append(t.arg)
        t = t.fn
    return t, args[::-1]


def apply(head, args):
    for a in args:
        head = App(head, a)
    return head


# ---------- kernel ----------

class Env:
    def __init__(self):
        self.types = {}  # name -> type
        self.defs = {}   # name -> body (unfoldable)
        self.laws = {}   # name -> statement still awaiting a proof
        self.metas = {}  # meta id -> solution (None = unsolved)
        self.recursors = {}  # "T.rec"/"T.rec1" -> (n_params, n_minors, n_indices, {ctor: iota info})
        self.n_fresh = 0
        check_source(PRELUDE, self)
        self.prelude_size = len(self.types)

    def whnf(self, t):
        while True:
            head, args = spine(t)
            if isinstance(head, Lam) and args:
                t = apply(instantiate(head.body, args[0]), args[1:])
            elif isinstance(head, Const) and head.name in self.defs:
                t = apply(self.defs[head.name], args)
            elif isinstance(head, Const) and head.name in self.recursors:
                # iota: T.rec params motive minors indices (c params fields) --> minor_c fields ihs
                np, nminors, nidx, ctors = self.recursors[head.name]
                mj = np + 1 + nminors + nidx  # position of the major premise
                if len(args) <= mj:
                    return t
                major = self.whnf(args[mj])
                ch, cargs = spine(major)
                c = ctors.get(ch.name) if isinstance(ch, Const) else None
                if c is None or len(cargs) != np + len(c[1]):
                    return apply(head, args[:mj] + [major] + args[mj + 1:])
                j, field_names, param_names, recs = c
                fields = cargs[np:]
                sub = dict(zip(param_names, cargs[:np])) | dict(zip(field_names, fields))
                fixed = args[: np + 1 + nminors]
                ihs = [apply(head, fixed + [replace_consts(ix, sub) for ix in ixs] + [fields[pos]]) for pos, ixs in recs]
                t = apply(args[np + 1 + j], fields + ihs + args[mj + 1:])
            else:
                return t

    def conv(self, a, b):
        a, b = self.whnf(a), self.whnf(b)
        match a, b:
            case Pi(_, a1, b1), Pi(_, a2, b2):
                return self.conv(a1, a2) and self.conv(b1, b2)
            case Lam(_, _, b1), Lam(_, _, b2):
                return self.conv(b1, b2)
            # eta: f == fun x => f x
            case Lam(_, _, b1), _:
                return self.conv(b1, App(shift(b, 1), Var(0)))
            case _, Lam(_, _, b2):
                return self.conv(App(shift(a, 1), Var(0)), b2)
            case App(f1, x1), App(f2, x2):
                return self.conv(f1, f2) and self.conv(x1, x2)
        return a == b

    def infer(self, ctx, t):
        match t:
            case Var(i):
                return shift(ctx[-1 - i][1], i + 1)
            case Sort(level):
                return Sort(level + 1)
            case Const(name):
                if name not in self.types:
                    raise CheckError(f"unknown name '{name}'")
                return self.types[name]
            case Pi(n, a, b):
                i = self.sort_of(ctx, a)
                j = self.sort_of(ctx + [(n, a)], b)
                return Sort(max(i, j))
            case Lam(n, a, b):
                if a is None:
                    raise CheckError(f"can't infer type of 'fun {n} => ...'; annotate it")
                self.sort_of(ctx, a)
                return Pi(n, a, self.infer(ctx + [(n, a)], b), t.implicit)
            case App(f, x):
                ft = self.whnf(self.infer(ctx, f))
                if not isinstance(ft, Pi):
                    raise CheckError(f"'{show(f, ctx)}' is not a function, it has type {show(ft, ctx)}")
                self.check(ctx, x, ft.dom)
                return instantiate(ft.body, x)
        raise CheckError(f"bad term {t}")

    def check(self, ctx, t, ty):
        if isinstance(t, Lam):
            expected = self.whnf(ty)
            if not isinstance(expected, Pi):
                raise CheckError(f"'fun {t.name} => ...' checked against non-function type {show(ty, ctx)}")
            if t.dom is not None and not self.conv(t.dom, expected.dom):
                raise CheckError(f"binder '{t.name}' annotated {show(t.dom, ctx)}, expected {show(expected.dom, ctx)}")
            return self.check(ctx + [(t.name, expected.dom)], t.body, expected.body)
        got = self.infer(ctx, t)
        if not self.conv(got, ty):
            raise CheckError(
                f"type mismatch in '{show(t, ctx)}'\n  expected: {show(ty, ctx)}\n  got:      {show(got, ctx)}"
            )

    def sort_of(self, ctx, t):
        s = self.whnf(self.infer(ctx, t))
        if not isinstance(s, Sort):
            raise CheckError(f"'{show(t, ctx)}' is not a type")
        return s.level

    def add(self, kind, name, ty, body):
        if name in self.types or (name in self.laws and kind != "proof"):
            raise CheckError(f"'{name}' already declared")
        if kind == "proof":
            if name not in self.laws:
                raise CheckError(f"proof for '{name}' but no such law")
            ty = self.laws[name]
        else:
            ty = self.elab_top(lambda: self.elab_type([], ty)[0])
            self.sort_of([], ty)
        if kind == "law":
            self.laws[name] = ty
            return
        # name isn't in scope yet, so a definition can't call itself (no cheating via loops)
        core = self.elab_top(lambda: self.elab_check([], body, ty))
        self.check([], core, ty)  # trusted re-check of the elaborator's output
        self.types[name] = ty
        self.laws.pop(name, None)
        if kind == "def":
            self.defs[name] = core

    # ---------- inductive types ----------
    # Built "locally nameless": binders are opened into fresh constants ("A%3"), terms are
    # assembled by name, then close_pi turns the constants back into de Bruijn variables.

    def fresh(self, name):
        self.n_fresh += 1
        return f"{name}%{self.n_fresh}"

    def open_telescope(self, t, n=None, names=None):
        binders = []
        while isinstance(t, Pi) and (n is None or len(binders) < n):
            f = names[len(binders)] if names else self.fresh(t.name)
            binders.append((f, t.name, t.dom, t.implicit))
            t = instantiate(t.body, Const(f))
        return binders, t

    def add_inductive(self, name, params, arity, ctors):
        rec_name = f"{name}.rec"
        for n in [name, rec_name, rec_name + "1"] + [c for c, _ in ctors]:
            if n in self.types:
                raise CheckError(f"'{n}' already declared")

        def pis(binders, body):
            for n, a, imp in reversed(binders):
                body = Pi(n, a, body, imp)
            return body

        np = len(params)
        tty = self.elab_top(lambda: self.elab_type([], pis(params, arity))[0])
        ps, rest = self.open_telescope(tty, np)
        idx, result = self.open_telescope(rest)
        if result != Sort(0):
            raise CheckError(f"'{name}' must live in Type 0")
        P = [Const(f) for f, *_ in ps]
        self.types[name] = tty  # in scope for its own constructors

        info = []
        for cname, surface in ctors:
            # constructors take the type's parameters as implicit arguments
            full = self.elab_top(lambda: self.elab_type([], pis([(n, a, True) for n, a, _ in params], surface))[0])
            ctx, t = [], full
            while isinstance(t, Pi):
                if len(ctx) >= np and self.sort_of(ctx, t.dom) > 0:
                    raise CheckError(f"constructor {cname}: field '{t.name}' is too large for Type 0 (universe)")
                ctx, t = ctx + [(t.name, t.dom)], t.body
            _, body = self.open_telescope(full, np, [f for f, *_ in ps])
            fields, res = self.open_telescope(body)
            rh, rargs = spine(res)
            if rh != Const(name) or rargs[:np] != P or len(rargs) != np + len(idx) or any(mentions(a, name) for a in rargs):
                raise CheckError(f"constructor {cname} must return {show(apply(Const(name), P))} (applied to its indices)")
            recs = []
            for pos, (_, _, dom, _) in enumerate(fields):
                h, hargs = spine(dom)
                ok = h == Const(name) and hargs[:np] == P and len(hargs) == np + len(idx)
                if ok and not any(mentions(a, name) for a in hargs):
                    recs.append((pos, hargs[np:]))
                elif mentions(dom, name):
                    raise CheckError(f"constructor {cname}: '{name}' must occur strictly positively (only as a direct field type)")
            self.types[cname] = full
            info.append((cname, fields, rargs[np:], recs))

        # T.rec : {params} -> (motive : (indices) -> T params indices -> Type 0)
        #         -> (one minor premise per constructor) -> {indices} -> (t : T params indices) -> motive indices t
        # T.rec1 is the same with the motive in Type 1 (large elimination: types defined by
        # recursion). Safe without Prop: predicative Martin-Lof type theory allows it.
        ctor_info = {c: (j, [f for f, *_ in fields], [f for f, *_ in ps], recs) for j, (c, fields, _, recs) in enumerate(info)}
        for level in (0, 1):
            motive, major = self.fresh("motive"), self.fresh("t")
            M, I = Const(motive), [Const(f) for f, *_ in idx]
            motive_ty = close_pi(idx + [(major, "t", apply(Const(name), P + I), False)], Sort(level))
            minors = []
            for cname, fields, rix, recs in info:
                fs = [(f, n, d, False) for f, n, d, _ in fields]
                ihs = [(self.fresh("ih"), "ih", apply(M, ixs + [Const(fields[pos][0])]), False) for pos, ixs in recs]
                target = apply(M, rix + [apply(Const(cname), P + [Const(f) for f, *_ in fields])])
                minors.append((self.fresh(cname), cname, close_pi(fs + ihs, target), False))
            rec_ty = close_pi(
                [(f, n, d, True) for f, n, d, _ in ps]
                + [(motive, "motive", motive_ty, False)]
                + minors
                + [(f, n, d, True) for f, n, d, _ in idx]
                + [(major, "t", apply(Const(name), P + I), False)],
                apply(M, I + [Const(major)]),
            )
            self.sort_of([], rec_ty)  # sanity: the generated recursor type is well-formed
            rec = rec_name + "1" * level
            self.types[rec] = rec_ty
            self.recursors[rec] = (np, len(info), len(idx), ctor_info)

    # ---------- elaborator (untrusted: its output is re-checked by the kernel) ----------
    # Metas are created and solved at one context depth; they never cross a binder
    # (see closed()), so a meta's solution is valid wherever the meta occurs, shifted
    # by the number of binders between (`k` below).

    def elab_top(self, f):
        try:
            return self.closed(f())
        except Stuck:
            raise CheckError("could not infer implicit arguments; pass them with @name") from None

    def new_meta(self):
        m = Meta(len(self.metas))
        self.metas[m.i] = None
        return m

    def zonk(self, t, k=0):
        match t:
            case Meta(i) if self.metas.get(i) is not None:
                return self.zonk(shift(self.metas[i], k), k)
            case Pi(_, a, b) | Lam(_, a, b):
                return replace(t, dom=a and self.zonk(a, k), body=self.zonk(b, k + 1))
            case App(f, a):
                return App(self.zonk(f, k), self.zonk(a, k))
        return t

    def closed(self, t):
        """Leaving a binder: everything inside must be solved."""
        t = self.zonk(t)
        if has_meta(t):
            raise Stuck
        return t

    def assign_if_meta(self, a, b, k):
        if a == b:
            return True
        if not isinstance(a, Meta):
            a, b = b, a
        if not isinstance(a, Meta):
            return False
        b = self.zonk(b, k)
        if any(x == a or (isinstance(x, Var) and d <= x.i < d + k) for x, d in subterms(b)):
            raise Stuck  # occurs check / refers to a variable bound after the meta
        self.metas[a.i] = shift(b, -k)
        return True

    def zonk_head(self, t, k):
        """Resolve a solved meta at the head only; unify reaches the rest as it recurses.
        A full zonk at every level is quadratic on a deep term like n + 2000."""
        h, args = spine(t)
        while isinstance(h, Meta) and self.metas.get(h.i) is not None:
            h, more = spine(shift(self.metas[h.i], k))
            args = more + args
        return apply(h, args)

    def unify(self, a, b, k=0):
        a, b = self.zonk_head(a, k), self.zonk_head(b, k)
        if self.assign_if_meta(a, b, k):
            return
        a, b = self.zonk_head(self.whnf(a), k), self.zonk_head(self.whnf(b), k)
        if self.assign_if_meta(a, b, k):
            return
        if isinstance(spine(a)[0], Meta) or isinstance(spine(b)[0], Meta):
            raise Stuck  # ?f x =?= t is higher-order: wait until ?f is known
        match a, b:
            case Pi(_, a1, b1), Pi(_, a2, b2):
                self.unify(a1, a2, k)
                return self.unify(b1, b2, k + 1)
            case Lam(_, _, b1), Lam(_, _, b2):
                return self.unify(b1, b2, k + 1)
            case Lam(_, _, b1), _:  # eta, as in the kernel's conv
                return self.unify(b1, App(shift(b, 1), Var(0)), k + 1)
            case _, Lam(_, _, b2):
                return self.unify(App(shift(a, 1), Var(0)), b2, k + 1)
            case App(f1, x1), App(f2, x2):
                try:
                    self.unify(f1, f2, k)
                    return self.unify(x1, x2, k)
                except Mismatch:
                    pass
        za, zb = self.zonk(a, k), self.zonk(b, k)
        if za != a or zb != b:
            return self.unify(za, zb, k)  # a solved meta deeper in (e.g. a major premise) blocked whnf
        if has_meta(za) or has_meta(zb):
            raise Stuck
        raise Mismatch()

    def unify_at(self, ctx, term, got, want):
        try:
            self.unify(got, want)
        except Mismatch:
            raise CheckError(
                f"type mismatch in '{show(self.zonk(term), ctx)}'\n"
                f"  expected: {show(self.zonk(want), ctx)}\n  got:      {show(self.zonk(got), ctx)}"
            ) from None

    def elab_type(self, ctx, t):
        core, ty = self.elab_infer(ctx, t)
        s = self.whnf(self.zonk(ty))
        if not isinstance(s, Sort):
            raise CheckError(f"'{show(t, ctx)}' is not a type")
        return self.closed(core), s.level

    def elab_infer(self, ctx, t):
        match t:
            case Var(i):
                return t, shift(ctx[-1 - i][1], i + 1)
            case Sort(level):
                return t, Sort(level + 1)
            case Const() | App():
                return self.elab_app(ctx, t, None)
            case Pi(n, a, b):
                ca, i = self.elab_type(ctx, a)
                cb, j = self.elab_type(ctx + [(n, ca)], b)
                return replace(t, dom=ca, body=cb), Sort(max(i, j))
            case Lam(n, a, b):
                if a is None:
                    raise CheckError(f"can't infer type of 'fun {n} => ...'; annotate it")
                ca, _ = self.elab_type(ctx, a)
                cb, tb = self.elab_infer(ctx + [(n, ca)], b)
                return replace(t, dom=ca, body=self.closed(cb)), Pi(n, ca, self.closed(tb), t.implicit)
        raise CheckError(f"bad term {t}")

    def elab_check(self, ctx, t, ty):
        ty_w = self.whnf(self.zonk(ty))
        if isinstance(ty_w, Pi) and ty_w.implicit and not getattr(t, "implicit", False) and not has_meta(ty_w):
            # auto-bind the implicit argument: check `t` under a `fun {x} =>`
            body = self.elab_check(ctx + [(ty_w.name, ty_w.dom)], shift(t, 1), ty_w.body)
            return Lam(ty_w.name, ty_w.dom, self.closed(body), True)
        if isinstance(t, Lam):
            ty = ty_w
            if has_meta(ty):
                if t.dom is None:
                    raise Stuck  # need the binder's type before entering the body
                core, got = self.elab_infer(ctx, t)
                self.unify_at(ctx, t, got, ty)
                return core
            if not isinstance(ty, Pi):
                raise CheckError(f"'fun {t.name} => ...' checked against non-function type {show(ty, ctx)}")
            if t.implicit and not ty.implicit:
                raise CheckError(f"'fun {{{t.name}}}' but the type expects an explicit argument")
            if t.dom is not None and not self.conv(self.elab_type(ctx, t.dom)[0], ty.dom):
                raise CheckError(f"binder '{t.name}' annotated {show(t.dom, ctx)}, expected {show(ty.dom, ctx)}")
            body = self.elab_check(ctx + [(t.name, ty.dom)], t.body, ty.body)
            return Lam(t.name, ty.dom, self.closed(body), ty.implicit)
        if isinstance(t, (Const, App)):
            return self.elab_app(ctx, t, ty)[0]
        core, got = self.elab_infer(ctx, t)
        self.unify_at(ctx, t, got, ty)
        return core

    def elab_app(self, ctx, t, expected):
        head, args = spine(t)
        explicit = (isinstance(head, Const) and head.name.startswith("@")) or (isinstance(head, Var) and head.explicit)
        if isinstance(head, Const):
            name = head.name.lstrip("@")
            if name not in self.types:
                raise CheckError(f"unknown name '{name}'")
            core, fty = Const(name), self.types[name]
        else:
            core, fty = self.elab_infer(ctx, head)
        # Walk the function type: a meta per implicit argument, a placeholder meta per
        # explicit one (its value is the elaborated argument, filled in below).
        core_args, goals = [], []
        for a in args + [None]:
            while True:
                fty = self.whnf(self.zonk(fty))
                if not (isinstance(fty, Pi) and fty.implicit and not explicit):
                    break
                m = self.new_meta()
                core_args.append(m)
                fty = instantiate(fty.body, m)
            if a is None:
                break
            if not isinstance(fty, Pi) and goals:
                # e.g. `Nat.rec (fun _ => A -> B) z s n a`: past n the type is `?motive n`,
                # a Pi only once the motive argument is elaborated
                self.solve_goals(ctx, goals, fty, partial=True)
                fty = self.whnf(self.zonk(fty))
            if not isinstance(fty, Pi):
                raise CheckError(f"'{show(head, ctx)}' applied to too many arguments")
            m = self.new_meta()
            core_args.append(m)
            goals.append((m, a, fty.dom))
            fty = instantiate(fty.body, m)
        if expected is not None:
            goals.insert(0, (None, t, expected))
        self.solve_goals(ctx, goals, fty)
        return apply(core, core_args), fty

    def solve_goals(self, ctx, goals, fty, partial=False):
        """Solve goals in whatever order makes progress; a stuck goal is rolled back and
        retried. partial: stop quietly when stuck, leaving the rest in `goals`."""
        while goals:
            progress = False
            for goal in list(goals):
                m, a, dom = goal
                saved = dict(self.metas)
                try:
                    if m is None:
                        self.unify_at(ctx, a, fty, dom)
                    else:
                        core_a = self.elab_check(ctx, a, dom)
                        if self.metas[m.i] is None:
                            self.metas[m.i] = core_a  # fresh placeholder: skip unify's O(size) zonk + occurs check
                        else:
                            self.unify(m, core_a)
                except Stuck:
                    self.metas = saved
                    continue
                goals.remove(goal)
                progress = True
            if not progress:
                if partial:
                    return
                raise Stuck


PRELUDE = """
inductive Nat : Type 0 where
  | zero : Nat
  | succ : Nat -> Nat
inductive Eq {A : Type 0} (x : A) : A -> Type 0 where
  | refl : Eq x x
theorem Eq.subst : {A : Type 0} -> {x y : A} -> (P : A -> Type 0) -> Eq x y -> P x -> P y :=
  fun P h px => Eq.rec (fun y _ => P y) px h
inductive Empty : Type 0 where
inductive Unit : Type 0 where
  | tt : Unit
def Not : Type 0 -> Type 0 := fun A => A -> Empty
inductive Bool : Type 0 where
  | false : Bool
  | true : Bool
inductive List (A : Type 0) : Type 0 where
  | nil : List A
  | cons : A -> List A -> List A
def Bool.cond : {A : Type 0} -> Bool -> A -> A -> A := fun {A} c t e => Bool.rec (fun _ => A) e t c
def Bool.not : Bool -> Bool := fun b => Bool.cond b false true
def Bool.and : Bool -> Bool -> Bool := fun a b => Bool.cond a b false
def Bool.or : Bool -> Bool -> Bool := fun a b => Bool.cond a true b
def Nat.eqb : Nat -> Nat -> Bool := fun n => Nat.rec (fun _ => Nat -> Bool)
  (fun m => Nat.rec (fun _ => Bool) true (fun _ _ => false) m)
  (fun _ ih m => Nat.rec (fun _ => Bool) false (fun m' _ => ih m') m) n
def Nat.ltb : Nat -> Nat -> Bool := fun n => Nat.rec (fun _ => Nat -> Bool)
  (fun m => Nat.rec (fun _ => Bool) false (fun _ _ => true) m)
  (fun _ ih m => Nat.rec (fun _ => Bool) false (fun m' _ => ih m') m) n
"""


# ---------- pretty printer ----------

def show(t, ctx=()):
    names = [n for n, _ in ctx]
    return _show(t, names)


def _show(t, names):
    match t:
        case Var(i):
            return names[-1 - i] if i < len(names) else f"#{i}"
        case Sort(level):
            return f"Type {level}"
        case Const(name):
            return name.split("%")[0]  # fresh names print as their source name
        case Meta(i):
            return f"?{i}"
        case Pi(n, a, b):
            if t.implicit:
                return f"{{{n} : {_show(a, names)}}} -> {_show(b, names + [n])}"
            if n == "_":
                return f"{_atom(a, names)} -> {_show(b, names + [n])}"
            return f"({n} : {_show(a, names)}) -> {_show(b, names + [n])}"
        case Lam(n, _, b):
            binder = f"{{{n}}}" if t.implicit else n
            return f"fun {binder} => {_show(b, names + [n])}"
        case App(f, x):
            fs = _atom(f, names) if isinstance(f, (Lam, Pi)) else _show(f, names)
            return f"{fs} {_atom(x, names)}"
    return str(t)


def _atom(t, names):
    s = _show(t, names)
    return f"({s})" if isinstance(t, (Pi, Lam, App)) else s


# ---------- parser ----------

TOKEN = re.compile(r"\s+|--[^\n]*|(:=|->|=>|[(){}:|]|@?[A-Za-z_][A-Za-z0-9_.']*|\d+)")
DECLS = {"def", "law", "proof", "theorem", "inductive"}
KEYWORDS = DECLS | {"fun", "Type", "where"}
STOP = {None, ")", "}", "->", ":=", ":", "=>", "|", "where"}


def tokenize(src):
    pos, out = 0, []
    while pos < len(src):
        m = TOKEN.match(src, pos)
        if not m:
            raise CheckError(f"unexpected character {src[pos]!r}")
        if m.group(1):
            out.append(m.group(1))
        pos = m.end()
    return out


def is_name(tok):
    return tok is not None and tok not in KEYWORDS and re.match(r"[A-Za-z_]", tok) is not None


class Parser:
    def __init__(self, tokens):
        self.toks, self.i = tokens, 0

    def peek(self, k=0):
        return self.toks[self.i + k] if self.i + k < len(self.toks) else None

    def eat(self, tok=None):
        t = self.peek()
        if t is None or (tok and t != tok):
            raise CheckError(f"expected {tok!r}, got {t!r}")
        self.i += 1
        return t

    def name(self):
        t = self.eat()
        if not is_name(t):
            raise CheckError(f"expected a name, got {t!r}")
        return t

    def is_binder_group(self):
        k = 1
        while is_name(self.peek(k)):
            k += 1
        return self.peek() in ("(", "{") and k > 1 and self.peek(k) == ":"

    def binder_group(self, scope):
        """'(x y : A)' or '{x y : A}' -> [(x, A, implicit), (y, A shifted, implicit)]."""
        close = {"(": ")", "{": "}"}[self.peek()]
        implicit = self.eat() == "{"
        names = []
        while self.peek() != ":":
            names.append(self.name())
        self.eat(":")
        a = self.expr(scope)
        self.eat(close)
        return [(n, shift(a, k), implicit) for k, n in enumerate(names)]

    def expr(self, scope):
        if self.peek() == "fun":
            self.eat()
            binders = []
            while self.peek() != "=>":
                inner = scope + [n for n, _, _ in binders]
                if self.is_binder_group():
                    binders += self.binder_group(inner)
                elif self.peek() == "{":  # fun {a b} => ...
                    self.eat()
                    while self.peek() != "}":
                        binders.append((self.name(), None, True))
                    self.eat("}")
                else:
                    binders.append((self.name(), None, False))
            self.eat("=>")
            body = self.expr(scope + [n for n, _, _ in binders])
            for n, a, imp in reversed(binders):
                body = Lam(n, a, body, imp)
            return body
        if self.is_binder_group():
            binders = self.binder_group(scope)
            self.eat("->")
            body = self.expr(scope + [n for n, _, _ in binders])
            for n, a, imp in reversed(binders):
                body = Pi(n, a, body, imp)
            return body
        lhs = self.app(scope)
        if self.peek() == "->":
            self.eat()
            return Pi("_", lhs, self.expr(scope + ["_"]))
        return lhs

    def app(self, scope):
        t = self.atom(scope)
        while self.peek() not in STOP and self.peek() not in DECLS:
            t = App(t, self.atom(scope))
        return t

    def atom(self, scope):
        t = self.peek()
        if t == "(":
            self.eat()
            e = self.expr(scope)
            self.eat(")")
            return e
        if t == "Type":
            self.eat()
            return Sort(int(self.eat()) if (self.peek() or "").isdigit() else 0)
        if t == "fun":
            return self.expr(scope)
        explicit = t is not None and t.startswith("@")
        n = self.eat()[1:] if explicit else self.name()
        for i, s in enumerate(reversed(scope)):
            if s == n and s != "_":
                return Var(i, explicit)
        return Const("@" + n if explicit else n)


def parse_expr(src):
    p = Parser(tokenize(src))
    e = p.expr([])
    if p.peek() is not None:
        raise CheckError(f"trailing token {p.peek()!r}")
    return e


def parse_decls(src):
    """Parse a source file into declarations: (kind, name, *payload)."""
    p = Parser(tokenize(src))
    decls = []
    while p.peek() is not None:
        kind = p.eat()
        if kind not in DECLS:
            raise CheckError(f"expected def/law/proof/theorem/inductive, got {kind!r}")
        name = p.name()
        if kind == "inductive":
            params = []
            while p.peek() in ("(", "{"):
                params += p.binder_group([n for n, _, _ in params])
            scope = [n for n, _, _ in params]
            p.eat(":")
            arity = p.expr(scope)
            p.eat("where")
            ctors = []
            while p.peek() == "|":
                p.eat()
                cname = p.name()
                p.eat(":")
                ctors.append((cname, p.expr(scope)))
            decls.append((kind, name, params, arity, ctors))
            continue
        ty = body = None
        if kind != "proof":
            p.eat(":")
            ty = p.expr([])
        if kind != "law":
            p.eat(":=")
            body = p.expr([])
        decls.append((kind, name, ty, body))
    return decls


def add_decl(env, decl):
    kind, name, *payload = decl
    try:
        if kind == "inductive":
            env.add_inductive(name, *payload)
        else:
            env.add(kind, name, *payload)
    except CheckError as e:
        raise CheckError(f"{kind} {name}: {e}") from None


def check_source(src, env=None):
    """Check every declaration in order; returns the Env. Raises CheckError on the first failure."""
    env = env or Env()
    for decl in parse_decls(src):
        add_decl(env, decl)
    return env


# ---------- Python -> minilaws ----------
# Trusted translator for a small, total subset of Python over Nat, bool and list[...]:
#
#     def f(x: Nat, ..., m: Nat) -> Nat:
#         if m == 0:              # optional: structural recursion on parameter m
#             return BASE
#         return STEP             # may call f(..., m - 1, ...) with the other args unchanged
#
# Same with `if not xs:` on a list parameter: STEP may use xs[0], xs[1:] and f(..., xs[1:], ...).
# Any other `if c: return a` / `return b` is `a if c else b` (Bool.cond, no recursion).
# Expressions: parameters, int literals >= 0, `e + <int>`, `m - 1` (in STEP), True/False,
# comparisons of Nats, and/or/not, `a if c else b`, list literals, `[...] + e`, calls to
# functions defined earlier in the same file. Anything else is refused instead of guessed at.
# Types aren't tracked here: a translation that mixes them up (`xs == ys`) fails in the kernel.
# Only `from minilaws import ...` is allowed: any other import could bind a name the checker
# verifies to different code at runtime.

Nat = int  # runtime type for the Python side; the laws speak about n >= 0


def translate_python(src):
    try:
        tree = ast.parse(src)
    except SyntaxError as e:
        raise CheckError(f"line {e.lineno}: Python syntax error: {e.msg}") from None
    out, defined = [], set()
    for i, node in enumerate(tree.body):
        if _is_docstring(node) or (isinstance(node, ast.ImportFrom) and node.module == "minilaws" and not node.level):
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            raise _unsupported(node, "only `from minilaws import ...`")
        if _is_main_block(node):
            if i != len(tree.body) - 1 or node.orelse:
                raise _unsupported(node, '`if __name__ == "__main__":` must be the last statement, with no else')
            _check_no_rebind(node, defined)
            continue  # unchecked script code: runs only as `python app.py`, never on import
        match node:
            case ast.FunctionDef():
                out.append(_translate_fn(node, defined))
            # Nat/bool only: a list constant could be mutated (`XS.append(9)`) after it was checked
            case ast.AnnAssign(target=ast.Name(id=name), annotation=ann, value=e, simple=1) if e and (ty := _py_type(ann)) in ("Nat", "Bool"):
                if name in PRELUDE_NAMES:
                    raise _unsupported(node, f"constant name can't be a prelude name: {name}")
                out.append(f"def {name} : {ty} := {_py_expr(e, name, {}, None, 'plain', defined)}")
            case ast.Assign() | ast.AnnAssign():
                raise _unsupported(node, "constants need a Nat or bool annotation: `K: Nat = 3`")
            case _:
                raise _unsupported(node, 'only functions, annotated constants and a final `if __name__ == "__main__":`')
        defined.add(node.target.id if isinstance(node, ast.AnnAssign) else node.name)
    return "\n".join(out) + "\n"


def _is_main_block(node):
    match node:
        case ast.If(test=ast.Compare(left=ast.Name(id="__name__"), ops=[ast.Eq()], comparators=[ast.Constant(value="__main__")])):
            return True
    return False


def _check_no_rebind(block, defined):
    """Anything bound in the main block can shadow a checked name for the rest of the script.
    Nested scopes are walked too: conservative, and simpler than tracking scopes. Indirect
    writes (`globals()[...] = ...`) aren't caught: like an importer's `app.add = ...`, that's
    code outside what minilaws checks."""
    for n in ast.walk(block):
        names = []
        if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            names = [n.id]
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
            names = [n.name]
        elif isinstance(n, ast.MatchMapping):
            names = [n.rest]
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            names = [(a.asname or a.name).split(".")[0] for a in n.names]
            if "*" in names:
                raise _unsupported(n, "`import *` in the main block could rebind any checked name")
        elif isinstance(n, (ast.Global, ast.Nonlocal)):
            names = n.names
        if hit := sorted(set(names) & defined):
            raise _unsupported(n, f"the main block rebinds checked names: {hit}")


def _unsupported(node, why):
    return CheckError(f"line {node.lineno}: unsupported Python ({why}): {ast.unparse(node).splitlines()[0]}")


def _is_docstring(node):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)


def _py_type(ann):
    """`Nat`, `bool`, `list[T]` -> the minilaws type; None for anything else."""
    match ann:
        case ast.Name(id="Nat"):
            return "Nat"
        case ast.Name(id="bool"):
            return "Bool"
        case ast.Subscript(value=ast.Name(id="list"), slice=elt) if (t := _py_type(elt)):
            return f"(List {t})"
    return None


def _translate_fn(fn, known):
    a = fn.args
    types = {p.arg: _py_type(p.annotation) for p in a.args}
    ret = _py_type(fn.returns)
    if a.vararg or a.kwarg or a.kwonlyargs or a.posonlyargs or a.defaults or fn.decorator_list:
        raise _unsupported(fn, "plain positional parameters only")
    if None in types.values() or ret is None:
        raise _unsupported(fn, "parameters and result must be annotated Nat, bool or list[...] of those")
    if reserved := sorted(types.keys() & PRELUDE_NAMES):
        raise _unsupported(fn, f"parameter names can't be prelude names: {reserved}")
    go = lambda e, rec=None, mode="plain", gen=(): _py_expr(e, fn.name, types, rec, mode, known, gen)
    body = fn.body
    if _is_docstring(body[0]):
        body = body[1:]
    match body:
        case [ast.Return(value=e)]:
            expr = go(e)
        case [ast.If(test=test, body=[ast.Return(value=then)], orelse=orelse), *rest]:
            steps = orelse + rest
            if len(steps) != 1 or not isinstance(steps[0], ast.Return):
                raise _unsupported(fn, "expected `if ...: return ...` then one `return ...`")
            other = steps[0].value
            m = _rec_test(test, types)
            if m is None:
                expr = f"Bool.cond {go(test)} {go(then)} {go(other)}"
            else:
                # An accumulator (another argument changes in the recursive call) needs the
                # other arguments in the motive, so the induction hypothesis is a function of them.
                gen = [p for p in types if p != m] if _changes_others(other, fn.name, list(types), m) else []
                motive = " -> ".join([types[p] for p in gen] + [ret])
                bind = "".join(f" {p}" for p in gen)
                base = f"(fun{bind} => {go(then, m, 'base')})" if gen else go(then, m, "base")
                fields = "pred'" if types[m] == "Nat" else "h' t'"
                rec = "Nat.rec" if types[m] == "Nat" else "List.rec"
                expr = f"{rec} (fun _ => {motive}) {base} (fun {fields} ih'{bind} => {go(other, m, 'step', gen)}) {m}{bind}"
        case _:
            raise _unsupported(fn, "body must be `return e`, or `if ...: return e` then `return e`")
    ty = " -> ".join([*types.values(), ret])
    return f"def {fn.name} : {ty} := " + (f"fun {' '.join(types)} => {expr}" if types else expr)


def _changes_others(e, fn, params, rec):
    """Whether some recursive call passes something other than the same parameter for a non-recursive argument."""
    return any(
        isinstance(c, ast.Call) and isinstance(c.func, ast.Name) and c.func.id == fn and len(c.args) == len(params)
        and any(p != rec and not (isinstance(a, ast.Name) and a.id == p) for p, a in zip(params, c.args))
        for c in ast.walk(e)
    )


def _rec_test(test, types):
    """`m == 0` on a Nat parameter or `not xs` on a list parameter: structural recursion on it."""
    match test:
        case ast.Compare(left=ast.Name(id=m), ops=[ast.Eq()], comparators=[ast.Constant(value=0)]) if types.get(m) == "Nat":
            return m
        case ast.UnaryOp(op=ast.Not(), operand=ast.Name(id=xs)) if types.get(xs, "").startswith("(List"):
            return xs
    return None


MAX_LITERAL = 10_000  # ~2s to check a law over it; 20000 takes ~8s


def _succs(t, c):
    for _ in range(c):
        t = f"(succ {t})"
    return t


def _nat_literal(e):
    return isinstance(e, ast.Constant) and type(e.value) is int and e.value >= 0


COMPARE = {  # a <op> b, Nats only
    ast.Eq: "(Nat.eqb {a} {b})", ast.NotEq: "(Bool.not (Nat.eqb {a} {b}))",
    ast.Lt: "(Nat.ltb {a} {b})", ast.Gt: "(Nat.ltb {b} {a})",
    ast.LtE: "(Bool.not (Nat.ltb {b} {a}))", ast.GtE: "(Bool.not (Nat.ltb {a} {b}))",
}


def _py_expr(e, fn, types, rec, mode, known, gen=()):
    """mode: 'plain' (no recursion), 'base' (rec var is 0 / []), 'step' (rec var is
    succ pred' / cons h' t'). gen: the arguments the induction hypothesis takes (accumulators)."""
    go = lambda x: _py_expr(x, fn, types, rec, mode, known, gen)
    step = mode == "step"
    for lit in (e, getattr(e, "right", None)):
        if _nat_literal(lit) and lit.value > MAX_LITERAL:
            raise _unsupported(e, f"literal above {MAX_LITERAL}: Nat is unary, so checking time grows with its square")
    if _nat_literal(e):
        return _succs("zero", e.value)
    match e:
        case ast.Constant(value=b) if type(b) is bool:
            return "true" if b else "false"
        case ast.Name(id=x) if x in types:
            if x != rec:
                return x
            if types[x] == "Nat":
                return "(succ pred')" if step else "zero"
            return "(cons h' t')" if step else "nil"
        case ast.Name(id=x) if x in known:  # a constant (a bare function name fails in the kernel)
            return x
        case ast.BinOp(left=left, op=ast.Add(), right=right) if _nat_literal(right):
            return _succs(go(left), right.value)
        case ast.BinOp(left=ast.List(elts=elts), op=ast.Add(), right=right):
            return _conses([go(x) for x in elts], go(right))
        case ast.List(elts=elts):
            return _conses([go(x) for x in elts], "nil")
        case ast.BinOp(left=ast.Name(id=x), op=ast.Sub(), right=ast.Constant(value=1)) if x == rec and step:
            return "pred'"
        case ast.Subscript(value=ast.Name(id=x), slice=ast.Constant(value=0)) if x == rec and step:
            return "h'"
        case ast.Subscript(value=ast.Name(id=x), slice=ast.Slice(lower=ast.Constant(value=1), upper=None, step=None)) if x == rec and step:
            return "t'"
        case ast.Compare(left=left, ops=[op], comparators=[right]) if type(op) in COMPARE:
            return COMPARE[type(op)].format(a=go(left), b=go(right))
        case ast.BoolOp(op=op, values=values):
            out = go(values[-1])
            for v in reversed(values[:-1]):
                out = f"({'Bool.and' if isinstance(op, ast.And) else 'Bool.or'} {go(v)} {out})"
            return out
        case ast.UnaryOp(op=ast.Not(), operand=x):
            return f"(Bool.not {go(x)})"
        case ast.IfExp(test=test, body=then, orelse=other):
            return f"(Bool.cond {go(test)} {go(then)} {go(other)})"
        case ast.Call(func=ast.Name(id=f), args=args, keywords=[]) if f == fn:
            params = list(types)
            # go(a) is pred' / t' only for `m - 1` / `xs[1:]` on the recursion variable
            ok = step and len(args) == len(params) and all(
                go(a) in ("pred'", "t'") if p == rec else (p in gen or (isinstance(a, ast.Name) and a.id == p))
                for p, a in zip(params, args)
            )
            if not ok:
                raise _unsupported(e, f"recursion must be {fn}(..., m - 1, ...) after `if m == 0` "
                                      f"or {fn}(..., xs[1:], ...) after `if not xs`")
            return "(" + " ".join(["ih'"] + [go(a) for p, a in zip(params, args) if p in gen]) + ")" if gen else "ih'"
        case ast.Call(func=ast.Name(id=f), args=args, keywords=[]) if f in known:
            return "(" + " ".join([f] + [go(a) for a in args]) + ")"
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name):
        raise _unsupported(e, f"`{e.func.id}` is not a function defined earlier in this file")
    raise _unsupported(e, "only parameters, literals, True/False, `x + <int>`, comparisons, and/or/not, "
                          "`a if c else b`, lists, `m - 1`, `xs[0]`, `xs[1:]` and function calls")


def _conses(heads, tail):
    for h in reversed(heads):
        tail = f"(cons {h} {tail})"
    return tail


def read_source(path):
    text = Path(path).read_text(encoding="utf-8")
    return translate_python(text) if str(path).endswith(".py") else text


PHASE = {"inductive": 0, "def": 0, "law": 1, "theorem": 2, "proof": 2}


def declared_names(decl):
    kind, name, *payload = decl
    if kind == "inductive":
        return {name, f"{name}.rec", f"{name}.rec1"} | {c for c, _ in payload[2]}
    return {name}  # for a proof: the law it makes usable


# a Python parameter with one of these names would shadow the constant in the translation
PRELUDE_NAMES = KEYWORDS | {n for d in parse_decls(PRELUDE) for n in declared_names(d)}


def used_names(decl):
    kind, name, *payload = decl
    if kind == "inductive":
        params, arity, ctors = payload
        terms = [a for _, a, _ in params] + [arity] + [t for _, t in ctors]
    else:
        terms = [t for t in payload if t is not None]
    return {x.name.lstrip("@") for t in terms for x, _ in subterms(t) if isinstance(x, Const)}


def in_check_order(decls):
    """Code, then laws, then proofs; within a phase, each declaration after the ones it
    uses (file order otherwise). So the order of files never matters."""
    out = []
    for phase in (0, 1, 2):
        todo = [(pd, used_names(pd[1]), declared_names(pd[1])) for pd in decls if PHASE[pd[1][0]] == phase]
        here = set().union(*(ds for _, _, ds in todo))
        done = set()
        while todo:
            # ponytail: O(n^2) scan, fine for hand-written files; a real toposort if projects get big
            # no candidate means a cycle (e.g. self-reference): take the first, the checker rejects it
            item = next((it for it in todo if (it[1] & here) - it[2] <= done), todo[0])
            todo.remove(item)
            out.append(item[0])
            done |= item[2]
    return out


def foreign_use(decls):
    """A file with laws is human-owned. Its laws, defs and types may use only the prelude,
    Python code (.py) and its own declarations; anything defined in another .laws file
    (editable by the AI) could change what the laws mean. Returns the first violation."""
    origin = {n: Path(p) for p, d in decls if d[0] != "proof" for n in declared_names(d)}
    homes = {Path(p) for p, d in decls if d[0] == "law"}
    for path, d in decls:
        if Path(path) not in homes or d[0] == "proof":
            continue
        for n in sorted(used_names(d)):
            src = origin.get(n)  # None: prelude
            if src is not None and src.suffix != ".py" and src != Path(path):
                return f"{Path(path).name}: {d[0]} {d[1]}: uses '{n}' from {src.name}; " \
                    "a file with laws may only use the prelude, .py code and its own declarations"
    return None


def deep_stack(f):
    """Run f in a thread with a big stack. Nat is unary, so `n + k` is k nested succs and
    the parser, shift/instantiate and whnf recurse k deep."""
    def run(*args, **kwargs):
        out = []
        def target():
            try:
                out.append((True, f(*args, **kwargs)))
            except BaseException as e:
                out.append((False, e))
        # ponytail: both settings are process-wide while the check runs; fine for a CLI/hook
        old_size, old_limit = threading.stack_size(STACK_BYTES), sys.getrecursionlimit()
        sys.setrecursionlimit(RECURSION_LIMIT)
        try:
            t = threading.Thread(target=target)
            t.start()
            t.join()
        finally:
            threading.stack_size(old_size)
            sys.setrecursionlimit(old_limit)
        ok, value = out[0]
        if not ok:
            raise value
        return value
    return run


STACK_BYTES = 64 << 20  # 256 MB is refused on Windows
RECURSION_LIMIT = 100_000


@deep_stack
def check_files(paths):
    """Check a set of files. Returns (ok, message)."""
    try:
        env, _ = load_files(paths)
    except CheckError as e:
        return False, f"REJECTED: {e}"
    return True, f"OK: {len(env.types) - env.prelude_size} declarations checked"


def load_files(paths):
    """Check a set of files; returns (env, [(path, decl)]). Raises CheckError."""
    def in_file(path, e):
        if isinstance(e, RecursionError):
            e = "term too deep to check (a very large literal?)"
        elif isinstance(e, OSError):
            e = f"can't read it ({e.strerror})"
        return CheckError(f"{Path(path).name}: {e}")

    env = Env()
    decls = []
    for path in paths:
        try:
            decls += [(path, d) for d in parse_decls(read_source(path))]
        except (CheckError, RecursionError, OSError) as e:
            raise in_file(path, e) from None
    for path, d in in_check_order(decls):
        try:
            add_decl(env, d)
        except (CheckError, RecursionError) as e:
            raise in_file(path, e) from None
    if why := foreign_use(decls):
        raise CheckError(why)
    if env.laws:
        raise CheckError("laws without proof: " + ", ".join(env.laws))
    return env, decls


# ---------- comparing against a trusted version (like Lean's comparator) ----------
# The checker proves the code meets the laws; it can't tell whether the laws are still the
# ones a human wrote. So, as Lean's `comparator` does with a challenge file, take the laws
# from a version the change can't touch (a git ref, e.g. the base branch) and require each
# one to mean the same thing now: same statement, same dependencies.

def erase(t):
    """A term without binder names or implicit flags: renaming a binder isn't a change."""
    match t:
        case Pi(_, a, b) | Lam(_, a, b):
            return (type(t).__name__, a and erase(a), erase(b))
        case App(f, a):
            return ("App", erase(f), erase(a))
    return t


def law_specs(env, decls, root):
    """{law: (statement, {dependency: what it is}, statement as printed)}, dependencies taken transitively. A spec
    def or type (from a .laws file) counts in full; code (.py) counts by signature and file,
    because changing the code is the whole point. The prelude never changes."""
    root = Path(root).resolve()
    origin = {n: Path(p).resolve() for p, d in decls if d[0] != "proof" for n in declared_names(d)}
    rel = lambda p: p.relative_to(root).as_posix() if p.is_relative_to(root) else p.name
    ctors = {rec.removesuffix(".rec"): list(info[3]) for rec, info in env.recursors.items() if rec.endswith(".rec")}
    specs = {}
    for _, (kind, name, *_) in decls:
        if kind != "law":
            continue
        deps, todo = {}, [env.types[name]]
        while todo:
            for x, _ in subterms(todo.pop()):
                if not isinstance(x, Const) or x.name in deps or x.name not in origin:
                    continue
                src = origin[x.name]
                if src.suffix == ".py":
                    deps[x.name] = ("code", rel(src), erase(env.types[x.name]))
                    continue
                deps[x.name] = ("spec", rel(src), erase(env.types[x.name]), erase(env.defs.get(x.name)))
                todo += [env.types[x.name], env.defs.get(x.name, Sort(0))] + [Const(c) for c in ctors.get(x.name, [])]
        specs[name] = (erase(env.types[name]), deps, show(env.types[name]))
    return specs


def law_changes(base, head):
    """What changed in the laws from base to head. New laws are fine: they only add duties."""
    out = []
    for name, (stmt, deps, shown) in base.items():
        if name not in head:
            out.append(f"law {name}: removed")
            continue
        now_stmt, now_deps, now_shown = head[name]
        if now_stmt != stmt:
            # as elaborated (implicits filled in): what the kernel will hold the code to
            out.append(f"law {name}: statement changed\n    was: {shown}\n    now: {now_shown}")
        for d in sorted(deps.keys() | now_deps.keys()):
            was, now = deps.get(d), now_deps.get(d)
            if was == now:
                continue
            if was and now and was[0] == now[0] == "code" and was[1] != now[1]:
                out.append(f"law {name}: '{d}' now comes from {now[1]} (was {was[1]})")
            else:
                out.append(f"law {name}: '{d}' changed")
    return out


def project_at(ref, root):
    """The project folder `root` as it is at git `ref`, extracted to a temp folder; None if
    it didn't exist there. Raises CheckError if the ref can't be read."""
    root = Path(root).resolve()
    git = lambda cwd, *a: subprocess.run(["git", *a], cwd=cwd, capture_output=True, check=True).stdout
    try:
        git(root, "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}")
        top = Path(git(root, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    except (OSError, subprocess.CalledProcessError):
        raise CheckError(f"can't read git ref {ref!r} in {root}") from None
    tree = f"{ref}:{root.relative_to(top).as_posix()}".removesuffix(":.")
    try:
        data = git(top, "archive", tree)  # from top: in a subfolder, git archive keeps only that subfolder of `tree`
    except subprocess.CalledProcessError:
        return None  # the project is new since ref
    out = Path(tempfile.mkdtemp(prefix="minilaws-"))
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        tar.extractall(out, filter="data")
    return out


SKIP_DIRS = {"node_modules", "__pycache__", "site-packages", "build", "dist"}
PROJECT_MARKERS = ("minilaws.toml", "LAWS.laws")
CHECKED_PY = re.compile(r"^from minilaws import .*\bNat\b", re.M)


def _tooling_dir(d):
    return d.name in SKIP_DIRS or d.name.startswith(".") or (d / "pyvenv.cfg").is_file()


def _skip_dir(d):
    """Not part of this project: tooling dirs, virtualenvs, and nested projects (checked on their own)."""
    return _tooling_dir(d) or any((d / m).is_file() for m in PROJECT_MARKERS)


def laws_dirs(root):
    """Every folder under root holding a .laws file or a project marker."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not _tooling_dir(Path(dirpath) / d))
        if any(f.endswith(".laws") or f in PROJECT_MARKERS for f in filenames):
            yield Path(dirpath)


def project_files(root):
    """Files to check under root: minilaws.toml's `files` if present, else every *.laws
    plus every .py that does `from minilaws import Nat` (the opt-in marker)."""
    root = Path(root)
    config = root / "minilaws.toml"
    if config.is_file():
        return [root / f for f in tomllib.loads(config.read_text(encoding="utf-8")).get("files", [])]
    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if not _skip_dir(Path(dirpath) / d))
        for f in sorted(filenames):
            p = Path(dirpath) / f
            if f.endswith(".laws") or (f.endswith(".py") and CHECKED_PY.search(p.read_text(encoding="utf-8", errors="ignore"))):
                found.append(p)
    return found


@deep_stack
def check_project(root=".", against=None):
    """Check the project under root. With `against` (a git ref), also require every law at
    that ref to still hold with the same meaning; see law_changes."""
    files = project_files(root)
    if not any(str(f).endswith(".laws") for f in files):
        return False, f"REJECTED: no .laws files under {Path(root).resolve()}"
    try:
        env, decls = load_files(files)
        n = len(env.types) - env.prelude_size
        if against is None:
            return True, f"OK: {n} declarations checked"
        base_root = project_at(against, root)
        base_files = project_files(base_root) if base_root else []
        if not any(str(f).endswith(".laws") for f in base_files):
            return True, f"OK: {n} declarations checked (no laws at {against} to compare)"
        try:
            base = law_specs(*load_files(base_files), base_root)
        except CheckError as e:
            raise CheckError(f"the version at {against} doesn't check, so it can't be the reference: {e}") from None
        if changes := law_changes(base, law_specs(env, decls, root)):
            raise CheckError(f"the laws differ from {against}; a human must approve this:\n  " + "\n  ".join(changes))
    except CheckError as e:
        return False, f"REJECTED: {e}"
    return True, f"OK: {n} declarations checked, the {len(base)} laws at {against} unchanged"


def main(paths):
    ok, msg = check_files(paths)
    print(msg)
    return 0 if ok else 1


def cli(argv=None):
    """`minilaws check [DIR] [--against REF]` checks a project; `minilaws FILE...` checks files."""
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ["check"]:
        args, against = argv[1:], None
        if "--against" in args:
            i = args.index("--against")
            if i + 1 >= len(args):
                print("--against needs a git ref, e.g. origin/main")
                return 2
            against = args[i + 1]
            del args[i : i + 2]
        ok, msg = check_project(args[0] if args else ".", against)
        print(msg)
        return 0 if ok else 1
    if not argv:
        print("usage: minilaws check [DIR] [--against REF]  |  minilaws FILE...")
        return 2
    return main(argv)


if __name__ == "__main__":
    sys.exit(cli())
