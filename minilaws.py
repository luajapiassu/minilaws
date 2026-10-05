"""minilaws: a tiny dependent-type proof checker (Curry-Howard), in the spirit of Bend's LAWS.bend.

Types are statements, programs are proofs, type checking is proof checking.
Kernel: Pi types, a predicative universe hierarchy (Type i : Type i+1), Nat with its
recursor (= induction), and Eq with transport (Eq.subst). No general recursion, so every
term terminates and the checker can't be fooled by a looping "proof".

Two layers:
  - elaborator (untrusted): fills in {implicit} arguments by unification;
  - kernel (trusted): re-checks the fully explicit result. A buggy elaborator can only
    cause rejections, never accept a wrong proof.

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
import os
import re
import sys
import tomllib
from dataclasses import dataclass, replace
from pathlib import Path


# ---------- terms (de Bruijn indices) ----------

@dataclass(frozen=True)
class Var:
    i: int

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
    match t:
        case Var(i):
            return Var(i + d) if i >= cut else t
        case Pi(_, a, b) | Lam(_, a, b):
            return replace(t, dom=a and shift(a, d, cut), body=shift(b, d, cut + 1))
        case App(f, a):
            return App(shift(f, d, cut), shift(a, d, cut))
    return t


def subst(t, j, s):
    match t:
        case Var(i):
            return s if i == j else t
        case Pi(_, a, b) | Lam(_, a, b):
            return replace(t, dom=a and subst(a, j, s), body=subst(b, j + 1, shift(s, 1)))
        case App(f, a):
            return App(subst(f, j, s), subst(a, j, s))
    return t


def instantiate(body, arg):
    return shift(subst(body, 0, shift(arg, 1)), -1)


def subterms(t, d=0):
    """Yield (subterm, binder depth) for every node."""
    yield t, d
    match t:
        case Pi(_, a, b) | Lam(_, a, b):
            if a is not None:
                yield from subterms(a, d)
            yield from subterms(b, d + 1)
        case App(f, a):
            yield from subterms(f, d)
            yield from subterms(a, d)


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
        self.recursors = {}  # "T.rec" -> (n_params, n_minors, n_indices, {ctor: iota info})
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
        for n in [name, rec_name] + [c for c, _ in ctors]:
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
        motive, major = self.fresh("motive"), self.fresh("t")
        M, I = Const(motive), [Const(f) for f, *_ in idx]
        motive_ty = close_pi(idx + [(major, "t", apply(Const(name), P + I), False)], Sort(0))
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
        self.types[rec_name] = rec_ty
        ctor_info = {c: (j, [f for f, *_ in fields], [f for f, *_ in ps], recs) for j, (c, fields, _, recs) in enumerate(info)}
        self.recursors[rec_name] = (np, len(info), len(idx), ctor_info)

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
        if any(x == a or (isinstance(x, Var) and d <= x.i < d + k) for x, d in subterms(b)):
            raise Stuck  # occurs check / refers to a variable bound after the meta
        self.metas[a.i] = shift(b, -k)
        return True

    def unify(self, a, b, k=0):
        a, b = self.zonk(a, k), self.zonk(b, k)
        if self.assign_if_meta(a, b, k):
            return
        a, b = self.whnf(a), self.whnf(b)
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
            case App(f1, x1), App(f2, x2):
                try:
                    self.unify(f1, f2, k)
                    return self.unify(x1, x2, k)
                except Mismatch:
                    pass
        if has_meta(self.zonk(a, k)) or has_meta(self.zonk(b, k)):
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
        explicit = isinstance(head, Const) and head.name.startswith("@")
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
            if not isinstance(fty, Pi):
                raise CheckError(f"'{show(head, ctx)}' applied to too many arguments")
            m = self.new_meta()
            core_args.append(m)
            goals.append((m, a, fty.dom))
            fty = instantiate(fty.body, m)
        if expected is not None:
            goals.insert(0, (None, t, expected))
        # Solve goals in whatever order makes progress; a stuck goal is rolled back and retried.
        while goals:
            progress = False
            for goal in list(goals):
                m, a, dom = goal
                saved = dict(self.metas)
                try:
                    if m is None:
                        self.unify_at(ctx, a, fty, dom)
                    else:
                        self.unify(m, self.elab_check(ctx, a, dom))
                except Stuck:
                    self.metas = saved
                    continue
                goals.remove(goal)
                progress = True
            if not progress:
                raise Stuck
        return apply(core, core_args), fty


PRELUDE = """
inductive Nat : Type 0 where
  | zero : Nat
  | succ : Nat -> Nat
inductive Eq {A : Type 0} (x : A) : A -> Type 0 where
  | refl : Eq x x
theorem Eq.subst : {A : Type 0} -> {x y : A} -> (P : A -> Type 0) -> Eq x y -> P x -> P y :=
  fun P h px => Eq.rec (fun y _ => P y) px h
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
        if t is not None and t.startswith("@"):
            return Const(self.eat())
        n = self.name()
        for i, s in enumerate(reversed(scope)):
            if s == n and s != "_":
                return Var(i)
        return Const(n)


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
# Trusted translator for a small, total subset of Python over natural numbers:
#
#     def f(x: Nat, ..., m: Nat) -> Nat:
#         if m == 0:              # optional: structural recursion on parameter m
#             return BASE
#         return STEP             # may call f(..., m - 1, ...) with the other args unchanged
#
# Expressions: parameters, int literals >= 0, `e + <int>`, `m - 1` (in STEP), calls to
# earlier functions. Anything else is refused instead of guessed at.

Nat = int  # runtime type for the Python side; the laws speak about n >= 0
RESERVED = KEYWORDS | {"Nat", "zero", "succ", "Eq", "refl"}


def translate_python(src):
    out = []
    for node in ast.parse(src).body:
        if isinstance(node, (ast.Import, ast.ImportFrom)) or _is_docstring(node):
            continue
        if not isinstance(node, ast.FunctionDef):
            raise _unsupported(node, "only function definitions")
        out.append(_translate_fn(node))
    return "\n".join(out) + "\n"


def _unsupported(node, why):
    return CheckError(f"line {node.lineno}: unsupported Python ({why}): {ast.unparse(node).splitlines()[0]}")


def _is_docstring(node):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)


def _is_nat(ann):
    return isinstance(ann, ast.Name) and ann.id == "Nat"


def _translate_fn(fn):
    a = fn.args
    params = [p.arg for p in a.args]
    if a.vararg or a.kwarg or a.kwonlyargs or a.posonlyargs or a.defaults or fn.decorator_list:
        raise _unsupported(fn, "plain positional parameters only")
    if not all(_is_nat(p.annotation) for p in a.args) or not _is_nat(fn.returns):
        raise _unsupported(fn, "parameters and result must be annotated Nat")
    if any(p in RESERVED for p in params):
        raise _unsupported(fn, f"parameter names can't be any of {sorted(RESERVED)}")
    body = fn.body
    if _is_docstring(body[0]):
        body = body[1:]
    match body:
        case [ast.Return(value=e)]:
            expr = _py_expr(e, fn.name, params, None, "plain")
        case [ast.If(test=test, body=[ast.Return(value=base)], orelse=orelse), *rest]:
            m = _zero_test(test, params)
            steps = orelse + rest
            if m is None or len(steps) != 1 or not isinstance(steps[0], ast.Return):
                raise _unsupported(fn, "expected `if m == 0: return ...` then one `return ...`")
            b = _py_expr(base, fn.name, params, m, "base")
            s = _py_expr(steps[0].value, fn.name, params, m, "step")
            expr = f"Nat.rec (fun _ => Nat) {b} (fun pred' ih' => {s}) {m}"
        case _:
            raise _unsupported(fn, "body must be `return e`, or `if m == 0: return e` then `return e`")
    ty = " -> ".join(["Nat"] * (len(params) + 1))
    return f"def {fn.name} : {ty} := " + (f"fun {' '.join(params)} => {expr}" if params else expr)


def _zero_test(test, params):
    match test:
        case ast.Compare(left=ast.Name(id=m), ops=[ast.Eq()], comparators=[ast.Constant(value=0)]) if m in params:
            return m
    return None


def _succs(t, c):
    for _ in range(c):
        t = f"(succ {t})"
    return t


def _nat_literal(e):
    return isinstance(e, ast.Constant) and type(e.value) is int and e.value >= 0


def _py_expr(e, fn, params, rec, mode):
    """mode: 'plain' (no recursion), 'base' (rec var is 0), 'step' (rec var is succ pred')."""
    go = lambda x: _py_expr(x, fn, params, rec, mode)
    if _nat_literal(e):
        return _succs("zero", e.value)
    match e:
        case ast.Name(id=x) if x in params:
            if x == rec:
                return "zero" if mode == "base" else "(succ pred')"
            return x
        case ast.BinOp(left=left, op=ast.Add(), right=right) if _nat_literal(right):
            return _succs(go(left), right.value)
        case ast.BinOp(left=ast.Name(id=x), op=ast.Sub(), right=ast.Constant(value=1)) if x == rec and mode == "step":
            return "pred'"
        case ast.Call(func=ast.Name(id=f), args=args, keywords=[]) if f == fn:
            i = params.index(rec) if mode == "step" else None
            pred = lambda a: isinstance(a, ast.BinOp) and isinstance(a.op, ast.Sub) and go(a) == "pred'"
            ok = i is not None and len(args) == len(params) and all(
                pred(a) if j == i else (isinstance(a, ast.Name) and a.id == params[j]) for j, a in enumerate(args)
            )
            if not ok:
                raise _unsupported(e, f"recursion must be {fn}(..., m - 1, ...) after `if m == 0`, other arguments unchanged")
            return "ih'"
        case ast.Call(func=ast.Name(id=f), args=args, keywords=[]):
            return "(" + " ".join([f] + [go(a) for a in args]) + ")"
    raise _unsupported(e, "only parameters, literals, `x + <int>`, `m - 1` and function calls")


def read_source(path):
    text = Path(path).read_text(encoding="utf-8")
    return translate_python(text) if str(path).endswith(".py") else text


# Code before laws before proofs, so file order doesn't matter. Stable within a phase.
PHASE = {"inductive": 0, "def": 0, "law": 1, "theorem": 2, "proof": 2}


def check_files(paths):
    """Check a set of files. Returns (ok, message)."""
    env = Env()
    try:
        decls = []
        for path in paths:
            try:
                decls += [(path, d) for d in parse_decls(read_source(path))]
            except CheckError as e:
                raise CheckError(f"{Path(path).name}: {e}") from None
        for path, d in sorted(decls, key=lambda pd: PHASE[pd[1][0]]):
            try:
                add_decl(env, d)
            except CheckError as e:
                raise CheckError(f"{Path(path).name}: {e}") from None
    except CheckError as e:
        return False, f"REJECTED: {e}"
    if env.laws:
        return False, "REJECTED: laws without proof: " + ", ".join(env.laws)
    return True, f"OK: {len(env.types) - env.prelude_size} declarations checked"


SKIP_DIRS = {"node_modules", "__pycache__", "site-packages", "venv", "env", "build", "dist"}
CHECKED_PY = re.compile(r"^from minilaws import .*\bNat\b", re.M)


def project_files(root):
    """Files to check under root: minilaws.toml's `files` if present, else every *.laws
    plus every .py that does `from minilaws import Nat` (the opt-in marker)."""
    root = Path(root)
    config = root / "minilaws.toml"
    if config.is_file():
        return [root / f for f in tomllib.loads(config.read_text(encoding="utf-8")).get("files", [])]
    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS and not d.startswith("."))
        for f in sorted(filenames):
            p = Path(dirpath) / f
            if f.endswith(".laws") or (f.endswith(".py") and CHECKED_PY.search(p.read_text(encoding="utf-8", errors="ignore"))):
                found.append(p)
    return found


def check_project(root="."):
    files = project_files(root)
    if not any(str(f).endswith(".laws") for f in files):
        return False, f"REJECTED: no .laws files under {Path(root).resolve()}"
    return check_files(files)


def main(paths):
    ok, msg = check_files(paths)
    print(msg)
    return 0 if ok else 1


def cli(argv=None):
    """`minilaws check [dir]` checks a project; `minilaws FILE...` checks files in the given order."""
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ["check"]:
        ok, msg = check_project(argv[1] if len(argv) > 1 else ".")
        print(msg)
        return 0 if ok else 1
    if not argv:
        print("usage: minilaws check [DIR]  |  minilaws FILE...")
        return 2
    return main(argv)


if __name__ == "__main__":
    sys.exit(cli())
