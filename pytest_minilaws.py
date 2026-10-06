"""pytest plugin (auto-loaded once minilaws is installed): every project with a .laws file
that pytest collects becomes one test that checks all its proofs. Any .laws file counts,
not only LAWS.laws, so deleting or renaming LAWS.laws leaves proofs without laws: a failure.
With --minilaws-against REF (or MINILAWS_AGAINST), the laws must also be unchanged from REF."""
import os

import pytest

from minilaws import PROJECT_MARKERS, check_project, laws_dirs

ROOTS = pytest.StashKey[set]()
MISSED = pytest.StashKey[list]()


class LawsBroken(Exception):
    pass


def pytest_addoption(parser):
    parser.addoption("--minilaws-against", metavar="REF", default=os.environ.get("MINILAWS_AGAINST") or None,
                     help="git ref whose laws must still hold unchanged, e.g. origin/main (env: MINILAWS_AGAINST)")


def project_root(file_path, rootpath):
    """Nearest folder (up to pytest's rootdir) that marks a project, else the file's own folder."""
    for d in [file_path.parent, *file_path.parent.parents]:
        if any((d / m).is_file() for m in PROJECT_MARKERS):
            return d
        if d == rootpath:
            break
    return file_path.parent


def pytest_collect_file(file_path, parent):
    if file_path.suffix != ".laws":
        return None
    seen = parent.config.stash.setdefault(ROOTS, set())
    root = project_root(file_path, parent.config.rootpath)
    if root in seen:
        return None
    seen.add(root)
    return LawsFile.from_parent(parent, path=file_path)


def pytest_collection_finish(session):
    """Narrowed collection (`testpaths`, `--ignore`) would silently turn the laws off: say so.
    Not when paths are given on the command line, since then the user picked them."""
    config = session.config
    if config.args_source == pytest.Config.ArgsSource.ARGS:
        return
    # ponytail: walks the rootdir once per run; skip it behind an option if that's ever slow
    roots = {project_root(d / "_", config.rootpath) for d in laws_dirs(config.rootpath)}
    # session.items, not ROOTS: pytest also visits files it then filters out by testpaths
    ran = {project_root(i.path, config.rootpath) for i in session.items if isinstance(i, LawsItem)}
    config.stash[MISSED] = sorted(roots - ran)


def pytest_terminal_summary(terminalreporter, config):
    if missed := config.stash.get(MISSED, []):
        terminalreporter.write_sep("=", "minilaws: laws not collected", yellow=True)
        for root in missed:
            terminalreporter.write_line(f"{root}: run `minilaws check` on it, or let pytest collect its .laws files")


class LawsFile(pytest.File):
    def collect(self):
        yield LawsItem.from_parent(self, name="laws")


class LawsItem(pytest.Item):
    def runtest(self):
        ok, msg = check_project(project_root(self.path, self.config.rootpath), self.config.getoption("minilaws_against"))
        if not ok:
            raise LawsBroken(msg)

    def repr_failure(self, excinfo):
        if isinstance(excinfo.value, LawsBroken):
            return str(excinfo.value)
        return super().repr_failure(excinfo)

    def reportinfo(self):
        return self.path, None, f"minilaws: {self.path.name}"
