"""pytest plugin (auto-loaded once minilaws is installed): every project with a .laws file
that pytest collects becomes one test that checks all its proofs. Any .laws file counts,
not only LAWS.laws, so deleting or renaming LAWS.laws leaves proofs without laws: a failure."""
import pytest

from minilaws import PROJECT_MARKERS, check_project

ROOTS = pytest.StashKey[set]()


class LawsBroken(Exception):
    pass


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


class LawsFile(pytest.File):
    def collect(self):
        yield LawsItem.from_parent(self, name="laws")


class LawsItem(pytest.Item):
    def runtest(self):
        ok, msg = check_project(project_root(self.path, self.config.rootpath))
        if not ok:
            raise LawsBroken(msg)

    def repr_failure(self, excinfo):
        if isinstance(excinfo.value, LawsBroken):
            return str(excinfo.value)
        return super().repr_failure(excinfo)

    def reportinfo(self):
        return self.path, None, f"minilaws: {self.path.name}"
