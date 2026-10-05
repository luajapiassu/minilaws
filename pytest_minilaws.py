"""pytest plugin (auto-loaded once minilaws is installed): every LAWS.laws that pytest
collects becomes one test that checks all proofs of its project."""
import pytest

from minilaws import check_project


class LawsBroken(Exception):
    pass


def pytest_collect_file(file_path, parent):
    if file_path.name == "LAWS.laws":
        return LawsFile.from_parent(parent, path=file_path)


class LawsFile(pytest.File):
    def collect(self):
        yield LawsItem.from_parent(self, name="laws")


class LawsItem(pytest.Item):
    def runtest(self):
        ok, msg = check_project(self.path.parent)
        if not ok:
            raise LawsBroken(msg)

    def repr_failure(self, excinfo):
        if isinstance(excinfo.value, LawsBroken):
            return str(excinfo.value)
        return super().repr_failure(excinfo)

    def reportinfo(self):
        return self.path, None, f"minilaws: {self.path.name}"
