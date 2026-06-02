from __future__ import annotations

import pytest
import os
from pathlib import Path
from pdd.pytest_slicer import PytestSlicer, SlicerError, SlicedManifest

"""
Test Plan for PytestSlicer:
- TestPytestSlicerInit: Verify initialization with/without file_path.
- TestPytestSlicerSliceBasic: Basic slicing of a single test with a helper.
- TestPytestSlicerFixtures: Slicing with fixtures (direct and @pytest.mark.usefixtures).
- TestPytestSlicerConftest: Verify discovery and inclusion of fixtures from conftest.py.
- TestPytestSlicerClass: Slicing a method inside a class.
- TestPytestSlicerParametrize: Support for @pytest.mark.parametrize.
- TestPytestSlicerImports: Verify all necessary imports are included.
- TestPytestSlicerDeterminism: Output is deterministic.
- TestPytestSlicerErrorHandling: Syntax errors and missing tests.
- TestPytestSlicerWhitespace: Preservation of indentation and whitespace.
"""

def test_init_basic():
    source = "def test_a(): pass"
    slicer = PytestSlicer(source)
    assert slicer.main_source == source
    assert "test_a" in slicer.definitions

def test_init_syntax_error():
    source = "def test_a("
    with pytest.raises(SlicerError, match="Syntax error"):
        PytestSlicer(source)

def test_slice_basic():
    source = """
import os

def helper(x):
    return x + 1

def test_one():
    assert helper(1) == 2

def test_two():
    assert 2 == 2
"""
    slicer = PytestSlicer(source)
    sliced_code, manifest = slicer.slice(["test_one"])
    
    assert "test_one" in manifest.selected_tests
    assert "helper" in manifest.included_helpers
    assert "test_two" not in sliced_code
    assert "def helper(x):" in sliced_code
    assert "def test_one():" in sliced_code
    assert "import os" in sliced_code

def test_slice_fixtures():
    source = """
import pytest

@pytest.fixture
def fix_a():
    return 1

@pytest.mark.usefixtures("fix_a")
def test_fix():
    pass

def test_arg(fix_a):
    assert fix_a == 1
"""
    slicer = PytestSlicer(source)
    
    # Test usefixtures
    sliced_code, manifest = slicer.slice(["test_fix"])
    assert "fix_a" in manifest.included_fixtures
    assert "def fix_a():" in sliced_code
    
    # Test arg fixture
    sliced_code, manifest = slicer.slice(["test_arg"])
    assert "fix_a" in manifest.included_fixtures
    assert "def fix_a():" in sliced_code

def test_slice_class(tmp_path):
    source = """
import pytest

class TestSuite:
    @pytest.fixture
    def class_fix(self):
        return 2

    def test_method(self, class_fix):
        assert class_fix == 2
"""
    slicer = PytestSlicer(source)
    sliced_code, manifest = slicer.slice(["TestSuite.test_method"])
    
    assert "TestSuite.test_method" in manifest.selected_tests
    assert "TestSuite.class_fix" in manifest.included_fixtures
    assert "class TestSuite:" in sliced_code
    assert "def test_method(self, class_fix):" in sliced_code
    assert "def class_fix(self):" in sliced_code

def test_slice_conftest(tmp_path):
    project_root = tmp_path / "project"
    project_root.mkdir()
    (project_root / "GEMINI.md").touch() # Mark as root
    
    conftest = project_root / "conftest.py"
    conftest.write_text("""
import pytest
@pytest.fixture
def global_fix():
    return "global"
""", encoding="utf-8")
    
    test_dir = project_root / "tests"
    test_dir.mkdir()
    test_file = test_dir / "test_something.py"
    test_source = """
def test_global(global_fix):
    assert global_fix == "global"
"""
    test_file.write_text(test_source, encoding="utf-8")
    
    slicer = PytestSlicer(test_source, file_path=str(test_file))
    sliced_code, manifest = slicer.slice(["test_global"])
    
    assert "global_fix" in manifest.included_fixtures
    assert "def global_fix():" in sliced_code
    assert "# --- From " in sliced_code
    assert "conftest.py" in sliced_code

def test_slice_missing_test():
    source = "def test_a(): pass"
    slicer = PytestSlicer(source)
    with pytest.raises(SlicerError, match="Test 'test_b' not found"):
        slicer.slice(["test_b"])

def test_slice_determinism():
    source = """
def b(): pass
def a(): pass
def test_x(a, b): pass
"""
    slicer = PytestSlicer(source)
    res1, _ = slicer.slice(["test_x"])
    res2, _ = slicer.slice(["test_x"])
    assert res1 == res2

def test_slice_parametrize():
    source = """
import pytest
@pytest.mark.parametrize("x", [1, 2])
def test_param(x):
    assert x > 0
"""
    slicer = PytestSlicer(source)
    sliced_code, manifest = slicer.slice(["test_param"])
    assert "@pytest.mark.parametrize" in sliced_code
    assert "def test_param(x):" in sliced_code

def test_slice_async_test():
    source = """
import pytest

async def test_async_flow():
    assert True

class TestAsync:
    async def test_method(self):
        assert 1 == 1
"""
    slicer = PytestSlicer(source)
    sliced_code, _ = slicer.slice(["test_async_flow"])
    assert "async def test_async_flow" in sliced_code

    sliced_code2, _ = slicer.slice(["TestAsync.test_method"])
    assert "async def test_method" in sliced_code2


def test_slice_recursive_deps():
    source = """
VAL = 10
def helper_b(): return VAL
def helper_a(): return helper_b()
def test_recursive(): assert helper_a() == 10
"""
    slicer = PytestSlicer(source)
    sliced_code, manifest = slicer.slice(["test_recursive"])
    assert "VAL = 10" in sliced_code
    assert "def helper_b():" in sliced_code
    assert "def helper_a():" in sliced_code
    assert "VAL" in manifest.included_helpers
    assert "helper_a" in manifest.included_helpers
    assert "helper_b" in manifest.included_helpers


def test_slice_includes_self_referenced_helper():
    source = """
class TestThing:
    def helper(self):
        return 1

    def test_uses_helper(self):
        assert self.helper() == 1
"""
    slicer = PytestSlicer(source)
    sliced_code, manifest = slicer.slice(["TestThing.test_uses_helper"])
    assert "def helper(self):" in sliced_code
    assert "TestThing.helper" in manifest.included_helpers


def test_slice_preserves_indentation():
    source = """
def helper(x):
        return x + 1

def test_one():
    assert helper(1) == 2
"""
    slicer = PytestSlicer(source)
    sliced_code, _ = slicer.slice(["test_one"])
    assert "        return x + 1" in sliced_code
