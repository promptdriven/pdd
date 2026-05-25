"""Regression coverage for the cloud regression behavioral-test validator."""
from __future__ import annotations

import importlib.util
import textwrap
from pathlib import Path


_VALIDATOR_PATH = Path(__file__).parent / "validate_behavioral_test.py"
_SPEC = importlib.util.spec_from_file_location("validate_behavioral_test", _VALIDATOR_PATH)
assert _SPEC and _SPEC.loader
_VALIDATOR = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_VALIDATOR)


def test_pytest_fixture_returning_source_callable_counts_as_behavioral(tmp_path: Path) -> None:
    """The cloud LLM may return a source function through a capture-aware fixture."""
    source = tmp_path / "bug_py_code.py"
    test_file = tmp_path / "test_bug.py"
    source.write_text("def preprocess(text, quiet=False):\n    return text\n", encoding="utf-8")
    test_file.write_text(
        textwrap.dedent(
            """\
            import importlib
            import pytest

            @pytest.fixture
            def preprocess_func():
                module = importlib.import_module("bug_py_code")
                return module.preprocess

            def test_quiet_behavior(preprocess_func):
                result = preprocess_func("hello", quiet=True)
                assert result == "hello"
            """
        ),
        encoding="utf-8",
    )

    assert _VALIDATOR.check_python_ast(str(test_file), str(source)) == []


def test_fixture_without_source_callable_still_fails_positive_check(tmp_path: Path) -> None:
    """An arbitrary fixture call must not satisfy source invocation checks."""
    source = tmp_path / "bug_py_code.py"
    test_file = tmp_path / "test_bug.py"
    source.write_text("def preprocess(text, quiet=False):\n    return text\n", encoding="utf-8")
    test_file.write_text(
        textwrap.dedent(
            """\
            import pytest

            @pytest.fixture
            def helper():
                return lambda text: text

            def test_only_calls_helper(helper):
                assert helper("hello") == "hello"
            """
        ),
        encoding="utf-8",
    )

    issues = _VALIDATOR.check_python_ast(str(test_file), str(source))
    assert any("No test function calls any public function" in issue for issue in issues)
