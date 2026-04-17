"""Tests for pdd.split_validation module.

Test Plan (from spec requirements):
1. ValidationFailure dataclass
   - test_validation_failure_defaults: severity defaults to "error"
   - test_validation_failure_warning: severity can be "warning"
2. ValidationResult dataclass
   - test_validation_result_defaults: failures defaults to empty list, failure_type to "none"
   - test_validation_result_passed_false: passed=False with error failures
3. validate_extraction — check (a) byte_equivalence
   - test_byte_equivalence_clean: no diff -> no failure
   - test_byte_equivalence_dirty: diff output -> error failure
   - test_byte_equivalence_git_not_found: FileNotFoundError -> error
   - test_byte_equivalence_os_error: OSError -> error
4. validate_extraction — check (b) children_completeness
   - test_children_completeness_all_present: all prompt files exist -> no failure
   - test_children_completeness_missing: missing prompt files -> error
5. validate_extraction — check (c) prompt_metadata
   - test_prompt_metadata_all_tags: all tags present -> no warning
   - test_prompt_metadata_missing_tags: missing tags -> warning failures
6. validate_extraction — check (d) example_file
   - test_example_file_exists: example exists -> no failure
   - test_example_file_missing: example missing -> error
7. validate_extraction — check (e) test_ownership
   - test_ownership_clean: test references only own module -> no failure
   - test_ownership_cross_ref: test references other module -> warning
8. validate_extraction — failure_type classification
   - test_failure_type_none: no failures -> "none"
   - test_failure_type_extraction: only byte_equiv failures -> "extraction"
   - test_failure_type_metadata: only metadata failures -> "metadata"
   - test_failure_type_completeness: only completeness failures -> "completeness"
   - test_failure_type_multiple: mixed categories -> "multiple"
9. validate_extraction — edge cases
   - test_worktree_not_directory: non-existent worktree -> error
   - test_plan_no_children: plan with no children attribute
   - test_empty_children: plan with empty children list
10. get_test_command
    - test_get_test_command_delegates: calls get_test_command_for_file(str(file))
    - test_get_test_command_returns_none: returns None when delegate returns None
11. get_lint_commands
    - test_get_lint_commands_delegates: calls _get_lint_commands_impl(file)
    - test_get_lint_commands_empty_for_non_python: returns empty list
12. passed field
    - test_passed_true_warnings_only: only warning failures -> passed=True
    - test_passed_false_with_errors: error failures -> passed=False
"""
from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.split_validation import (
    ValidationFailure,
    ValidationResult,
    validate_extraction,
    get_test_command,
    get_lint_commands,
    LintCommand,
    TestCommand,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

@dataclass
class FakeChild:
    """Mock child object with prompt_file and code_file."""
    prompt_file: str
    code_file: str


@dataclass
class FakePlan:
    """Mock plan object with children list."""
    children: list


FULL_PROMPT_CONTENT = (
    "<pdd-reason>reason</pdd-reason>\n"
    "<pdd-interface>{}</pdd-interface>\n"
    "<pdd-dependency>dep</pdd-dependency>\n"
)


def _mock_git_clean():
    """Return a patch for subprocess.run that simulates clean git diff."""
    return patch(
        "pdd.split_validation.subprocess.run",
        return_value=subprocess.CompletedProcess(
            args=["git", "diff", "--stat"], returncode=0, stdout="", stderr=""
        ),
    )


# ---------------------------------------------------------------------------
# 1. ValidationFailure dataclass
# ---------------------------------------------------------------------------

class TestValidationFailure:
    """Tests for the ValidationFailure dataclass."""

    def test_validation_failure_defaults(self):
        """severity defaults to 'error'."""
        f = ValidationFailure(check="test", message="msg")
        assert f.check == "test"
        assert f.message == "msg"
        assert f.severity == "error"

    def test_validation_failure_warning(self):
        """severity can be explicitly set to 'warning'."""
        f = ValidationFailure(check="test", message="msg", severity="warning")
        assert f.severity == "warning"


# ---------------------------------------------------------------------------
# 2. ValidationResult dataclass
# ---------------------------------------------------------------------------

class TestValidationResult:
    """Tests for the ValidationResult dataclass."""

    def test_validation_result_defaults(self):
        """failures defaults to empty list, failure_type to 'none'."""
        r = ValidationResult(passed=True)
        assert r.failures == []
        assert r.failure_type == "none"

    def test_validation_result_passed_false(self):
        """Can construct with passed=False and failures."""
        f = ValidationFailure(check="x", message="y")
        r = ValidationResult(passed=False, failures=[f], failure_type="extraction")
        assert r.passed is False
        assert len(r.failures) == 1
        assert r.failure_type == "extraction"


# ---------------------------------------------------------------------------
# 3. validate_extraction — byte_equivalence (a)
# ---------------------------------------------------------------------------

class TestByteEquivalence:
    """Tests for check (a): moved-code byte-equivalence."""

    def test_byte_equivalence_clean(self, tmp_path):
        """Clean git diff -> no byte_equivalence failure."""
        plan = FakePlan(children=[])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.passed is True
        assert not any(f.check == "byte_equivalence" for f in result.failures)

    def test_byte_equivalence_dirty_is_allowed(self, tmp_path):
        """git status with working-tree changes is expected after extraction
        — no failure. The check only catches git repository errors.
        """
        plan = FakePlan(children=[])
        with patch(
            "pdd.split_validation.subprocess.run",
            return_value=subprocess.CompletedProcess(
                args=[], returncode=0,
                stdout=" M file.py\n?? new.py\n", stderr=""
            ),
        ):
            result = validate_extraction(plan, tmp_path)
        errors = [f for f in result.failures if f.check == "byte_equivalence"]
        # Dirty worktree is expected post-extraction; only rc != 0 fails
        assert len(errors) == 0

    def test_byte_equivalence_git_rc_nonzero(self, tmp_path):
        """git status returning non-zero -> byte_equivalence error."""
        plan = FakePlan(children=[])
        with patch(
            "pdd.split_validation.subprocess.run",
            return_value=subprocess.CompletedProcess(
                args=[], returncode=128, stdout="", stderr="fatal: not a git repo"
            ),
        ):
            result = validate_extraction(plan, tmp_path)
        errors = [f for f in result.failures if f.check == "byte_equivalence"]
        assert len(errors) == 1
        assert errors[0].severity == "error"
        assert "git status failed" in errors[0].message

    def test_byte_equivalence_git_not_found(self, tmp_path):
        """FileNotFoundError when git not found -> error failure."""
        plan = FakePlan(children=[])
        with patch(
            "pdd.split_validation.subprocess.run",
            side_effect=FileNotFoundError("git not found"),
        ):
            result = validate_extraction(plan, tmp_path)
        errors = [f for f in result.failures if f.check == "byte_equivalence"]
        assert len(errors) == 1
        assert "git executable not found" in errors[0].message

    def test_byte_equivalence_os_error(self, tmp_path):
        """OSError during git run -> error failure."""
        plan = FakePlan(children=[])
        with patch(
            "pdd.split_validation.subprocess.run",
            side_effect=OSError("permission denied"),
        ):
            result = validate_extraction(plan, tmp_path)
        errors = [f for f in result.failures if f.check == "byte_equivalence"]
        assert len(errors) == 1
        assert "Error running git status" in errors[0].message


# ---------------------------------------------------------------------------
# 4. validate_extraction — children_completeness (b)
# ---------------------------------------------------------------------------

class TestChildrenCompleteness:
    """Tests for check (b): children completeness."""

    def test_children_completeness_all_present(self, tmp_path):
        """All prompt files exist -> no completeness failure."""
        (tmp_path / "a.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "a.py").write_text("")  # example
        plan = FakePlan(children=[
            FakeChild(prompt_file="a.prompt", code_file="a.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert not any(f.check == "children_completeness" for f in result.failures)

    def test_children_completeness_missing(self, tmp_path):
        """Missing prompt file -> children_completeness error."""
        (tmp_path / "a.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "a.py").write_text("")
        plan = FakePlan(children=[
            FakeChild(prompt_file="a.prompt", code_file="a.py"),
            FakeChild(prompt_file="b.prompt", code_file="b.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        errors = [f for f in result.failures if f.check == "children_completeness"]
        assert len(errors) == 1
        assert "Expected 2" in errors[0].message
        assert "b.prompt" in errors[0].message


# ---------------------------------------------------------------------------
# 5. validate_extraction — prompt_metadata (c)
# ---------------------------------------------------------------------------

class TestPromptMetadata:
    """Tests for check (c): prompt metadata tag presence."""

    def test_prompt_metadata_all_tags(self, tmp_path):
        """All required tags present -> no metadata warnings."""
        (tmp_path / "child.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "child.py").write_text("")  # example
        plan = FakePlan(children=[
            FakeChild(prompt_file="child.prompt", code_file="child.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert not any(f.check == "prompt_metadata" for f in result.failures)

    def test_prompt_metadata_missing_tags(self, tmp_path):
        """Missing all three tags -> three warning failures."""
        (tmp_path / "child.prompt").write_text("no tags here")
        (tmp_path / "child.py").write_text("")  # example
        plan = FakePlan(children=[
            FakeChild(prompt_file="child.prompt", code_file="child.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        meta_failures = [f for f in result.failures if f.check == "prompt_metadata"]
        assert len(meta_failures) == 3
        assert all(f.severity == "warning" for f in meta_failures)
        tags_mentioned = {f.message for f in meta_failures}
        assert any("<pdd-reason>" in m for m in tags_mentioned)
        assert any("<pdd-interface>" in m for m in tags_mentioned)
        assert any("<pdd-dependency>" in m for m in tags_mentioned)


# ---------------------------------------------------------------------------
# 6. validate_extraction — example_file (d)
# ---------------------------------------------------------------------------

class TestExampleFile:
    """Tests for check (d): example file existence."""

    def test_example_file_exists(self, tmp_path):
        """Example file exists -> no example_file failure."""
        (tmp_path / "child.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "child.py").write_text("")  # example file
        plan = FakePlan(children=[
            FakeChild(prompt_file="child.prompt", code_file="child.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert not any(f.check == "example_file" for f in result.failures)

    def test_example_file_missing(self, tmp_path):
        """Missing example file -> error failure."""
        (tmp_path / "child.prompt").write_text(FULL_PROMPT_CONTENT)
        # No child.py created
        plan = FakePlan(children=[
            FakeChild(prompt_file="child.prompt", code_file="child.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        errors = [f for f in result.failures if f.check == "example_file"]
        assert len(errors) == 1
        assert errors[0].severity == "error"
        assert "child.py" in errors[0].message


# ---------------------------------------------------------------------------
# 7. validate_extraction — test_ownership (e)
# ---------------------------------------------------------------------------

class TestTestOwnership:
    """Tests for check (e): test ownership classification."""

    def test_ownership_clean(self, tmp_path):
        """Test file references only own module -> no failure."""
        (tmp_path / "a.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "b.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "a.py").write_text("")
        (tmp_path / "b.py").write_text("")
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_a.py").write_text("import a\n")
        (tests_dir / "test_b.py").write_text("import b\n")
        plan = FakePlan(children=[
            FakeChild(prompt_file="a.prompt", code_file="a.py"),
            FakeChild(prompt_file="b.prompt", code_file="b.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert not any(f.check == "test_ownership" for f in result.failures)

    def test_ownership_cross_ref(self, tmp_path):
        """Test file references other child's module -> warning."""
        (tmp_path / "a.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "b.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "a.py").write_text("")
        (tmp_path / "b.py").write_text("")
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        # test_a.py references module 'b'
        (tests_dir / "test_a.py").write_text("from b import something\n")
        (tests_dir / "test_b.py").write_text("import b\n")
        plan = FakePlan(children=[
            FakeChild(prompt_file="a.prompt", code_file="a.py"),
            FakeChild(prompt_file="b.prompt", code_file="b.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        ownership_warnings = [f for f in result.failures if f.check == "test_ownership"]
        assert len(ownership_warnings) >= 1
        assert any("'b'" in f.message for f in ownership_warnings)
        assert all(f.severity == "warning" for f in ownership_warnings)


# ---------------------------------------------------------------------------
# 8. failure_type classification
# ---------------------------------------------------------------------------

class TestFailureTypeClassification:
    """Tests for failure_type summary category."""

    def test_failure_type_none(self, tmp_path):
        """No failures -> failure_type 'none'."""
        plan = FakePlan(children=[])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.failure_type == "none"

    def test_failure_type_extraction(self, tmp_path):
        """Only byte_equivalence (git-status failure) -> 'extraction'."""
        plan = FakePlan(children=[])
        with patch(
            "pdd.split_validation.subprocess.run",
            return_value=subprocess.CompletedProcess(
                args=[], returncode=128, stdout="", stderr="not a git repo"
            ),
        ):
            result = validate_extraction(plan, tmp_path)
        assert result.failure_type == "extraction"

    def test_failure_type_metadata(self, tmp_path):
        """Only prompt_metadata warnings -> 'metadata'."""
        (tmp_path / "c.prompt").write_text("no tags")
        (tmp_path / "c.py").write_text("")  # example exists
        plan = FakePlan(children=[
            FakeChild(prompt_file="c.prompt", code_file="c.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.failure_type == "metadata"

    def test_failure_type_completeness(self, tmp_path):
        """Only completeness failures -> 'completeness'."""
        (tmp_path / "c.prompt").write_text(FULL_PROMPT_CONTENT)
        # No example file -> example_file error (completeness category)
        plan = FakePlan(children=[
            FakeChild(prompt_file="c.prompt", code_file="c.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.failure_type == "completeness"

    def test_failure_type_multiple(self, tmp_path):
        """Mixed failure categories -> 'multiple'."""
        # byte_equivalence (git rc!=0) + missing example (completeness)
        (tmp_path / "c.prompt").write_text(FULL_PROMPT_CONTENT)
        plan = FakePlan(children=[
            FakeChild(prompt_file="c.prompt", code_file="c.py"),
        ])
        with patch(
            "pdd.split_validation.subprocess.run",
            return_value=subprocess.CompletedProcess(
                args=[], returncode=128, stdout="", stderr="not a git repo"
            ),
        ):
            result = validate_extraction(plan, tmp_path)
        assert result.failure_type == "multiple"


# ---------------------------------------------------------------------------
# 9. Edge cases
# ---------------------------------------------------------------------------

class TestDictChildren:
    """Children from LLM JSON are dicts — should work alongside dataclass objects."""

    def test_dict_child_with_new_prompt_field(self, tmp_path):
        """Dict child with new_prompt/new_source (LLM output format)."""
        (tmp_path / "child.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "examples").mkdir()
        (tmp_path / "examples" / "child_example.py").write_text("")
        plan = FakePlan(children=[
            {"name": "child", "new_prompt": "child.prompt", "new_source": "child.py"},
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        # Should succeed with no errors (warnings OK)
        assert result.passed is True

    def test_dict_child_with_prompt_file_field(self, tmp_path):
        """Dict child using prompt_file/code_file field names."""
        (tmp_path / "child.prompt").write_text(FULL_PROMPT_CONTENT)
        (tmp_path / "examples").mkdir()
        (tmp_path / "examples" / "child_example.py").write_text("")
        plan = FakePlan(children=[
            {"name": "child", "prompt_file": "child.prompt", "code_file": "child.py"},
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.passed is True


class TestEdgeCases:
    """Edge case tests for validate_extraction."""

    def test_worktree_not_directory(self, tmp_path):
        """Non-existent worktree -> byte_equivalence error, passed=False."""
        plan = FakePlan(children=[])
        bad_path = tmp_path / "nonexistent"
        result = validate_extraction(plan, bad_path)
        assert result.passed is False
        assert len(result.failures) == 1
        assert result.failures[0].check == "byte_equivalence"
        assert "not a directory" in result.failures[0].message

    def test_plan_no_children_attr(self, tmp_path):
        """Plan without children attribute -> treated as empty list."""
        plan = MagicMock(spec=[])  # no attributes
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.passed is True

    def test_empty_children(self, tmp_path):
        """Plan with empty children list -> no failures."""
        plan = FakePlan(children=[])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert result.passed is True
        assert result.failure_type == "none"


# ---------------------------------------------------------------------------
# 10. get_test_command
# ---------------------------------------------------------------------------

class TestGetTestCommand:
    """Tests for get_test_command delegation."""

    def test_get_test_command_delegates(self):
        """Calls get_test_command_for_file with str(file)."""
        expected = TestCommand(command="pytest tests/test_foo.py", cwd=None)
        with patch(
            "pdd.split_validation.get_test_command_for_file",
            return_value=expected,
        ) as mock_fn:
            result = get_test_command(Path("tests/test_foo.py"))
        mock_fn.assert_called_once_with("tests/test_foo.py")
        assert result is expected

    def test_get_test_command_returns_none(self):
        """Returns None when delegate returns None."""
        with patch(
            "pdd.split_validation.get_test_command_for_file",
            return_value=None,
        ):
            result = get_test_command(Path("tests/test_unknown.xyz"))
        assert result is None


# ---------------------------------------------------------------------------
# 11. get_lint_commands
# ---------------------------------------------------------------------------

class TestGetLintCommands:
    """Tests for get_lint_commands delegation."""

    def test_get_lint_commands_delegates(self):
        """Calls _get_lint_commands_impl with the file path."""
        expected = [LintCommand(command="ruff check f.py", cwd=None)]
        with patch(
            "pdd.split_validation._get_lint_commands_impl",
            return_value=expected,
        ) as mock_fn:
            result = get_lint_commands(Path("f.py"))
        mock_fn.assert_called_once_with(Path("f.py"))
        assert result == expected

    def test_get_lint_commands_empty_for_non_python(self):
        """Returns empty list for non-Python files (via real implementation)."""
        result = get_lint_commands(Path("file.js"))
        assert result == []


# ---------------------------------------------------------------------------
# 12. passed field behavior
# ---------------------------------------------------------------------------

class TestPassedField:
    """Tests for ValidationResult.passed based on severity."""

    def test_passed_true_warnings_only(self, tmp_path):
        """Only warning-severity failures -> passed=True."""
        # Prompt with missing tags -> only warnings
        (tmp_path / "c.prompt").write_text("no tags here")
        (tmp_path / "c.py").write_text("")  # example exists
        plan = FakePlan(children=[
            FakeChild(prompt_file="c.prompt", code_file="c.py"),
        ])
        with _mock_git_clean():
            result = validate_extraction(plan, tmp_path)
        assert all(f.severity == "warning" for f in result.failures)
        assert result.passed is True

    def test_passed_false_with_errors(self, tmp_path):
        """Error-severity failure -> passed=False."""
        plan = FakePlan(children=[])
        with patch(
            "pdd.split_validation.subprocess.run",
            return_value=subprocess.CompletedProcess(
                args=[], returncode=128, stdout="", stderr="not a git repo"
            ),
        ):
            result = validate_extraction(plan, tmp_path)
        assert result.passed is False
