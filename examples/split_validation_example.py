#!/usr/bin/env python3
"""Example usage of the split_validation module.

Demonstrates the three public functions:
- validate_extraction(plan, worktree) -> ValidationResult
- get_test_command(file) -> Optional[TestCommand]
- get_lint_commands(file) -> list[LintCommand]

All external dependencies are mocked so this runs standalone.
"""
from __future__ import annotations

import sys
import os
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from unittest.mock import patch, MagicMock

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

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
# Helper: fake plan objects
# ---------------------------------------------------------------------------

@dataclass
class FakeChild:
    """A mock child with prompt_file and code_file attributes."""

    prompt_file: str
    code_file: str


@dataclass
class FakePlan:
    """A mock plan with a children list."""

    children: list


# ---------------------------------------------------------------------------
# Demo 1: validate_extraction — all checks pass
# ---------------------------------------------------------------------------

def demo_validate_all_pass() -> None:
    """Show validate_extraction when all checks pass.

    Sets up a temp directory that looks like a valid worktree:
    - git diff --stat returns empty (no unexpected changes)
    - All child prompt files exist with required metadata tags
    - Example files exist
    - Test files reference only their own module
    """
    print("=" * 60)
    print("Demo 1: validate_extraction — all checks pass")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        worktree = Path(tmpdir)

        # Create child prompt files with all required tags
        prompt_content = (
            "<pdd-reason>Reason</pdd-reason>\n"
            "<pdd-interface>{}</pdd-interface>\n"
            "<pdd-dependency>dep</pdd-dependency>\n"
        )
        (worktree / "child_a.prompt").write_text(prompt_content)
        (worktree / "child_b.prompt").write_text(prompt_content)

        # Create example files (derived from prompt_file with .py suffix)
        (worktree / "child_a.py").write_text("# example a\n")
        (worktree / "child_b.py").write_text("# example b\n")

        # Create test files in tests/ directory
        (worktree / "tests").mkdir()
        (worktree / "tests" / "test_child_a.py").write_text(
            "from child_a import something\n"
        )
        (worktree / "tests" / "test_child_b.py").write_text(
            "from child_b import something\n"
        )

        plan = FakePlan(children=[
            FakeChild(prompt_file="child_a.prompt", code_file="child_a.py"),
            FakeChild(prompt_file="child_b.prompt", code_file="child_b.py"),
        ])

        # Mock git diff to return empty (no changes)
        with patch("pdd.split_validation.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess(
                args=["git", "diff", "--stat"],
                returncode=0,
                stdout="",
                stderr="",
            )
            result = validate_extraction(plan, worktree)

        print(f"  passed: {result.passed}")
        print(f"  failure_type: {result.failure_type}")
        print(f"  failures: {result.failures}")
    print()


# ---------------------------------------------------------------------------
# Demo 2: validate_extraction — some failures
# ---------------------------------------------------------------------------

def demo_validate_with_failures() -> None:
    """Show validate_extraction when checks detect problems.

    Demonstrates:
    - byte_equivalence error (git diff shows changes)
    - children_completeness error (missing prompt file)
    - prompt_metadata warning (missing tags)
    - example_file error (missing example)
    """
    print("=" * 60)
    print("Demo 2: validate_extraction — multiple failures")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        worktree = Path(tmpdir)

        # Only create one prompt file, missing tags
        (worktree / "mod_a.prompt").write_text("no tags here\n")
        # mod_b.prompt intentionally missing -> completeness failure

        # No example files -> example_file failures

        plan = FakePlan(children=[
            FakeChild(prompt_file="mod_a.prompt", code_file="pdd/mod_a.py"),
            FakeChild(prompt_file="mod_b.prompt", code_file="pdd/mod_b.py"),
        ])

        # Mock git diff to show changes
        with patch("pdd.split_validation.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess(
                args=["git", "diff", "--stat"],
                returncode=0,
                stdout=" src/file.py | 5 ++---\n 1 file changed\n",
                stderr="",
            )
            result = validate_extraction(plan, worktree)

        print(f"  passed: {result.passed}")
        print(f"  failure_type: {result.failure_type}")
        print(f"  failures ({len(result.failures)}):")
        for f in result.failures:
            print(f"    [{f.severity}] {f.check}: {f.message}")
    print()


# ---------------------------------------------------------------------------
# Demo 3: get_test_command
# ---------------------------------------------------------------------------

def demo_get_test_command() -> None:
    """Show get_test_command delegating to get_test_command_for_file.

    Parameters:
        None

    Returns:
        None — prints the resolved TestCommand or None.

    get_test_command(file: Path) -> Optional[TestCommand]
      file: Path to the test file to resolve a command for.
      Returns a TestCommand(command=str, cwd=Optional[Path]) or None.
    """
    print("=" * 60)
    print("Demo 3: get_test_command")
    print("=" * 60)

    test_file = Path("tests/test_example.py")

    mock_result = TestCommand(command="pytest -xvs tests/test_example.py", cwd=None)

    with patch(
        "pdd.split_validation.get_test_command_for_file",
        return_value=mock_result,
    ):
        result = get_test_command(test_file)

    if result:
        print(f"  command: {result.command}")
        print(f"  cwd: {result.cwd or '(caller decides)'}")
    else:
        print("  No command resolved — agentic fallback needed")
    print()


# ---------------------------------------------------------------------------
# Demo 4: get_lint_commands
# ---------------------------------------------------------------------------

def demo_get_lint_commands() -> None:
    """Show get_lint_commands delegating to the get_lint_commands module.

    Parameters:
        None

    Returns:
        None — prints the resolved LintCommand list.

    get_lint_commands(file: Path) -> list[LintCommand]
      file: Path to the source file to lint.
      Returns a list of LintCommand(command=str, cwd=Optional[Path]).
      Empty list for non-Python files (hybrid contract).
    """
    print("=" * 60)
    print("Demo 4: get_lint_commands")
    print("=" * 60)

    source_file = Path("pdd/my_module.py")

    mock_cmds = [
        LintCommand(command="ruff check pdd/my_module.py", cwd=Path("/project")),
        LintCommand(command="mypy pdd/my_module.py", cwd=Path("/project")),
    ]

    with patch(
        "pdd.split_validation._get_lint_commands_impl",
        return_value=mock_cmds,
    ):
        results = get_lint_commands(source_file)

    print(f"  {len(results)} lint command(s):")
    for cmd in results:
        print(f"    command: {cmd.command}")
        print(f"    cwd: {cmd.cwd}")
    print()


# ---------------------------------------------------------------------------
# Demo 5: ValidationFailure and ValidationResult dataclasses
# ---------------------------------------------------------------------------

def demo_dataclasses() -> None:
    """Show direct construction of ValidationFailure and ValidationResult.

    ValidationFailure fields:
      check (str): name of the check that failed
      message (str): human-readable failure description
      severity (str): "error" (default) or "warning"

    ValidationResult fields:
      passed (bool): True if no error-severity failures
      failures (list[ValidationFailure]): all failures found
      failure_type (str): "none", "extraction", "metadata", "completeness", or "multiple"
    """
    print("=" * 60)
    print("Demo 5: Dataclass construction")
    print("=" * 60)

    # Default severity is "error"
    f1 = ValidationFailure(check="byte_equivalence", message="unexpected diff")
    print(f"  f1.severity: {f1.severity}")

    # Explicit warning severity
    f2 = ValidationFailure(
        check="prompt_metadata", message="missing tag", severity="warning"
    )
    print(f"  f2.severity: {f2.severity}")

    # Result with no failures
    r_ok = ValidationResult(passed=True, failures=[], failure_type="none")
    print(f"  r_ok.passed: {r_ok.passed}, failure_type: {r_ok.failure_type}")

    # Result with mixed failures
    r_bad = ValidationResult(passed=False, failures=[f1, f2], failure_type="multiple")
    print(f"  r_bad.passed: {r_bad.passed}, failure_type: {r_bad.failure_type}")
    print()


def main() -> None:
    """Run all demonstration examples."""
    demo_validate_all_pass()
    demo_validate_with_failures()
    demo_get_test_command()
    demo_get_lint_commands()
    demo_dataclasses()
    print("All examples completed!")


if __name__ == "__main__":
    main()
