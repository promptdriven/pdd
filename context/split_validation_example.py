#!/usr/bin/env python3
"""Example usage of pdd.split_validation.

This script demonstrates the public API of split_validation:
- ValidationFailure / ValidationResult dataclasses
- validate_extraction(plan, worktree) -> ValidationResult
- get_test_command(file) -> Optional[TestCommand]
- get_lint_commands(file) -> list[LintCommand]

The example builds a tiny on-disk "worktree" using a temporary directory so the
script is self-contained and runnable without external state.

Inputs:
    plan: any object with a ``children`` attribute (list of either
          dataclass-like objects with .prompt_file/.code_file or dicts using
          new_prompt/new_source/prompt_file/code_file keys), and an optional
          ``parent_changes`` dict.
    worktree (Path): directory where the extraction took place.

Output:
    ValidationResult with `passed: bool`, `failures: list[ValidationFailure]`,
    and `failure_type: str` ∈ {"none", "extraction", "metadata",
    "completeness", "multiple"}.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from unittest.mock import patch

# Make `pdd` importable regardless of the working directory.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

# Suppress test-seam progress prints so example output is clean.
from pdd import split_validation  # noqa: E402

split_validation.quiet_import = True

from pdd.split_validation import (  # noqa: E402
    LintCommand,
    TestCommand,
    ValidationFailure,
    ValidationResult,
    get_lint_commands,
    get_test_command,
    validate_extraction,
)


@dataclass
class FakeChild:
    """A simple child object: prompt_file + code_file."""
    prompt_file: str
    code_file: str
    name: str = ""


@dataclass
class FakePlan:
    """A simple plan object with a list of children."""
    children: list


PROMPT_TEMPLATE = (
    "<pdd-reason>demo reason</pdd-reason>\n"
    "<pdd-interface>{}</pdd-interface>\n"
    "<pdd-dependency>none</pdd-dependency>\n"
)


def _mock_clean_git():
    """Patch subprocess.run so git status returns 0 with empty output."""
    return patch(
        "pdd.split_validation.subprocess.run",
        return_value=subprocess.CompletedProcess(
            args=["git", "status", "--porcelain"],
            returncode=0,
            stdout="",
            stderr="",
        ),
    )


def demonstrate_dataclasses() -> None:
    """ValidationFailure/ValidationResult dataclass shapes.

    Returns:
        None — prints the constructed objects.
    """
    print("=== Dataclasses ===")
    f_err = ValidationFailure(check="byte_equivalence", message="boom")
    f_warn = ValidationFailure(check="prompt_metadata", message="missing", severity="warning")
    res = ValidationResult(passed=False, failures=[f_err, f_warn], failure_type="multiple")
    print(f"  ValidationFailure (default severity): {f_err.severity}")
    print(f"  ValidationFailure (warning):          {f_warn.severity}")
    print(f"  ValidationResult.passed:              {res.passed}")
    print(f"  ValidationResult.failure_type:        {res.failure_type}")
    print()


def demonstrate_clean_validation() -> None:
    """All checks happy-path -> passed=True, failure_type='none'."""
    print("=== Clean extraction (all checks pass) ===")
    with tempfile.TemporaryDirectory() as td:
        wt = Path(td)
        (wt / "child.prompt").write_text(PROMPT_TEMPLATE)
        (wt / "child.py").write_text("# example file used as the example fallback\n")

        plan = FakePlan(children=[FakeChild("child.prompt", "child.py", "child")])
        with _mock_clean_git():
            result = validate_extraction(plan, wt)

        print(f"  passed:       {result.passed}")
        print(f"  failure_type: {result.failure_type}")
        print(f"  failures:     {len(result.failures)}")
    print()


def demonstrate_missing_example() -> None:
    """A child without a corresponding example file -> example_file error."""
    print("=== Missing example file (error) ===")
    with tempfile.TemporaryDirectory() as td:
        wt = Path(td)
        (wt / "alpha.prompt").write_text(PROMPT_TEMPLATE)
        # Intentionally do NOT create alpha.py / examples/alpha_example.py

        plan = FakePlan(children=[FakeChild("alpha.prompt", "alpha.py", "alpha")])
        with _mock_clean_git():
            result = validate_extraction(plan, wt)

        print(f"  passed:       {result.passed}")
        print(f"  failure_type: {result.failure_type}")
        for f in result.failures:
            print(f"    [{f.severity}] {f.check}: {f.message[:80]}")
    print()


def demonstrate_metadata_warnings() -> None:
    """Prompt missing required tags -> three metadata warnings, still passed."""
    print("=== Missing prompt metadata tags (warnings) ===")
    with tempfile.TemporaryDirectory() as td:
        wt = Path(td)
        (wt / "beta.prompt").write_text("no tags at all")
        (wt / "beta.py").write_text("")  # serves as example fallback

        plan = FakePlan(children=[FakeChild("beta.prompt", "beta.py", "beta")])
        with _mock_clean_git():
            result = validate_extraction(plan, wt)

        print(f"  passed (only warnings): {result.passed}")
        print(f"  failure_type:           {result.failure_type}")
        for f in result.failures:
            print(f"    [{f.severity}] {f.check}: {f.message}")
    print()


def demonstrate_dict_child() -> None:
    """LLM-style dict children with new_prompt/new_source keys."""
    print("=== Dict child (LLM JSON shape) ===")
    with tempfile.TemporaryDirectory() as td:
        wt = Path(td)
        (wt / "gamma.prompt").write_text(PROMPT_TEMPLATE)
        (wt / "examples").mkdir()
        (wt / "examples" / "gamma_example.py").write_text("")

        plan = FakePlan(children=[
            {"name": "gamma", "new_prompt": "gamma.prompt", "new_source": "gamma.py"},
        ])
        with _mock_clean_git():
            result = validate_extraction(plan, wt)

        print(f"  passed:       {result.passed}")
        print(f"  failure_type: {result.failure_type}")
    print()


def demonstrate_worktree_not_directory() -> None:
    """Non-existent worktree -> immediate byte_equivalence error."""
    print("=== Worktree not a directory ===")
    plan = FakePlan(children=[])
    bogus = Path("/nonexistent/path/that/does/not/exist")
    result = validate_extraction(plan, bogus)
    print(f"  passed:                      {result.passed}")
    print(f"  failure_type:                {result.failure_type}")
    print(f"  failures[0].check:           {result.failures[0].check}")
    print(f"  'not a directory' in message: {'not a directory' in result.failures[0].message}")
    print()


def demonstrate_test_and_lint_helpers() -> None:
    """get_test_command and get_lint_commands delegate helpers.

    get_test_command(file) -> Optional[TestCommand]
    get_lint_commands(file) -> list[LintCommand]
    """
    print("=== get_test_command / get_lint_commands ===")
    # Mock the underlying delegates so the example does not depend on local
    # config files.
    fake_tc = TestCommand(command="pytest tests/test_x.py", cwd=None)
    with patch("pdd.split_validation.get_test_command_for_file", return_value=fake_tc):
        tc = get_test_command(Path("tests/test_x.py"))
    print(f"  get_test_command -> {tc}")

    # Real call: non-Python file returns []
    print(f"  get_lint_commands('foo.js'): {get_lint_commands(Path('foo.js'))}")

    fake_lints = [LintCommand(command="ruff check x.py", cwd=None)]
    with patch("pdd.split_validation._get_lint_commands_impl", return_value=fake_lints):
        lints = get_lint_commands(Path("x.py"))
    print(f"  get_lint_commands('x.py') (mocked): {lints}")
    print()


def main() -> None:
    """Run all demonstrations."""
    print("split_validation example — module overview")
    print("-" * 60)
    demonstrate_dataclasses()
    demonstrate_clean_validation()
    demonstrate_missing_example()
    demonstrate_metadata_warnings()
    demonstrate_dict_child()
    demonstrate_worktree_not_directory()
    demonstrate_test_and_lint_helpers()
    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
