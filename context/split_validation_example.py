#!/usr/bin/env python3
"""Example usage of pdd.split_validation.

Demonstrates the post-extraction validation API used by the agentic split
orchestrator (per-child verify gate at step 6v + cross-cutting cycle at
steps 7a/7b).

Run from anywhere::

    python context/split_validation_example.py

The script is fully self-contained: it stages a fake worktree under
``tmp_path``, builds plan-like objects, monkey-patches ``subprocess.run``
to simulate ``git status`` output, and drives every public function:

- ``validate_extraction(plan, worktree)`` -> ``ValidationResult``
- ``get_test_command(file)`` -> ``Optional[TestCommand]``
- ``get_lint_commands(file)`` -> ``list[LintCommand]``

It also shows the duck-typed ``children`` contract: dataclass-style
objects with ``prompt_file`` / ``code_file`` AND dicts with
``new_prompt`` / ``new_source`` (the LLM step-4 output format).
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import List
from unittest.mock import patch

# Make ``pdd`` importable regardless of the working directory.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from rich.console import Console
from rich.panel import Panel
from rich.rule import Rule

from pdd.split_validation import (  # noqa: E402  (after sys.path edit)
    LintCommand,
    TestCommand,
    ValidationFailure,
    ValidationResult,
    get_lint_commands,
    get_test_command,
    validate_extraction,
)

console = Console()


# ---------------------------------------------------------------------------
# Fixture helpers — stand-ins for the orchestrator's SplitPlan / SplitOption
# ---------------------------------------------------------------------------


@dataclass
class FakeChild:
    """Dataclass-style child (mirrors fields the validator reads).

    Inputs:
        prompt_file: path (relative to worktree) of the child's prompt
        code_file: path (relative to worktree) of the child's source code
        example_file: optional explicit example path
        test_file: optional explicit test path
    """

    prompt_file: str
    code_file: str
    example_file: str = ""
    test_file: str = ""


@dataclass
class FakePlan:
    """Plan-like container holding a list of children."""

    children: List[object] = field(default_factory=list)


def _clean_git_patch():
    """Patch subprocess.run inside split_validation to simulate a clean git
    repo (returncode == 0, empty output). Returns the unittest.mock patcher.
    """
    return patch(
        "pdd.split_validation.subprocess.run",
        return_value=subprocess.CompletedProcess(
            args=["git", "status", "--porcelain"],
            returncode=0,
            stdout="",
            stderr="",
        ),
    )


def _print_result(label: str, result: ValidationResult) -> None:
    """Pretty-print a ValidationResult for the demo."""
    console.print(Rule(label))
    console.print(
        f"  passed = [bold]{result.passed}[/bold]   "
        f"failure_type = [bold]{result.failure_type}[/bold]   "
        f"failures = {len(result.failures)}"
    )
    for failure in result.failures:
        color = "red" if failure.severity == "error" else "yellow"
        console.print(
            f"   [{color}]{failure.severity:>7}[/{color}]  "
            f"[{failure.check}] {failure.message}"
        )
    print()


# ---------------------------------------------------------------------------
# Demonstration 1 — Happy path: every check passes
# ---------------------------------------------------------------------------


def demo_happy_path(worktree: Path) -> None:
    """All required artefacts present -> passed=True, failure_type='none'."""
    console.print(Panel("[bold cyan]1. Happy path[/bold cyan]"))

    full_prompt = (
        "<pdd-reason>why</pdd-reason>\n"
        "<pdd-interface>{}</pdd-interface>\n"
        "<pdd-dependency>dep</pdd-dependency>\n"
    )
    (worktree / "alpha.prompt").write_text(full_prompt)
    (worktree / "alpha.py").write_text("# alpha module\n")
    (worktree / "test_alpha.py").write_text("import alpha\n")

    plan = FakePlan(children=[FakeChild(prompt_file="alpha.prompt", code_file="alpha.py")])
    with _clean_git_patch():
        result = validate_extraction(plan, worktree)
    _print_result("Happy path result", result)


# ---------------------------------------------------------------------------
# Demonstration 2 — Per-child gate: SimpleNamespace single-child view
# ---------------------------------------------------------------------------


def demo_per_child_gate(worktree: Path) -> None:
    """Validator works on any subset of children — used at step 6v."""
    console.print(Panel("[bold cyan]2. Per-child verify gate (step 6v)[/bold cyan]"))

    full_prompt = (
        "<pdd-reason>r</pdd-reason><pdd-interface>{}</pdd-interface>"
        "<pdd-dependency>d</pdd-dependency>"
    )
    (worktree / "beta.prompt").write_text(full_prompt)
    (worktree / "beta.py").write_text("# beta\n")
    (worktree / "test_beta.py").write_text("import beta\n")

    only_beta = SimpleNamespace(
        children=[FakeChild(prompt_file="beta.prompt", code_file="beta.py")]
    )
    with _clean_git_patch():
        result = validate_extraction(only_beta, worktree)
    _print_result("Single-child view", result)


# ---------------------------------------------------------------------------
# Demonstration 3 — Dict children (LLM step-4 output format)
# ---------------------------------------------------------------------------


def demo_dict_children(worktree: Path) -> None:
    """The validator is duck-typed: dicts with new_prompt/new_source work."""
    console.print(Panel("[bold cyan]3. Dict children (LLM step-4 format)[/bold cyan]"))

    full_prompt = (
        "<pdd-reason>r</pdd-reason><pdd-interface>{}</pdd-interface>"
        "<pdd-dependency>d</pdd-dependency>"
    )
    (worktree / "gamma.prompt").write_text(full_prompt)
    (worktree / "gamma.py").write_text("# gamma\n")
    (worktree / "test_gamma.py").write_text("import gamma\n")
    (worktree / "examples").mkdir(exist_ok=True)
    (worktree / "examples" / "gamma_example.py").write_text("")

    plan = FakePlan(children=[
        {"name": "gamma", "new_prompt": "gamma.prompt", "new_source": "gamma.py"},
    ])
    with _clean_git_patch():
        result = validate_extraction(plan, worktree)
    _print_result("Dict children", result)


# ---------------------------------------------------------------------------
# Demonstration 4 — Each failure category in isolation
# ---------------------------------------------------------------------------


def demo_failure_categories(worktree: Path) -> None:
    """Show each failure_type bucket: extraction / completeness / metadata."""
    console.print(Panel("[bold cyan]4. Failure categorization[/bold cyan]"))

    # 4a — byte_equivalence error (git rc != 0) -> failure_type 'extraction'.
    plan_empty = FakePlan(children=[])
    with patch(
        "pdd.split_validation.subprocess.run",
        return_value=subprocess.CompletedProcess(
            args=[], returncode=128, stdout="", stderr="fatal: not a git repo"
        ),
    ):
        result = validate_extraction(plan_empty, worktree)
    _print_result("4a) byte_equivalence (extraction)", result)

    # 4b — Missing example file -> completeness.
    full_prompt = (
        "<pdd-reason>r</pdd-reason><pdd-interface>{}</pdd-interface>"
        "<pdd-dependency>d</pdd-dependency>"
    )
    (worktree / "delta.prompt").write_text(full_prompt)
    (worktree / "test_delta.py").write_text("import delta\n")
    plan_delta = FakePlan(children=[FakeChild(prompt_file="delta.prompt", code_file="delta.py")])
    with _clean_git_patch():
        result = validate_extraction(plan_delta, worktree)
    _print_result("4b) example_file missing (completeness)", result)

    # 4c — Prompt missing required tags -> metadata (warnings only, passed=True).
    (worktree / "epsilon.prompt").write_text("no required tags here")
    (worktree / "epsilon.py").write_text("")
    (worktree / "test_epsilon.py").write_text("import epsilon\n")
    plan_eps = FakePlan(children=[FakeChild(prompt_file="epsilon.prompt", code_file="epsilon.py")])
    with _clean_git_patch():
        result = validate_extraction(plan_eps, worktree)
    _print_result("4c) prompt_metadata warnings (metadata)", result)


# ---------------------------------------------------------------------------
# Demonstration 5 — Lint and test command resolution
# ---------------------------------------------------------------------------


def demo_command_resolvers() -> None:
    """``get_test_command`` / ``get_lint_commands`` thin wrappers."""
    console.print(Panel("[bold cyan]5. Test & lint command resolvers[/bold cyan]"))

    # Test command resolution returns a TestCommand or None.
    fake_test = TestCommand(command="pytest tests/test_x.py -xvs", cwd=None)
    with patch(
        "pdd.split_validation.get_test_command_for_file",
        return_value=fake_test,
    ):
        tc = get_test_command(Path("tests/test_x.py"))
    console.print(f"  get_test_command -> {tc}")

    with patch(
        "pdd.split_validation.get_test_command_for_file",
        return_value=None,
    ):
        tc_none = get_test_command(Path("tests/test_unknown.xyz"))
    console.print(f"  get_test_command (unknown ext) -> {tc_none}")

    # Lint commands: returns [] for non-Python files (real implementation).
    js_lints = get_lint_commands(Path("foo.js"))
    console.print(f"  get_lint_commands('foo.js') -> {js_lints}")

    # Mocked Python case to avoid needing config files on disk.
    fake_lints = [LintCommand(command="ruff check foo.py", cwd=None)]
    with patch(
        "pdd.split_validation._get_lint_commands_impl",
        return_value=fake_lints,
    ):
        py_lints = get_lint_commands(Path("foo.py"))
    console.print(f"  get_lint_commands('foo.py')  -> {py_lints}")
    print()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    """Run every demonstration in a temporary worktree.

    Output: prints validation results to stdout via rich. Exits 0 on success.
    Each demonstration uses a fresh subdirectory under a tmp dir so demos
    don't share state.
    """
    console.print(Panel(
        "[bold]pdd.split_validation usage examples[/bold]\n\n"
        "Demos: happy path, per-child gate (SimpleNamespace),\n"
        "dict children, failure categorization, and command resolvers.",
        title="Overview",
        border_style="blue",
    ))
    print()

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for n, fn in enumerate((demo_happy_path, demo_per_child_gate,
                                demo_dict_children, demo_failure_categories), 1):
            sub = root / f"demo_{n}"
            sub.mkdir()
            fn(sub)

    demo_command_resolvers()

    # Show the dataclass shapes so readers know the public surface.
    console.print(Rule("Dataclass surface"))
    console.print(f"  ValidationFailure -> {ValidationFailure(check='x', message='y')}")
    console.print(
        f"  ValidationResult  -> {ValidationResult(passed=True)}"
    )
    print()
    console.print("[bold green]All examples completed successfully.[/bold green]")


if __name__ == "__main__":
    main()
