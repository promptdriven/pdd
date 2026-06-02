"""Capability policy CLI for ``pdd checkup policy`` (not a top-level command)."""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Iterator, Optional

import click

from ..evidence_manifest import write_evidence_manifest
from ..path_resolution import get_default_resolver
from ..policy_check import PolicyResult, run_policy_check

_SKIP_DIR_NAMES = frozenset(
    {
        ".git",
        ".hg",
        ".svn",
        ".venv",
        "venv",
        "node_modules",
        "__pycache__",
        ".pdd",
        "dist",
        "build",
        ".tox",
        ".mypy_cache",
        ".pytest_cache",
    }
)


def _iter_python_targets(target: Path) -> Iterator[Path]:
    if target.is_file():
        if target.suffix == ".py":
            yield target
        return
    for path in sorted(target.rglob("*.py")):
        if any(part in _SKIP_DIR_NAMES for part in path.parts):
            continue
        yield path


@click.group(name="policy")
def policy_group() -> None:
    """Side-effect policy enforcement group."""


@policy_group.command(name="check")
@click.argument("target", type=click.Path(exists=True, path_type=Path))
@click.option(
    "--prompt",
    "prompt_path",
    type=click.Path(exists=True, path_type=Path),
    help="Explicitly specify the prompt file.",
)
@click.option("--json", "as_json", is_flag=True, help="Output results in JSON format.")
@click.option(
    "--strict",
    is_flag=True,
    help="Flag high-risk side effects even when the prompt has no <capabilities> section.",
)
@click.option("--evidence", is_flag=True, help="Write findings to an evidence manifest.")
def check(
    target: Path,
    prompt_path: Optional[Path],
    as_json: bool,
    strict: bool,
    evidence: bool,
) -> None:
    """Scan files or directories for policy violations.

    Exit codes: 0 pass, 1 violations (non-strict), 2 strict violations or parse errors.
    """
    results: list[PolicyResult] = []
    any_violations = False
    system_errors = False

    resolver = get_default_resolver()

    for py_file in _iter_python_targets(target):
        current_prompt = prompt_path
        if not current_prompt:
            try:
                prompt_name = f"{py_file.stem}_python.prompt"
                current_prompt = resolver.resolve_prompt_template(prompt_name)
            except (OSError, ValueError, RuntimeError):
                current_prompt = None

        result = run_policy_check(py_file, current_prompt, strict=strict)
        results.append(result)
        if not result.passed:
            any_violations = True
            if any(issue.category == "system" for issue in result.issues):
                system_errors = True

    if not results:
        raise click.ClickException(f"No Python files found under {target}")

    if as_json:
        output = [
            {
                "target": str(r.target_path),
                "passed": r.passed,
                "capabilities": [
                    {
                        "modal": cap.modal,
                        "text": cap.text,
                        "line": cap.line,
                        "is_must_not": cap.is_must_not,
                    }
                    for cap in r.capabilities
                ],
                "issues": [
                    {
                        "category": issue.category,
                        "message": issue.message,
                        "line": issue.line,
                        "col": issue.col,
                        "severity": issue.severity,
                    }
                    for issue in r.issues
                ],
            }
            for r in results
        ]
        click.echo(json.dumps(output, indent=2))
    else:
        for result in results:
            if result.passed:
                click.secho(f"PASS: {result.target_path}", fg="green")
            else:
                color = (
                    "red"
                    if strict or any(issue.category == "system" for issue in result.issues)
                    else "yellow"
                )
                click.secho(f"FAIL: {result.target_path}", fg=color)
                for issue in result.issues:
                    click.echo(f"  [{issue.category}] {issue.message} (line {issue.line})")

    if evidence:
        policy_status = "passed" if not any_violations else "failed"
        write_evidence_manifest(
            command="pdd checkup policy check",
            prompt_file=prompt_path,
            output_files=[r.target_path for r in results],
            validation={"policy": policy_status},
        )

    if any_violations:
        sys.exit(2 if (strict or system_errors) else 1)
    sys.exit(0)
