#!/usr/bin/env python3
"""A0→A1 formalization via ``pdd checkup lint``, ``contract check``, and ``coverage``.

Runs the product checkup commands (JSON output), parses deterministic suggestions,
and applies benchmark-local write-backs until lint, contract, and coverage pass
or iteration budget is exhausted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

_PIPELINE_DIR = Path(__file__).resolve().parent
_BENCHMARK_ROOT = _PIPELINE_DIR.parent
_REPO_ROOT = _BENCHMARK_ROOT.parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
if str(_PIPELINE_DIR) not in sys.path:
    sys.path.insert(0, str(_PIPELINE_DIR))

import checkup_apply  # noqa: E402
import writeback  # noqa: E402

SCRIPT_VERSION = "checkup_formalize_v1"
DEFAULT_MAX_ITERS = 8


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _append_command_log(log_path: Optional[Path], entry: dict[str, Any]) -> None:
    if log_path is None:
        return
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry, sort_keys=True) + "\n")


def _run_checkup_json(
    subcommand: list[str],
    *,
    project_root: Path,
) -> tuple[int, Any, str]:
    """Invoke ``python -m pdd checkup … --json`` and parse stdout."""
    cmd = [sys.executable, "-m", "pdd", "checkup", *subcommand, "--json"]
    proc = subprocess.run(
        cmd,
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    stdout = proc.stdout.strip()
    stderr = proc.stderr.strip()
    data: Any = None
    if stdout:
        try:
            data = json.loads(stdout)
        except json.JSONDecodeError:
            data = {"parse_error": stdout[:500], "stderr": stderr[:500]}
    return proc.returncode, data, stderr


def _lint_pass(exit_code: int) -> bool:
    return exit_code == 0


def _contract_pass(exit_code: int) -> bool:
    return exit_code == 0


def _coverage_pass(payload: dict[str, Any]) -> bool:
    return checkup_apply.coverage_exit_code(payload) == 0


def formalize(
    *,
    input_path: Path,
    output_path: Path,
    commands_log: Optional[Path],
    max_iters: int,
    dry_run: bool,
    verbose: bool,
    project_root: Path,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
    allow_waivers: bool = True,
) -> dict[str, Any]:
    """Run checkup-driven A0→A1 formalization; return manifest dict."""
    if not input_path.is_file():
        raise FileNotFoundError(f"Input not found: {input_path}")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(input_path, output_path)

    manifest: dict[str, Any] = {
        "script_version": SCRIPT_VERSION,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "input": str(input_path),
        "output": str(output_path),
        "input_sha256": _sha256(input_path),
        "dry_run": dry_run,
        "stories_dir": str(stories_dir) if stories_dir else None,
        "tests_dir": str(tests_dir) if tests_dir else None,
        "allow_waivers": allow_waivers,
        "iterations": [],
    }

    if dry_run:
        lint_code, lint_data, _ = _run_checkup_json(
            ["lint", str(output_path)], project_root=project_root,
        )
        contract_args = ["contract", "check", str(output_path)]
        contract_code, contract_data, _ = _run_checkup_json(
            contract_args, project_root=project_root,
        )
        coverage_args = [str(output_path)]
        if stories_dir:
            coverage_args.extend(["--stories-dir", str(stories_dir)])
        if tests_dir:
            coverage_args.extend(["--tests-dir", str(tests_dir)])
        coverage_code, coverage_data, _ = _run_checkup_json(
            ["coverage", *coverage_args], project_root=project_root,
        )
        manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
        manifest["output_sha256"] = _sha256(output_path)
        manifest["summary"] = {
            "lint_exit_code": lint_code,
            "contract_exit_code": contract_code,
            "coverage_exit_code": coverage_code,
            "checkup_pass": False,
            "lint_pass": _lint_pass(lint_code),
            "contract_pass": _contract_pass(contract_code),
            "coverage_pass": _coverage_pass(coverage_data or {}),
            "lint_warnings": _warn_count(lint_data),
            "lint_errors": _error_count(lint_data),
            "contract_errors": _contract_errors(contract_data),
            "contract_warnings": _contract_warnings(contract_data),
        }
        return manifest

    total_written = {"vocabulary": 0, "contract_rules": 0, "coverage_links": 0, "waivers": 0}
    lint_code = contract_code = coverage_code = 1
    lint_data: Any = []
    contract_data: Any = []
    coverage_data: Any = {"results": []}

    for iteration in range(1, max_iters + 1):
        step: dict[str, Any] = {"iteration": iteration, "stage": "checkup_loop"}

        lint_code, lint_data, lint_stderr = _run_checkup_json(
            ["lint", str(output_path)], project_root=project_root,
        )
        lint_counts = checkup_apply.apply_lint_results(output_path, lint_data or [])
        for key, value in lint_counts.items():
            if key in total_written and isinstance(value, int):
                total_written[key] += value

        contract_args = ["contract", "check", str(output_path)]
        contract_code, contract_data, contract_stderr = _run_checkup_json(
            contract_args, project_root=project_root,
        )
        contract_counts = checkup_apply.apply_contract_results(
            output_path, contract_data or [],
        )
        for key, value in contract_counts.items():
            total_written[key] = total_written.get(key, 0) + value

        coverage_args = [str(output_path)]
        if stories_dir:
            coverage_args.extend(["--stories-dir", str(stories_dir)])
        if tests_dir:
            coverage_args.extend(["--tests-dir", str(tests_dir)])
        coverage_code, coverage_data, coverage_stderr = _run_checkup_json(
            ["coverage", *coverage_args], project_root=project_root,
        )
        coverage_counts = checkup_apply.apply_coverage_results(
            output_path,
            coverage_data or {},
            stories_dir=stories_dir,
            allow_waivers=allow_waivers,
        )
        for key, value in coverage_counts.items():
            total_written[key] = total_written.get(key, 0) + value

        step.update(
            {
                "lint_exit_code": lint_code,
                "contract_exit_code": contract_code,
                "coverage_exit_code": coverage_code,
                "lint_counts": lint_counts,
                "contract_counts": contract_counts,
                "coverage_counts": coverage_counts,
                "lint_pass": _lint_pass(lint_code),
                "contract_pass": _contract_pass(contract_code),
                "coverage_pass": _coverage_pass(coverage_data or {}),
            }
        )
        if verbose and lint_stderr:
            step["lint_stderr"] = lint_stderr[:300]
        if verbose and contract_stderr:
            step["contract_stderr"] = contract_stderr[:300]
        if verbose and coverage_stderr:
            step["coverage_stderr"] = coverage_stderr[:300]

        manifest["iterations"].append(step)
        _append_command_log(commands_log, step)

        wrote = (
            lint_counts.get("vocabulary", 0)
            + contract_counts.get("vocabulary", 0)
            + contract_counts.get("contract_rules", 0)
            + coverage_counts.get("coverage_links", 0)
            + coverage_counts.get("waivers", 0)
        )
        all_pass = step["lint_pass"] and step["contract_pass"] and step["coverage_pass"]
        if all_pass or wrote == 0:
            break

    sections = writeback.extract_sections(output_path.read_text(encoding="utf-8"))
    manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    manifest["output_sha256"] = _sha256(output_path)
    manifest["summary"] = {
        "writeback_totals": total_written,
        "lint_exit_code": lint_code,
        "contract_exit_code": contract_code,
        "coverage_exit_code": coverage_code,
        "lint_pass": _lint_pass(lint_code),
        "contract_pass": _contract_pass(contract_code),
        "coverage_pass": _coverage_pass(coverage_data or {}),
        "checkup_pass": (
            _lint_pass(lint_code)
            and _contract_pass(contract_code)
            and _coverage_pass(coverage_data or {})
        ),
        "lint_warnings": _warn_count(lint_data),
        "lint_errors": _error_count(lint_data),
        "contract_errors": _contract_errors(contract_data),
        "contract_warnings": _contract_warnings(contract_data),
        "has_vocabulary": "vocabulary" in sections,
        "has_contract_rules": bool(sections.get("contract_rules", "").strip()),
        "has_coverage": bool(sections.get("coverage", "").strip()),
        "iterations_run": len(manifest["iterations"]),
    }
    return manifest


def _warn_count(lint_data: Any) -> int:
    if not isinstance(lint_data, list):
        return 0
    return sum(int(r.get("warn_count", 0)) for r in lint_data)


def _error_count(lint_data: Any) -> int:
    if not isinstance(lint_data, list):
        return 0
    return sum(int(r.get("error_count", 0)) for r in lint_data)


def _contract_errors(contract_data: Any) -> int:
    if not isinstance(contract_data, list):
        return 0
    return sum(int(r.get("error_count", 0)) for r in contract_data)


def _contract_warnings(contract_data: Any) -> int:
    if not isinstance(contract_data, list):
        return 0
    return sum(int(r.get("warn_count", 0)) for r in contract_data)


def main(argv: Optional[list[str]] = None) -> int:
    """CLI entrypoint."""
    parser = argparse.ArgumentParser(
        description="Benchmark A0→A1 via pdd checkup lint/contract/coverage",
    )
    parser.add_argument("--input", type=Path, required=True, help="Handwritten A0 prompt")
    parser.add_argument("--output", type=Path, required=True, help="Generated A1 prompt path")
    parser.add_argument(
        "--commands-log",
        type=Path,
        default=None,
        help="Append JSONL audit log (one object per line)",
    )
    parser.add_argument("--max-iters", type=int, default=DEFAULT_MAX_ITERS)
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Copy input only; run checkup metrics without writeback",
    )
    parser.add_argument(
        "--stories-dir",
        type=Path,
        default=None,
        help="Stories directory for contract/coverage checkup commands",
    )
    parser.add_argument(
        "--tests-dir",
        type=Path,
        default=None,
        help="Tests directory for coverage checkup command",
    )
    parser.add_argument(
        "--no-waivers",
        action="store_true",
        help="Do not add benchmark waivers for uncovered tier-A rules",
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument(
        "--project-root",
        type=Path,
        default=_REPO_ROOT,
        help="Working directory for pdd checkup subprocesses",
    )
    parser.add_argument("--json", action="store_true", dest="as_json", help="Print manifest JSON")
    args = parser.parse_args(argv)

    manifest = formalize(
        input_path=args.input.resolve(),
        output_path=args.output.resolve(),
        commands_log=args.commands_log.resolve() if args.commands_log else None,
        max_iters=args.max_iters,
        dry_run=args.dry_run,
        verbose=args.verbose,
        project_root=args.project_root.resolve(),
        stories_dir=args.stories_dir.resolve() if args.stories_dir else None,
        tests_dir=args.tests_dir.resolve() if args.tests_dir else None,
        allow_waivers=not args.no_waivers,
    )

    if args.as_json:
        print(json.dumps(manifest, indent=2))
    else:
        summary = manifest["summary"]
        print(f"Wrote A1: {args.output}")
        print(f"  checkup pass: {summary.get('checkup_pass')}")
        print(f"  lint pass: {summary.get('lint_pass')} (exit {summary.get('lint_exit_code')})")
        print(
            f"  contract pass: {summary.get('contract_pass')} "
            f"(exit {summary.get('contract_exit_code')})"
        )
        print(
            f"  coverage pass: {summary.get('coverage_pass')} "
            f"(exit {summary.get('coverage_exit_code')})"
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
