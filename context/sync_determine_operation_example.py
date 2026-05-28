"""
sync_determine_operation_example.py
-----------------------------------

Demonstrates how `pdd.sync_determine_operation.sync_determine_operation`
chooses the next PDD operation based on file state, fingerprint metadata,
and run reports.

Run from any working directory:

    python context/sync_determine_operation_example.py

The example builds a sandboxed temp directory so it never touches your real
project state and is unaffected by any ancestor `.pddrc` file.
"""

import hashlib
import json
import os
import shutil
import sys
import tempfile
from datetime import datetime
from pathlib import Path

# Make the local `pdd` package importable regardless of where this script is run.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.sync_determine_operation import (  # noqa: E402
    Fingerprint,
    RunReport,
    SyncDecision,
    estimate_operation_cost,
    read_fingerprint,
    read_run_report,
    sync_determine_operation,
)


def _create_file(path: Path, content: str) -> str:
    """Write `content` to `path` and return its SHA256 hex digest."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def _write_fingerprint(meta_dir: Path, basename: str, language: str, fp: Fingerprint) -> None:
    meta_dir.mkdir(parents=True, exist_ok=True)
    (meta_dir / f"{basename}_{language.lower()}.json").write_text(
        json.dumps(fp.__dict__), encoding="utf-8"
    )


def _write_run_report(meta_dir: Path, basename: str, language: str, rr: RunReport) -> None:
    meta_dir.mkdir(parents=True, exist_ok=True)
    (meta_dir / f"{basename}_{language.lower()}_run.json").write_text(
        json.dumps(rr.__dict__), encoding="utf-8"
    )


def _print_decision(label: str, decision: SyncDecision) -> None:
    print(f"  Operation : {decision.operation}")
    print(f"  Reason    : {decision.reason}")
    print(f"  Confidence: {decision.confidence:.2f}")
    print(f"  Est. cost : ${decision.estimated_cost:.2f}")
    print()


def main() -> int:
    basename = "calculator"
    language = "python"
    target_coverage = 80.0

    original_cwd = Path.cwd()
    sandbox = Path(tempfile.mkdtemp(prefix="pdd_sync_example_"))
    os.chdir(sandbox)
    try:
        prompts_dir = sandbox / "prompts"
        meta_dir = sandbox / ".pdd" / "meta"
        prompt_path = prompts_dir / f"{basename}_{language}.prompt"
        code_path = sandbox / f"{basename}.py"
        example_path = sandbox / f"{basename}_example.py"
        test_path = sandbox / f"test_{basename}.py"

        print(f"Sandbox        : {sandbox}")
        print(f"Module under   : pdd.sync_determine_operation")
        print(f"Target coverage: {target_coverage:.1f}%")
        print()

        # ----------------------------------------------------------------------
        # Scenario 1 — Brand-new prompt, no history.
        # Expected operation: 'generate' (no <include>, so no auto-deps).
        # ----------------------------------------------------------------------
        print("Scenario 1 — New prompt, no fingerprint")
        _create_file(prompt_path, "Implement an add(a, b) function.\n")
        decision = sync_determine_operation(
            basename,
            language,
            target_coverage=target_coverage,
            log_mode=True,
        )
        _print_decision("scenario_1", decision)

        # ----------------------------------------------------------------------
        # Scenario 2 — Fingerprint exists, tests failed.
        # Expected operation: 'fix' (test file exists, failures detected).
        # ----------------------------------------------------------------------
        print("Scenario 2 — Run report shows test failures")
        prompt_hash = _create_file(prompt_path, "Implement an add(a, b) function.\n")
        code_hash = _create_file(code_path, "def add(a, b):\n    return a + b\n")
        example_hash = _create_file(example_path, "from calculator import add\nprint(add(2, 2))\n")
        test_hash = _create_file(
            test_path,
            "from calculator import add\n\ndef test_add():\n    assert add(2, 2) == 5  # intentionally wrong\n",
        )
        _write_fingerprint(
            meta_dir,
            basename,
            language,
            Fingerprint(
                pdd_version="0.1.0",
                timestamp=datetime.utcnow().isoformat(),
                command="test",
                prompt_hash=prompt_hash,
                code_hash=code_hash,
                example_hash=example_hash,
                test_hash=test_hash,
            ),
        )
        _write_run_report(
            meta_dir,
            basename,
            language,
            RunReport(
                timestamp=datetime.utcnow().isoformat(),
                exit_code=1,
                tests_passed=0,
                tests_failed=1,
                coverage=42.0,
                test_hash=test_hash,
            ),
        )
        decision = sync_determine_operation(
            basename,
            language,
            target_coverage=target_coverage,
            log_mode=True,
        )
        _print_decision("scenario_2", decision)

        # ----------------------------------------------------------------------
        # Scenario 3 — Prompt was edited; derived files unchanged.
        # Expected operation: 'generate' (prompt change takes priority).
        # ----------------------------------------------------------------------
        print("Scenario 3 — Prompt edited after fingerprint")
        new_prompt_hash = _create_file(
            prompt_path,
            "Implement an add(a, b) function AND a subtract(a, b) function.\n",
        )
        # Re-use existing fingerprint but with the OLD prompt hash so the change is detected.
        # The current run_report (failing) would normally trigger 'fix', but the spec says
        # prompt changes take priority over runtime signals.
        decision = sync_determine_operation(
            basename,
            language,
            target_coverage=target_coverage,
            log_mode=True,
        )
        _print_decision("scenario_3", decision)
        assert new_prompt_hash  # silence linter

        # ----------------------------------------------------------------------
        # Scenario 4 — Everything in sync, tests pass with full coverage.
        # Expected operation: 'nothing' (workflow complete).
        # ----------------------------------------------------------------------
        print("Scenario 4 — Fully synced unit")
        # Re-write prompt to original content so its hash matches the fingerprint
        synced_prompt_hash = _create_file(prompt_path, "Implement an add(a, b) function.\n")
        synced_code_hash = _create_file(code_path, "def add(a, b):\n    return a + b\n")
        synced_example_hash = _create_file(
            example_path, "from calculator import add\nprint(add(2, 2))\n"
        )
        synced_test_hash = _create_file(
            test_path,
            "from calculator import add\n\ndef test_add():\n    assert add(2, 2) == 4\n",
        )
        _write_fingerprint(
            meta_dir,
            basename,
            language,
            Fingerprint(
                pdd_version="0.1.0",
                timestamp=datetime.utcnow().isoformat(),
                command="fix",
                prompt_hash=synced_prompt_hash,
                code_hash=synced_code_hash,
                example_hash=synced_example_hash,
                test_hash=synced_test_hash,
            ),
        )
        _write_run_report(
            meta_dir,
            basename,
            language,
            RunReport(
                timestamp=datetime.utcnow().isoformat(),
                exit_code=0,
                tests_passed=1,
                tests_failed=0,
                coverage=95.0,
                test_hash=synced_test_hash,
            ),
        )
        decision = sync_determine_operation(
            basename,
            language,
            target_coverage=target_coverage,
            log_mode=True,
        )
        _print_decision("scenario_4", decision)

        # ----------------------------------------------------------------------
        # Bonus — read_fingerprint / read_run_report now accept project_root
        # (Issue #1252 Gap 1). Show that anchoring on a project root finds the
        # subproject's `.pdd/meta` even when CWD is elsewhere.
        # ----------------------------------------------------------------------
        print("Bonus — read_fingerprint with explicit project_root")
        fp = read_fingerprint(basename, language, project_root=sandbox)
        rr = read_run_report(basename, language, project_root=sandbox)
        print(f"  Fingerprint command: {fp.command if fp else None}")
        print(f"  Run report exit_code: {rr.exit_code if rr else None}")
        print()

        # ----------------------------------------------------------------------
        # Cost estimation helper
        # ----------------------------------------------------------------------
        print("Operation cost estimates (USD):")
        for op in ("auto-deps", "generate", "example", "verify", "test", "fix", "update"):
            print(f"  {op:<10s} ${estimate_operation_cost(op):.2f}")

        return 0
    finally:
        os.chdir(original_cwd)
        shutil.rmtree(sandbox, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
