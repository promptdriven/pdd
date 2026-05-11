"""Example usage of pdd.commands.metadata.

Demonstrates the `pdd metadata finalize` CLI command, which is a thin shim
over ``pdd.metadata_finalize.finalize_metadata``.

Inputs (CLI options for `metadata finalize`):
- TARGET (str): a basename, a prompt path, or a code/example/test path.
- --dry-run (flag): print state without writing.
- --json (flag): emit a single JSON object to stdout.
- --language TEXT: override language detection.
- --context TEXT: override .pddrc context selection.
- --quiet (flag): suppress non-error output in human-readable mode.

Exit codes:
- 0: report produced (and in normal mode, fingerprint written).
- 1: --dry-run only; drift detected.
- 2: error (resolution, lock, or unexpected).

Output (human-readable): header, resolved paths, fingerprint and run_report
states, write status lines (in normal mode), trailing warnings.

Output (--json): a single JSON object matching the MetadataReport schema.

This script runs entirely against a temporary project root and uses Click's
``CliRunner`` so it is self-contained — no real filesystem state outside of
the temporary directory is modified.
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path

# Make `pdd` package importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".."))

from click.testing import CliRunner

from pdd.commands.metadata import metadata_group


def _seed_project(root: Path) -> None:
    """Populate a minimal PDD-shaped project tree under ``root``."""
    (root / "prompts").mkdir(parents=True, exist_ok=True)
    (root / "examples").mkdir(parents=True, exist_ok=True)
    (root / "tests").mkdir(parents=True, exist_ok=True)

    (root / "prompts" / "demo_python.prompt").write_text(
        "% demo prompt for pdd metadata finalize example\n"
    )
    (root / "demo.py").write_text("def hello():\n    return 'hello'\n")
    (root / "examples" / "demo_example.py").write_text(
        "from demo import hello\nprint(hello())\n"
    )
    (root / "tests" / "test_demo.py").write_text(
        "from demo import hello\n\n\ndef test_hello():\n    assert hello() == 'hello'\n"
    )


def _run(runner: CliRunner, *args: str) -> "object":
    """Invoke the metadata CLI group with the given args, returning the Click Result."""
    return runner.invoke(metadata_group, list(args))


def main() -> int:
    original_cwd = Path.cwd()
    runner = CliRunner()
    with tempfile.TemporaryDirectory(prefix="pdd_metadata_cmd_example_") as tmpdir:
        root = Path(tmpdir)
        _seed_project(root)
        os.chdir(root)
        try:
            print("--- 1. Dry-run before any fingerprint exists ---")
            print("Expected: drift detected => Click Result exit_code == 1.")
            result = _run(runner, "finalize", "demo", "--dry-run", "--language", "python")
            print(result.output)
            print(f"exit_code = {result.exit_code}")
            assert result.exit_code == 1, f"expected 1 for drift in dry-run, got {result.exit_code}"
            print()

            print("--- 2. Normal run: writes fingerprint ---")
            print("Expected: 'wrote fingerprint' in output, exit_code == 0.")
            result = _run(runner, "finalize", "demo", "--language", "python")
            print(result.output)
            print(f"exit_code = {result.exit_code}")
            assert result.exit_code == 0
            assert "wrote fingerprint" in result.output
            print()

            print("--- 3. Dry-run again: fingerprint is now current ---")
            print("Expected: 'fingerprint: current', exit_code == 0.")
            result = _run(runner, "finalize", "demo", "--dry-run", "--language", "python")
            print(result.output)
            print(f"exit_code = {result.exit_code}")
            assert result.exit_code == 0
            assert "fingerprint: current" in result.output
            print()

            print("--- 4. JSON output mode ---")
            print("Expected: stdout is a single JSON object with MetadataReport fields.")
            result = _run(runner, "finalize", "demo", "--dry-run", "--language", "python", "--json")
            print(result.output)
            payload = json.loads(result.output)
            assert payload["basename"] == "demo"
            assert payload["language"] == "python"
            assert payload["fingerprint_state"] == "current"
            print(f"parsed JSON keys: {sorted(payload.keys())}")
            print()

            print("--- 5. Quiet flag suppresses non-error output (non-JSON mode) ---")
            result = _run(runner, "finalize", "demo", "--dry-run", "--language", "python", "--quiet")
            print(f"output (should be empty): {result.output!r}")
            print(f"exit_code = {result.exit_code}")
            assert result.output == ""
            print()

            print("--- 6. Drift after editing the code file (dry-run) ---")
            (root / "demo.py").write_text("def hello():\n    return 'goodbye'\n")
            result = _run(runner, "finalize", "demo", "--dry-run", "--language", "python")
            print(result.output)
            print(f"exit_code = {result.exit_code}")
            assert result.exit_code == 1
            assert "fingerprint: stale" in result.output
            print()

            print("--- 7. Error path: unresolvable target ---")
            print("Expected: exit_code == 2, 'error:' on stderr (mix_stderr=True by default).")
            # An empty target triggers the ValueError branch inside finalize_metadata.
            result = _run(runner, "finalize", "")
            print(result.output)
            print(f"exit_code = {result.exit_code}")
            assert result.exit_code == 2
            print()

            print("Example completed successfully.")
            return 0
        finally:
            os.chdir(original_cwd)


if __name__ == "__main__":
    raise SystemExit(main())
