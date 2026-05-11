"""Example usage of pdd.metadata_finalize.

Demonstrates how to call ``finalize_metadata`` to audit & finalize PDD
``.pdd/meta/`` state for a dev unit.

Inputs to ``finalize_metadata``:
- ``target`` (str): basename, prompt path, or code/example/test path
- ``language`` (Optional[str]): language identifier (e.g. ``"python"``). If
  ``None``, inferred from the target.
- ``prompts_dir`` (str): directory containing prompt files (default ``"prompts"``).
- ``context_override`` (Optional[str]): override the resolved ``.pddrc`` context.
- ``dry_run`` (bool): if True, no disk writes are performed (audit only).

Output:
- ``MetadataReport`` dataclass with: ``basename``, ``language``, ``paths``,
  ``files_present``, ``fingerprint_state`` (``missing``/``current``/``stale``),
  ``run_report_state`` (``missing``/``current``/``stale``/``skipped``),
  ``stale_components``, ``wrote_fingerprint``, ``cleared_run_report``,
  ``warnings``, and ``dry_run``.

This script runs entirely against a temporary project root and prints the
report at each stage.
"""
from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

# Make `pdd` package importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.metadata_finalize import MetadataReport, finalize_metadata


def _seed_project(root: Path) -> None:
    """Populate a minimal PDD-shaped project tree."""
    (root / "prompts").mkdir(parents=True, exist_ok=True)
    (root / "examples").mkdir(parents=True, exist_ok=True)
    (root / "tests").mkdir(parents=True, exist_ok=True)

    (root / "prompts" / "demo_python.prompt").write_text(
        "% demo prompt for metadata_finalize example\n"
    )
    (root / "demo.py").write_text("def hello():\n    return 'hello'\n")
    (root / "examples" / "demo_example.py").write_text(
        "from demo import hello\nprint(hello())\n"
    )
    (root / "tests" / "test_demo.py").write_text(
        "from demo import hello\n\n\ndef test_hello():\n    assert hello() == 'hello'\n"
    )


def _print_report(label: str, report: MetadataReport) -> None:
    print(f"--- {label} ---")
    print(f"basename            = {report.basename}")
    print(f"language            = {report.language}")
    print(f"files_present       = {report.files_present}")
    print(f"fingerprint_state   = {report.fingerprint_state}")
    print(f"run_report_state    = {report.run_report_state}")
    print(f"stale_components    = {report.stale_components}")
    print(f"wrote_fingerprint   = {report.wrote_fingerprint}")
    print(f"cleared_run_report  = {report.cleared_run_report}")
    print(f"warnings            = {report.warnings}")
    print(f"dry_run             = {report.dry_run}")
    print()


def main() -> int:
    original_cwd = Path.cwd()
    with tempfile.TemporaryDirectory(prefix="pdd_metafin_example_") as tmpdir:
        root = Path(tmpdir)
        _seed_project(root)
        os.chdir(root)
        try:
            # 1. Initial dry-run audit. No fingerprint yet => "missing".
            report = finalize_metadata("demo", language="python", dry_run=True)
            _print_report("dry-run, no fingerprint yet", report)
            assert isinstance(report, MetadataReport)
            assert report.fingerprint_state == "missing"
            assert report.run_report_state == "missing"
            assert report.wrote_fingerprint is False
            assert report.cleared_run_report is False
            assert report.dry_run is True

            # 2. Real run: write a fresh fingerprint.
            report = finalize_metadata("demo", language="python", dry_run=False)
            _print_report("write fingerprint", report)
            assert report.wrote_fingerprint is True
            # After writing, fingerprint exists; a second audit should report "current".

            # 3. Audit again (dry-run); fingerprint should now be current.
            report = finalize_metadata("demo", language="python", dry_run=True)
            _print_report("dry-run after write", report)
            assert report.fingerprint_state == "current"
            assert report.stale_components == []

            # 4. Mutate the code file -> fingerprint becomes stale.
            (root / "demo.py").write_text("def hello():\n    return 'goodbye'\n")
            report = finalize_metadata("demo", language="python", dry_run=True)
            _print_report("dry-run after code change", report)
            assert report.fingerprint_state == "stale"
            assert "code" in report.stale_components

            # 5. Resolve via a prompt-path target (language inferred from filename).
            report = finalize_metadata("prompts/demo_python.prompt", dry_run=True)
            _print_report("prompt-path target, inferred language", report)
            assert report.basename == "demo"
            assert report.language == "python"

            print("Example completed successfully.")
            return 0
        finally:
            os.chdir(original_cwd)


if __name__ == "__main__":
    raise SystemExit(main())
