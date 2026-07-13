"""Regression tests for the Cloud Batch source upload allowlist."""

from __future__ import annotations

import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SUBMIT_SCRIPT = REPO_ROOT / "ci" / "cloud-batch" / "submit.sh"


def _run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )


def _cloud_batch_source_paths() -> list[str]:
    result = _run(
        "bash",
        "-c",
        (
            "source <(sed -n '/^SOURCE_PATHS=(/,/^)/p' "
            "'ci/cloud-batch/submit.sh'); "
            'printf "%s\\n" "${SOURCE_PATHS[@]}"'
        ),
    )
    return [line for line in result.stdout.splitlines() if line]


def _expected_demo_files() -> list[Path]:
    demo = REPO_ROOT / "demos" / "checkup_interactive"
    return [
        demo / "README.md",
        demo / "FULL_WORKFLOW.md",
        demo / "run_demo.sh",
        demo / "prompts" / "01_clean_task.prompt",
        demo / "prompts" / "02_vague_clarification.prompt",
        demo / "prompts" / "03_formatting_edge_case.prompt",
        demo / "prompts" / "04_contract_sensitive.prompt",
        demo / "prompts" / "05_coverage_sensitive.prompt",
        demo / "prompts" / "06_snapshot_candidate.prompt",
        demo / "prompts" / "07_drift_candidate.prompt",
        demo / "drift_workspace" / "prompts" / "drift_candidate_python.prompt",
        demo / "drift_workspace" / "src" / "drift_candidate.py",
    ]


def test_cloud_batch_source_upload_includes_checkup_interactive_demo() -> None:
    """The uploaded source tarball must include demo fixtures used by tests."""
    source_paths = _cloud_batch_source_paths()
    assert "demos" in source_paths

    missing = [
        str(path.relative_to(REPO_ROOT))
        for path in _expected_demo_files()
        if not path.is_file()
    ]
    assert not missing, (
        "cloud-batch source upload must include checkup interactive "
        f"demo fixtures; missing: {missing}"
    )


def test_cloud_batch_source_upload_includes_repository_ignore_contract() -> None:
    """The synthetic worker checkout must retain generated-file exclusions."""
    assert ".gitignore" in _cloud_batch_source_paths()


def test_cloud_batch_source_archive_disables_macos_metadata_for_every_write() -> None:
    """Every tar write must suppress AppleDouble metadata on macOS."""
    submit_text = SUBMIT_SCRIPT.read_text(encoding="utf-8")

    assert "_source_tar()" in submit_text
    assert "COPYFILE_DISABLE=1 COPY_EXTENDED_ATTRIBUTES_DISABLE=1 tar \"$@\"" in (
        submit_text
    )
    assert submit_text.count("_source_tar ") == 3
    assert not any(
        line.strip().startswith("tar ")
        and (" -cf " in f" {line} " or " -rf " in f" {line} ")
        for line in submit_text.splitlines()
    )
