"""Regression tests for the Cloud Batch source upload allowlist."""

from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SUBMIT_SCRIPT = REPO_ROOT / "ci" / "cloud-batch" / "submit.sh"


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
    """All tracked files make the allowlist-omission class impossible."""
    submit_text = SUBMIT_SCRIPT.read_text(encoding="utf-8")
    assert "SOURCE_PATHS" not in submit_text

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
    """Source construction is from exact HEAD rather than selected paths."""
    source_identity_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "source-identity.py"
    ).read_text(encoding="utf-8")
    assert "*paths" not in source_identity_text
    assert 'add_argument("--path"' not in source_identity_text


def test_cloud_batch_source_archive_disables_macos_metadata_for_every_write() -> None:
    """Exact-HEAD archive construction must be deterministic and host-clean."""
    submit_text = SUBMIT_SCRIPT.read_text(encoding="utf-8")
    source_identity_text = (
        REPO_ROOT / "ci" / "cloud-batch" / "source-identity.py"
    ).read_text(encoding="utf-8")

    assert "source-identity.py\" archive" in submit_text
    assert '"ls-tree",' in source_identity_text
    assert '"cat-file", "--batch"' in source_identity_text
    assert "gzip.GzipFile" in source_identity_text
    assert "mtime=0" in source_identity_text
    assert "PARENT_PDDRC" not in submit_text
    assert "ls-files --cached --others" not in submit_text
