"""Path-policy regressions for legacy continuous-sync metadata repair."""

from pathlib import Path

import pytest

from pdd import continuous_sync


def test_artifact_path_violation_rejects_resolved_project_escape(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    outside = tmp_path / "outside.py"
    outside.write_text("def value():\n    return 1\n", encoding="utf-8")

    assert (
        continuous_sync._artifact_path_violation(root / "../outside.py", root)
        == "resolves outside project"
    )


def test_repair_search_skips_symlink_candidate_without_hashing(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    archive = root / "archive"
    archive.mkdir()
    outside = tmp_path / "widget.py"
    outside.write_text("def value():\n    return 1\n", encoding="utf-8")
    try:
        (archive / "widget.py").symlink_to(outside)
    except OSError as exc:  # pragma: no cover - platform permission guard
        pytest.skip(f"symlink creation unavailable: {exc}")

    def fail_if_hashed(path: Path) -> str:
        raise AssertionError(f"unexpected hash read: {path}")

    monkeypatch.setattr(continuous_sync, "calculate_sha256", fail_if_hashed)

    match, failure = continuous_sync._find_matching_artifact(root, "widget.py", "unused")
    assert match is None
    assert failure is None


def test_prompt_ownership_ignores_contexts_without_explicit_prompts_dir(
    tmp_path: Path,
) -> None:
    root = tmp_path / "repo"
    prompt_root = root / "prompts"
    prompt_root.mkdir(parents=True)
    prompt = prompt_root / "agentic_checkup_python.prompt"
    prompt.write_text("contract", encoding="utf-8")
    config_path = root / ".pddrc"
    config_path.write_text("version: '1.0'\n", encoding="utf-8")
    config = {
        "contexts": {
            "utils": {"defaults": {"test_output_path": "tests/utils"}},
            "pdd_cli": {"defaults": {"prompts_dir": "prompts"}},
        }
    }

    basename, context_name, owner, owned_root = continuous_sync._prompt_ownership(
        prompt,
        "agentic_checkup",
        prompt_root,
        root,
        {config_path: config},
    )

    assert basename == "agentic_checkup"
    assert context_name == "pdd_cli"
    assert owner == config_path
    assert owned_root == prompt_root
