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


def test_prompt_ownership_uses_path_patterns_to_break_root_prompt_ties(
    tmp_path: Path,
) -> None:
    """Canonical pdd/prompts ownership must not depend on context order."""
    root = tmp_path / "repo"
    (root / "pdd" / "prompts" / "core").mkdir(parents=True)
    (root / "pdd" / "prompts" / "commands").mkdir(parents=True)
    (root / "prompts").symlink_to("pdd/prompts", target_is_directory=True)
    pddrc = root / ".pddrc"
    pddrc.write_text("contexts: {}\n", encoding="utf-8")
    contexts = {
        "utils": {
            "paths": ["utils/**"],
            "defaults": {"prompts_dir": "prompts"},
        },
        "core": {
            "paths": ["pdd/core/**", "prompts/core/**"],
            "defaults": {"prompts_dir": "prompts"},
        },
        "commands": {
            "paths": ["pdd/commands/**", "prompts/commands/**"],
            "defaults": {"prompts_dir": "prompts"},
        },
        "pdd_cli": {
            "paths": ["pdd/**", "prompts/**", "tests/**"],
            "defaults": {"prompts_dir": "prompts"},
        },
    }
    cache = {pddrc: {"contexts": contexts}}

    def owner(relative: str) -> str | None:
        prompt = root / "pdd" / "prompts" / relative
        prompt.parent.mkdir(parents=True, exist_ok=True)
        prompt.write_text("% prompt\n", encoding="utf-8")
        stem = prompt.stem.rsplit("_", 1)[0]
        _basename, context_name, _config_path, _root = continuous_sync._prompt_ownership(
            prompt, stem, root / "prompts", root, cache
        )
        return context_name

    assert owner("story_detection_result_python.prompt") == "pdd_cli"
    assert owner("core/cli_python.prompt") == "core"
    assert owner("commands/analysis_python.prompt") == "commands"


def test_prompt_context_specificity_preserves_utils_mcp_pattern(tmp_path: Path) -> None:
    """A utility subtree still beats the broad pdd CLI pattern."""
    root = tmp_path / "repo"
    prompt = root / "utils" / "mcp" / "prompts" / "runner_python.prompt"
    prompt.parent.mkdir(parents=True)
    utils = {"paths": ["utils/**"], "defaults": {"prompts_dir": "prompts"}}
    pdd_cli = {
        "paths": ["pdd/**", "prompts/**"],
        "defaults": {"prompts_dir": "prompts"},
    }
    assert continuous_sync._context_path_specificity(prompt, utils, root) > (
        continuous_sync._context_path_specificity(prompt, pdd_cli, root)
    )
