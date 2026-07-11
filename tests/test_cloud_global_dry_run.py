"""Regression coverage for the bounded global sync dry-run report."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner

from pdd import cli
from pdd.continuous_sync import SyncUnit, classify_unit


def test_global_dry_run_json_discovers_absolute_configured_prompt_root_once(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Configured absolute prompt roots are report roots, not glob patterns."""
    project = tmp_path / "project"
    prompts = project / "shared-prompts"
    project.mkdir()
    prompts.mkdir()
    (prompts / "alpha_python.prompt").write_text("alpha\n", encoding="utf-8")
    (prompts / "beta_python.prompt").write_text("beta\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        f"      prompts_dir: {prompts}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)
    before = sorted(path.relative_to(project) for path in project.rglob("*"))

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["total"] == 2
    assert {unit["basename"] for unit in report["units"]} == {"alpha", "beta"}
    assert sorted(path.relative_to(project) for path in project.rglob("*")) == before


def test_global_dry_run_json_rejects_parent_relative_prompt_root(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Candidate configs cannot escape to a parent workspace with relative paths."""
    workspace = tmp_path / "workspace"
    project = workspace / "project"
    sibling = workspace / "sibling-secret"
    project.mkdir(parents=True)
    sibling.mkdir()
    (sibling / "secret_python.prompt").write_text("secret\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        "      prompts_dir: ..\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["failures"] == 1
    assert report["failures"][0]["failure"] == "unsafe_prompt_root"
    assert all(unit.get("basename") != "secret" for unit in report["units"])


def test_global_dry_run_json_rejects_sibling_relative_prompt_root(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Candidate configs cannot point discovery at a sibling checkout."""
    workspace = tmp_path / "workspace"
    project = workspace / "project"
    sibling = workspace / "sibling"
    project.mkdir(parents=True)
    sibling.mkdir()
    (sibling / "secret_python.prompt").write_text("secret\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        "      prompts_dir: ../sibling\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["failures"] == 1
    assert report["failures"][0]["failure"] == "unsafe_prompt_root"
    assert all(unit.get("basename") != "secret" for unit in report["units"])


def test_global_dry_run_json_rejects_unsafe_absolute_prompt_root(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Candidate configs cannot make dry-run traverse arbitrary absolute trees."""
    project = tmp_path / "workspace" / "project"
    outside = tmp_path / "outside"
    project.mkdir(parents=True)
    outside.mkdir()
    (outside / "secret_python.prompt").write_text("secret\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        f"      prompts_dir: {outside}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["failures"] == 1
    assert report["summary"]["total"] == 1
    assert report["failures"][0]["failure"] == "unsafe_prompt_root"
    assert "outside project" in report["failures"][0]["reason"]


def test_global_dry_run_json_rejects_absolute_workspace_parent_prompt_root(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """An absolute parent workspace is not a trusted prompt root."""
    workspace = tmp_path / "workspace"
    project = workspace / "project"
    sibling = workspace / "sibling"
    project.mkdir(parents=True)
    sibling.mkdir()
    (sibling / "secret_python.prompt").write_text("secret\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        f"      prompts_dir: {workspace}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["failures"] == 1
    assert report["failures"][0]["failure"] == "unsafe_prompt_root"
    assert all(unit.get("basename") != "secret" for unit in report["units"])


def test_global_dry_run_json_reports_prompt_traversal_budget(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Large configured prompt trees fail closed instead of hanging discovery."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    for index in range(3):
        (prompts / f"unit{index}_python.prompt").write_text(
            f"unit {index}\n",
            encoding="utf-8",
        )
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        "      prompts_dir: prompts\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.MAX_PROMPT_DISCOVERY_FILES", 2)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["failures"] == 1
    assert report["failures"][0]["failure"] == "prompt_traversal_budget"


def test_global_dry_run_json_reports_directory_entry_traversal_budget(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Traversal budget counts directory entries, not only matching prompt files."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    for index in range(4):
        (prompts / f"file{index}.txt").write_text("not a prompt\n", encoding="utf-8")
    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.MAX_PROMPT_DISCOVERY_ENTRIES", 3)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    report = json.loads(result.output)
    assert report["summary"]["failures"] == 1
    assert report["failures"][0]["failure"] == "prompt_traversal_budget"


def test_missing_fingerprint_does_not_mask_path_resolution_failure(
    tmp_path: Path,
) -> None:
    """Path failures remain distinct even when no legacy fingerprint exists."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "broken_python.prompt"
    prompt.write_text("broken\n", encoding="utf-8")
    unit = SyncUnit("broken", "python", prompt, prompts)

    with patch(
        "pdd.continuous_sync._resolve_report_paths",
        side_effect=ValueError("ambiguous module configuration"),
    ):
        report = classify_unit(unit, project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "path_resolution"
    assert "ambiguous module configuration" in report["reason"]


def test_classify_unit_does_not_remove_concurrent_empty_directories(
    tmp_path: Path,
) -> None:
    """Read-only classification must not clean up directories it did not create."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    unit = SyncUnit("widget", "python", prompt, prompts)

    def create_concurrent_dir(*_args, **_kwargs):
        (project / "concurrent-empty").mkdir()
        raise ValueError("ambiguous module configuration")

    with patch(
        "pdd.continuous_sync._resolve_report_paths",
        side_effect=create_concurrent_dir,
    ):
        report = classify_unit(unit, project)

    assert report["failure"] == "path_resolution"
    assert (project / "concurrent-empty").is_dir()
