"""Regression coverage for the bounded global sync dry-run report."""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner
import pytest

from pdd import cli
from pdd.continuous_sync import SyncUnit, classify_unit
from pdd.sync_determine_operation import calculate_current_hashes


def _write_fingerprint(project: Path, basename: str, hashes: dict) -> None:
    meta = project / ".pdd" / "meta"
    meta.mkdir(parents=True, exist_ok=True)
    (meta / f"{basename}_python.json").write_text(
        json.dumps(
            {
                "pdd_version": "0.0-test",
                "timestamp": "2026-07-11T00:00:00+00:00",
                "command": f"pdd sync {basename}",
                **hashes,
            }
        ),
        encoding="utf-8",
    )


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


def test_missing_prompt_repair_uses_bounded_pruned_traversal(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Stale fingerprints cannot trigger unbounded whole-project artifact search."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    meta = project / ".pdd" / "meta"
    prompts.mkdir(parents=True)
    meta.mkdir(parents=True)
    code = project / "node_modules" / "deep" / "widget.py"
    code.parent.mkdir(parents=True)
    code.write_text("value = 1\n", encoding="utf-8")
    for index in range(8):
        (project / f"entry-{index}.txt").write_text("noise\n", encoding="utf-8")
    (meta / "widget_python.json").write_text(
        json.dumps(
            {
                "pdd_version": "0.0-test",
                "timestamp": "2026-07-11T00:00:00+00:00",
                "command": "pdd sync widget",
                "prompt_hash": None,
                "code_hash": hashlib.sha256(code.read_bytes()).hexdigest(),
                "example_hash": None,
                "test_hash": None,
                "test_files": None,
                "include_deps": {},
            }
        ),
        encoding="utf-8",
    )
    unit = SyncUnit("widget", "python", prompts / "widget_python.prompt", prompts)
    monkeypatch.setattr("pdd.continuous_sync.MAX_REPAIR_DISCOVERY_ENTRIES", 3)

    report = classify_unit(unit, project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "repair_traversal_budget"
    assert "repair search exceeded traversal budget" in report["reason"]
    assert "node_modules" not in json.dumps(report["paths"])


def test_configured_outputs_without_architecture_remain_in_sync(
    tmp_path: Path,
) -> None:
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    code = project / "src" / "widget.py"
    example = project / "samples" / "widget_example.py"
    test_file = project / "checks" / "test_widget.py"
    for path, content in (
        (prompt, "widget\n"),
        (code, "value = 1\n"),
        (example, "print('widget')\n"),
        (test_file, "def test_widget(): pass\n"),
    ):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: ['**']\n    defaults:\n"
        "      prompts_dir: prompts\n      generate_output_path: src/\n"
        "      example_output_path: samples/\n      test_output_path: checks/\n",
        encoding="utf-8",
    )
    paths = {
        "prompt": prompt,
        "code": code,
        "example": example,
        "test": test_file,
        "test_files": [test_file],
    }
    _write_fingerprint(project, "widget", calculate_current_hashes(paths))

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "IN_SYNC"
    assert report["paths"]["code"] == "src/widget.py"
    assert report["paths"]["example"] == "samples/widget_example.py"
    assert report["paths"]["test"] == "checks/test_widget.py"


def test_live_include_hash_is_independent_of_nested_cwd(
    tmp_path: Path,
    monkeypatch,
) -> None:
    project = tmp_path / "project"
    prompts = project / "prompts"
    nested = project / "nested"
    prompts.mkdir(parents=True)
    nested.mkdir()
    prompt = prompts / "widget_python.prompt"
    dependency = project / "shared.txt"
    prompt.write_text('<include path="shared.txt">\nwidget\n', encoding="utf-8")
    dependency.write_text("trusted\n", encoding="utf-8")
    (nested / "shared.txt").write_text("cwd-dependent\n", encoding="utf-8")
    paths = {"prompt": prompt, "code": project / "widget.py", "example": project / "examples/widget_example.py", "test": project / "tests/test_widget.py", "test_files": [project / "tests/test_widget.py"]}
    for key in ("code", "example", "test"):
        paths[key].parent.mkdir(parents=True, exist_ok=True)
        paths[key].write_text(f"{key}\n", encoding="utf-8")
    monkeypatch.chdir(project)
    hashes = calculate_current_hashes(paths, dependency_root=project)
    _write_fingerprint(project, "widget", hashes)
    monkeypatch.chdir(nested)

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "IN_SYNC"


@pytest.mark.parametrize("include_kind", ["absolute", "symlink"])
def test_live_include_rejects_unsafe_target(
    tmp_path: Path,
    include_kind: str,
) -> None:
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    outside = tmp_path / "secret.txt"
    outside.write_text("secret\n", encoding="utf-8")
    if include_kind == "absolute":
        reference = str(outside)
    else:
        link = project / "linked.txt"
        try:
            link.symlink_to(outside)
        except OSError as exc:
            pytest.skip(f"symlink creation unavailable: {exc}")
        reference = "linked.txt"
    prompt = prompts / "widget_python.prompt"
    prompt.write_text(f'<include path="{reference}">\nwidget\n', encoding="utf-8")
    _write_fingerprint(project, "widget", {"prompt_hash": "stored", "code_hash": None, "example_hash": None, "test_hash": None, "test_files": None, "include_deps": {}})

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "hash_calculation"


def test_symlinked_architecture_is_rejected_before_read(
    tmp_path: Path,
) -> None:
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    outside = tmp_path / "architecture.json"
    outside.write_text("[]", encoding="utf-8")
    try:
        (project / "architecture.json").symlink_to(outside)
    except OSError as exc:
        pytest.skip(f"symlink creation unavailable: {exc}")

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "unsafe_architecture"


@pytest.mark.parametrize("value", ["[]", "7", "true", "'   '"])
def test_invalid_prompts_dir_value_emits_invalid_pddrc_json(
    tmp_path: Path,
    monkeypatch,
    value: str,
) -> None:
    project = tmp_path / "project"
    project.mkdir()
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    defaults:\n      prompts_dir: " + value + "\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    result = CliRunner().invoke(cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"], catch_exceptions=False)

    report = json.loads(result.output)
    assert report["failures"][0]["failure"] == "invalid_pddrc"


def test_unexpandable_prompts_dir_emits_invalid_pddrc_json(
    tmp_path: Path,
    monkeypatch,
) -> None:
    project = tmp_path / "project"
    project.mkdir()
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    defaults:\n      prompts_dir: ~pdd_user_that_does_not_exist/prompts\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    result = CliRunner().invoke(cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"], catch_exceptions=False)

    report = json.loads(result.output)
    assert report["failures"][0]["failure"] == "invalid_pddrc"


def test_malformed_string_include_path_is_unit_scoped_failure(tmp_path: Path) -> None:
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    _write_fingerprint(project, "widget", {"prompt_hash": "stored", "code_hash": None, "example_hash": None, "test_hash": None, "test_files": None, "include_deps": {"bad\u0000path": "digest"}})

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["failure"] == "unsafe_include_deps"
    assert report["unsafe_include_deps"] == [{"path": "bad\u0000path", "reason": "invalid_path"}]
