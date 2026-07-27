"""Regression coverage for the bounded global sync dry-run report."""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner
import pytest

from pdd import cli
from pdd.continuous_sync import SyncUnit, _find_matching_artifact, classify_unit
from pdd.sync_determine_operation import (
    _architecture_artifact_paths,
    calculate_current_hashes,
    calculate_prompt_hash,
    get_pdd_file_paths,
)


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


def test_prompt_traversal_stops_scandir_at_entry_budget(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """A single wide directory is consumed only through allowance plus one."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    for index in range(8):
        (prompts / f"file{index}.txt").write_text("noise\n", encoding="utf-8")
    real_scandir = __import__("os").scandir
    yielded = 0

    def observing_scandir(path):
        iterator = real_scandir(path)

        class Observed:
            def __enter__(self):
                return self

            def __exit__(self, *_args):
                iterator.close()

            def __iter__(self):
                return self

            def __next__(self):
                nonlocal yielded
                entry = next(iterator)
                yielded += 1
                return entry

        return Observed()

    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.os.scandir", observing_scandir)
    monkeypatch.setattr("pdd.continuous_sync.MAX_PROMPT_DISCOVERY_ENTRIES", 3)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert json.loads(result.output)["failures"][0]["failure"] == "prompt_traversal_budget"
    assert yielded == 4


def test_metadata_traversal_stops_scandir_at_entry_budget(
    tmp_path: Path, monkeypatch,
) -> None:
    """Metadata enumeration consumes only the remaining allowance plus one."""
    project = tmp_path / "project"
    meta = project / ".pdd" / "meta"
    meta.mkdir(parents=True)
    for index in range(8):
        (meta / f"unit{index}_python.json").write_text("{}", encoding="utf-8")
    real_scandir = __import__("os").scandir
    yielded = 0

    def observing_scandir(path):
        nonlocal yielded
        iterator = real_scandir(path)

        class Observed:
            def __enter__(self):
                return self

            def __exit__(self, *_args):
                iterator.close()

            def __iter__(self):
                return self

            def __next__(self):
                nonlocal yielded
                entry = next(iterator)
                if Path(path) == meta:
                    yielded += 1
                return entry

        return Observed()

    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.os.scandir", observing_scandir)
    monkeypatch.setattr("pdd.continuous_sync.MAX_PROMPT_DISCOVERY_ENTRIES", 3)

    result = CliRunner().invoke(
        cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert json.loads(result.output)["failures"][0]["failure"] == "discovery_budget"
    assert yielded == 4


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


@pytest.mark.parametrize(
    "output_key",
    ["generate_output_path", "example_output_path", "test_output_path"],
)
def test_missing_fingerprint_does_not_mask_unsafe_legacy_artifact(
    tmp_path: Path,
    output_key: str,
) -> None:
    """Every resolved legacy artifact is validated before fingerprint branching."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: ['**']\n    defaults:\n"
        "      prompts_dir: prompts\n"
        f"      {output_key}: ../outside\n",
        encoding="utf-8",
    )

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "unsafe_artifacts"
    assert "resolves outside project" in report["reason"]


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


def test_repair_traversal_stops_scandir_at_entry_budget(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Repair does not materialize a wide directory before enforcing its cap."""
    project = tmp_path / "project"
    project.mkdir()
    for index in range(8):
        (project / f"entry-{index}.txt").write_text("noise\n", encoding="utf-8")
    real_scandir = __import__("os").scandir
    yielded = 0

    def observing_scandir(path):
        iterator = real_scandir(path)

        class Observed:
            def __enter__(self):
                return self

            def __exit__(self, *_args):
                iterator.close()

            def __iter__(self):
                return self

            def __next__(self):
                nonlocal yielded
                entry = next(iterator)
                yielded += 1
                return entry

        return Observed()

    monkeypatch.setattr("pdd.continuous_sync.os.scandir", observing_scandir)
    monkeypatch.setattr("pdd.continuous_sync.MAX_REPAIR_DISCOVERY_ENTRIES", 3)

    _match, failure = _find_matching_artifact(project, "widget.py", "stored")

    assert failure is not None
    assert failure.failure == "repair_traversal_budget"
    assert yielded == 4


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


def test_default_context_templates_preserve_nested_basename(tmp_path: Path) -> None:
    """Read-only reports use the same default/template semantics as sync."""
    project = tmp_path / "project"
    prompts = project / "prompts" / "core"
    prompts.mkdir(parents=True)
    prompt = prompts / "cloud_python.prompt"
    code = project / "src" / "cloud.py"
    example = project / "usage" / "cloud_demo.py"
    test_file = project / "spec" / "cloud_spec.py"
    for path, content in ((prompt, "cloud\n"), (code, "VALUE = 1\n"),
                          (example, "print('cloud')\n"),
                          (test_file, "def test_cloud(): pass\n")):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: ['**']\n    defaults:\n"
        "      outputs:\n"
        "        code: {path: 'src/{name}.py'}\n"
        "        example: {path: 'usage/{name}_demo.py'}\n"
        "        test: {path: 'spec/{name}_spec.py'}\n",
        encoding="utf-8",
    )
    paths = {"prompt": prompt, "code": code, "example": example,
             "test": test_file, "test_files": [test_file]}
    _write_fingerprint(project, "core_cloud", calculate_current_hashes(paths))

    report = classify_unit(SyncUnit("core/cloud", "python", prompt, prompts), project)

    assert report["classification"] == "IN_SYNC"
    assert report["paths"]["code"] == "src/cloud.py"
    assert report["paths"]["example"] == "usage/cloud_demo.py"
    assert report["paths"]["test"] == "spec/cloud_spec.py"


def test_report_and_live_resolver_share_leaf_name_semantics(tmp_path: Path, monkeypatch) -> None:
    project = tmp_path / "project"
    prompt = project / "prompts" / "core" / "cloud_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("cloud\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: ['**']\n    defaults:\n"
        "      outputs:\n        code: {path: 'src/{name}.py'}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    report = classify_unit(SyncUnit("core/cloud", "python", prompt, project / "prompts"), project)
    live = get_pdd_file_paths("core/cloud", "python", "prompts")

    assert report["paths"]["code"] == "src/cloud.py"
    assert live["code"] == Path("src/cloud.py")


def test_live_flat_basename_uses_discovered_nested_prompt_context(tmp_path: Path, monkeypatch) -> None:
    project = tmp_path / "project"
    prompt = project / "prompts" / "frontend" / "app" / "page_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("page\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: ['**']\n    defaults:\n"
        "      outputs:\n        code: {path: 'src/{category}/{name}.py'}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)

    live = get_pdd_file_paths("page", "python", "prompts")

    assert live["code"] == Path("src/frontend/app/page.py")


@pytest.mark.parametrize("malformed", ["contexts: []\n", "contexts:\n  local:\n    defaults: []\n", "contexts:\n  local:\n    defaults:\n      prompts_dir: []\n"])
def test_nested_malformed_config_fails_closed(tmp_path: Path, monkeypatch, malformed: str) -> None:
    project = tmp_path / "project"
    prompt = project / "prompts" / "nested" / "widget_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("widget\n", encoding="utf-8")
    (prompt.parent / ".pddrc").write_text(malformed, encoding="utf-8")
    monkeypatch.chdir(project)

    result = CliRunner().invoke(cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"], catch_exceptions=False)
    report = json.loads(result.output)

    assert report["failures"][0]["failure"] == "invalid_pddrc"


def test_metadata_inference_is_bounded_and_validates_before_stat(tmp_path: Path, monkeypatch) -> None:
    project = tmp_path / "project"
    meta = project / ".pdd" / "meta"
    meta.mkdir(parents=True)
    safe_name = "_".join("x" for _ in range(40))
    (meta / f"{safe_name}_python.json").write_text("{}", encoding="utf-8")
    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.MAX_METADATA_INFERENCE_CANDIDATES", 3, raising=False)
    calls = []

    def guarded_exists(path: Path, _base: Path) -> bool:
        calls.append(path)
        assert path.resolve(strict=False).is_relative_to(project.resolve())
        return False

    with patch("pdd.continuous_sync._validated_artifact_exists", side_effect=guarded_exists, create=True):
        result = CliRunner().invoke(cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"], catch_exceptions=False)

    assert result.exit_code == 0
    assert len(calls) <= 12


@pytest.mark.parametrize("target_exists", [True, False])
def test_metadata_symlink_is_rejected_without_target_stat(tmp_path: Path, monkeypatch, target_exists: bool) -> None:
    project = tmp_path / "project"
    (project / ".pdd").mkdir(parents=True)
    target = tmp_path / "outside-meta"
    if target_exists:
        target.mkdir()
    try:
        (project / ".pdd" / "meta").symlink_to(target, target_is_directory=True)
    except OSError as exc:
        pytest.skip(f"symlink creation unavailable: {exc}")
    monkeypatch.chdir(project)
    meta_root = project / ".pdd" / "meta"
    real_exists = Path.exists

    def guarded_exists(path: Path) -> bool:
        assert path != meta_root, "metadata exists() followed the symlink before lstat validation"
        return real_exists(path)

    with patch.object(Path, "exists", guarded_exists):
        result = CliRunner().invoke(cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"], catch_exceptions=False)
    report = json.loads(result.output)

    assert report["failures"][0]["failure"] == "unsafe_metadata"


def test_architecture_duplicate_leaves_match_relative_prompt_path(tmp_path: Path) -> None:
    """Architecture selection distinguishes path-qualified duplicate leaves."""
    project = tmp_path / "project"
    prompts = project / "prompts" / "app" / "settings"
    prompts.mkdir(parents=True)
    prompt = prompts / "page_typescriptreact.prompt"
    prompt.write_text("page\n", encoding="utf-8")
    code = project / "src" / "app" / "settings" / "page.tsx"
    code.parent.mkdir(parents=True)
    code.write_text("export default 1\n", encoding="utf-8")
    (project / "architecture.json").write_text(json.dumps([
        {"filename": "app/login/page_typescriptreact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "app/settings/page_typescriptreact.prompt", "filepath": "src/app/settings/page.tsx"},
    ]), encoding="utf-8")
    _write_fingerprint(project, "app_settings_page", {
        "prompt_hash": hashlib.sha256(prompt.read_bytes()).hexdigest(),
        "code_hash": hashlib.sha256(code.read_bytes()).hexdigest(),
        "example_hash": None, "test_hash": None, "test_files": None,
        "include_deps": {},
    })
    (project / ".pdd" / "meta" / "app_settings_page_python.json").rename(
        project / ".pdd" / "meta" / "app_settings_page_typescriptreact.json"
    )

    report = classify_unit(
        SyncUnit("app/settings/page", "typescriptreact", prompt, project / "prompts"),
        project,
    )

    assert report["classification"] == "IN_SYNC"
    assert report["paths"]["code"] == "src/app/settings/page.tsx"


def test_nested_architecture_report_matches_all_live_artifact_paths(
    tmp_path: Path, monkeypatch,
) -> None:
    """Nested architecture ownership applies to every derived artifact."""
    project = tmp_path / "project"
    owner = project / "packages" / "store"
    prompts = owner / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "cart_typescriptreact.prompt"
    prompt.write_text("cart\n", encoding="utf-8")
    (owner / "architecture.json").write_text(json.dumps([
        {"filename": "cart_typescriptreact.prompt", "filepath": "src/pages/cart.tsx"},
    ]), encoding="utf-8")
    monkeypatch.chdir(project)

    live = get_pdd_file_paths("cart", "typescriptreact", str(prompts))
    report = classify_unit(
        SyncUnit("cart", "typescriptreact", prompt, prompts), project
    )["paths"]

    for key in ("code", "example", "test"):
        assert report[key] == live[key].relative_to(project).as_posix()
    assert report["test_files"] == [
        path.relative_to(project).as_posix() for path in live["test_files"]
    ]


def test_global_dry_run_json_rejects_symlinked_pddrc_before_read(
    tmp_path: Path, monkeypatch,
) -> None:
    """Candidate config links are rejected before their targets are opened."""
    project = tmp_path / "project"
    project.mkdir()
    outside = tmp_path / "outside.yml"
    outside.write_text("contexts: {}\n", encoding="utf-8")
    try:
        (project / ".pddrc").symlink_to(outside)
    except OSError as exc:
        pytest.skip(f"symlink creation unavailable: {exc}")
    monkeypatch.chdir(project)

    result = CliRunner().invoke(
        cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    report = json.loads(result.output)
    assert report["failures"][0]["failure"] == "unsafe_config"


def test_global_discovery_budget_is_shared_across_nested_roots(
    tmp_path: Path, monkeypatch,
) -> None:
    """Nested configured roots cannot multiply the traversal allowance."""
    project = tmp_path / "project"
    nested = project / "prompts" / "nested"
    nested.mkdir(parents=True)
    (nested / "unit_python.prompt").write_text("unit\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  outer: {defaults: {prompts_dir: prompts}}\n"
        "  inner: {defaults: {prompts_dir: prompts/nested}}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.MAX_PROMPT_DISCOVERY_ENTRIES", 4)

    result = CliRunner().invoke(
        cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    report = json.loads(result.output)
    assert report["summary"]["total"] == 1
    assert report["failures"] == []


def test_malformed_architecture_output_is_unit_scoped_json_failure(
    tmp_path: Path, monkeypatch,
) -> None:
    """Malformed artifact paths cannot abort the machine-readable report."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    (project / "architecture.json").write_text(json.dumps([
        {"filename": prompt.name, "filepath": "bad\u0000path.py"},
    ]), encoding="utf-8")
    _write_fingerprint(project, "widget", {
        "prompt_hash": "stored", "code_hash": "stored", "example_hash": None,
        "test_hash": None, "test_files": None, "include_deps": {},
    })
    monkeypatch.chdir(project)

    result = CliRunner().invoke(
        cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    report = json.loads(result.output)
    assert report["units"][0]["classification"] == "FAILURE"
    assert report["units"][0]["failure"] in {"path_resolution", "unsafe_artifacts"}


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
    dependency = prompts / "shared.txt"
    prompt.write_text("<include>shared.txt</include>\nwidget\n", encoding="utf-8")
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


def test_live_include_is_validated_once_before_dependency_read(
    tmp_path: Path,
) -> None:
    """Hash and dependency-map generation share one validated include resolution."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    outside = tmp_path / "secret.txt"
    outside.write_text("secret\n", encoding="utf-8")
    prompt = prompts / "widget_python.prompt"
    prompt.write_text(f"<include>{outside}</include>\nwidget\n", encoding="utf-8")
    _write_fingerprint(project, "widget", {"prompt_hash": "stored", "code_hash": None, "example_hash": None, "test_hash": None, "test_files": None, "include_deps": {}})
    original_read_bytes = Path.read_bytes
    outside_reads = 0

    def observing_read_bytes(path: Path) -> bytes:
        nonlocal outside_reads
        if path == outside:
            outside_reads += 1
        return original_read_bytes(path)

    with patch.object(Path, "read_bytes", observing_read_bytes):
        report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["failure"] == "hash_calculation"
    assert outside_reads == 0


def test_unresolved_live_include_preserves_v1_skip_without_ancestor_read(
    tmp_path: Path,
) -> None:
    """Safe report resolution preserves v1 missing-dependency semantics."""
    project = tmp_path / "workspace" / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    ancestor = project.parent / "ancestor-only.txt"
    ancestor.write_text("outside\n", encoding="utf-8")
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("<include>ancestor-only.txt</include>\n", encoding="utf-8")
    reads = 0
    original = Path.read_bytes

    def observing(path: Path) -> bytes:
        nonlocal reads
        if path == ancestor:
            reads += 1
        return original(path)

    with patch.object(Path, "read_bytes", observing):
        hashes = calculate_current_hashes({"prompt": prompt}, dependency_root=project)

    assert hashes["prompt_hash"] == hashlib.sha256(prompt.read_bytes()).hexdigest()
    assert reads == 0


def test_validated_v1_hash_preserves_declared_alias_multiplicity(tmp_path: Path) -> None:
    """v1 deduplicates declared strings, not their resolved path aliases."""
    project = tmp_path / "project"
    project.mkdir()
    dependency = project / "dep.txt"
    dependency.write_text("dependency\n", encoding="utf-8")
    prompt = project / "widget_python.prompt"
    prompt.write_text(
        "<include>dep.txt</include>\n<include>./dep.txt</include>\n",
        encoding="utf-8",
    )

    legacy = calculate_prompt_hash(prompt, dependency_root=project, hash_version=1)
    validated = calculate_current_hashes(
        {"prompt": prompt}, dependency_root=project
    )["prompt_hash"]

    assert validated == legacy


def test_report_caches_config_ownership_and_caps_contexts(
    tmp_path: Path, monkeypatch,
) -> None:
    """One config is parsed once and context ownership has a hard command cap."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    for name in ("alpha", "beta"):
        (prompts / f"{name}_python.prompt").write_text(name, encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    defaults:\n      prompts_dir: prompts\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)
    from pdd import continuous_sync
    original = continuous_sync._load_pddrc_config
    loads = 0

    def observing(path):
        nonlocal loads
        loads += 1
        return original(path)

    monkeypatch.setattr(continuous_sync, "_load_pddrc_config", observing)
    first = CliRunner().invoke(
        cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )
    assert json.loads(first.output)["summary"]["total"] == 2
    assert loads == 1

    monkeypatch.setattr(continuous_sync, "MAX_CONFIG_CONTEXTS", 1, raising=False)
    (project / ".pddrc").write_text(
        "contexts:\n  one: {defaults: {prompts_dir: prompts}}\n"
        "  two: {defaults: {prompts_dir: prompts}}\n",
        encoding="utf-8",
    )
    second = CliRunner().invoke(
        cli.cli, ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )
    assert json.loads(second.output)["failures"][0]["failure"] == "invalid_pddrc"


def test_metadata_only_report_reuses_parsed_config(
    tmp_path: Path, monkeypatch,
) -> None:
    """Metadata inference and classification share the report config cache."""
    project = tmp_path / "project"
    meta = project / ".pdd" / "meta"
    meta.mkdir(parents=True)
    for name in ("alpha", "beta"):
        (meta / f"{name}_python.json").write_text("{}", encoding="utf-8")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    defaults:\n      prompts_dir: prompts\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)
    from pdd import continuous_sync
    original = continuous_sync._load_pddrc_config
    loads = 0

    def observing(path):
        nonlocal loads
        loads += 1
        return original(path)

    monkeypatch.setattr(continuous_sync, "_load_pddrc_config", observing)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert json.loads(result.output)["summary"]["total"] == 2
    assert loads == 1


def test_duplicate_prompt_roots_cannot_bypass_context_cap_without_prompts(
    tmp_path: Path, monkeypatch,
) -> None:
    """Context validation runs before duplicate prompt roots are collapsed."""
    project = tmp_path / "project"
    project.mkdir()
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  one: {defaults: {prompts_dir: prompts}}\n"
        "  two: {defaults: {prompts_dir: prompts}}\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(project)
    monkeypatch.setattr("pdd.continuous_sync.MAX_CONFIG_CONTEXTS", 1)

    result = CliRunner().invoke(
        cli.cli,
        ["--no-core-dump", "sync", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert json.loads(result.output)["failures"][0]["failure"] == "invalid_pddrc"


def test_architecture_artifact_construction_performs_no_discovery(
    tmp_path: Path,
) -> None:
    """Architecture path construction is pure until report validation."""
    project = tmp_path / "project"

    with patch.object(Path, "exists", side_effect=AssertionError("exists called")), \
         patch.object(Path, "glob", side_effect=AssertionError("glob called")):
        paths = _architecture_artifact_paths(
            project, Path("src/widget.py"), "widget", "py"
        )

    assert paths["test_files"] == [project / "tests" / "test_widget.py"]


def test_architecture_test_output_is_validated_before_discovery(
    tmp_path: Path, monkeypatch,
) -> None:
    """Outside architecture test directories are rejected before scandir."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    (project / "architecture.json").write_text(
        json.dumps([{"filename": prompt.name, "filepath": "src/widget.py"}]),
        encoding="utf-8",
    )
    outside = tmp_path / "outside-tests"
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    defaults:\n"
        "      prompts_dir: prompts\n"
        f"      test_output_path: {outside}\n",
        encoding="utf-8",
    )
    original_scandir = __import__("os").scandir

    def guarded_scandir(path):
        assert Path(path) != outside
        return original_scandir(path)

    monkeypatch.setattr("pdd.continuous_sync.os.scandir", guarded_scandir)

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "unsafe_artifacts"


def test_symlinked_architecture_test_output_is_validated_before_discovery(
    tmp_path: Path, monkeypatch,
) -> None:
    """Symlink-directed architecture test directories are never enumerated."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    prompts.mkdir(parents=True)
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    (project / "architecture.json").write_text(
        json.dumps([{"filename": prompt.name, "filepath": "src/widget.py"}]),
        encoding="utf-8",
    )
    outside = tmp_path / "outside-tests"
    outside.mkdir()
    linked = project / "linked-tests"
    try:
        linked.symlink_to(outside, target_is_directory=True)
    except OSError as exc:
        pytest.skip(f"symlink creation unavailable: {exc}")
    (project / ".pddrc").write_text(
        "contexts:\n  default:\n    defaults:\n"
        "      prompts_dir: prompts\n"
        "      test_output_path: linked-tests\n",
        encoding="utf-8",
    )
    original_scandir = __import__("os").scandir

    def guarded_scandir(path):
        assert Path(path) != linked
        return original_scandir(path)

    monkeypatch.setattr("pdd.continuous_sync.os.scandir", guarded_scandir)

    report = classify_unit(SyncUnit("widget", "python", prompt, prompts), project)

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "unsafe_artifacts"


def test_architecture_test_discovery_uses_shared_budget(
    tmp_path: Path, monkeypatch,
) -> None:
    """Wide architecture test directories stop at the command budget."""
    project = tmp_path / "project"
    prompts = project / "prompts"
    tests = project / "tests"
    prompts.mkdir(parents=True)
    tests.mkdir()
    prompt = prompts / "widget_python.prompt"
    prompt.write_text("widget\n", encoding="utf-8")
    (project / "architecture.json").write_text(
        json.dumps([{"filename": prompt.name, "filepath": "src/widget.py"}]),
        encoding="utf-8",
    )
    for index in range(4):
        (tests / f"test_widget_{index}.py").write_text("pass\n", encoding="utf-8")
    monkeypatch.setattr("pdd.continuous_sync.MAX_REPAIR_DISCOVERY_ENTRIES", 2)
    budget = {"repair_entries": 0}

    report = classify_unit(
        SyncUnit("widget", "python", prompt, prompts), project, budget
    )

    assert report["classification"] == "FAILURE"
    assert report["failure"] == "path_resolution"
    assert budget["report_entries"] == 3


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
    prompt.write_text(f"<include>{reference}</include>\nwidget\n", encoding="utf-8")
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
