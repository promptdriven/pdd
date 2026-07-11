"""Regression coverage for the bounded global sync dry-run report."""

from __future__ import annotations

import json
from pathlib import Path

from click.testing import CliRunner

from pdd import cli


def test_global_dry_run_json_discovers_absolute_configured_prompt_root_once(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Configured absolute prompt roots are report roots, not glob patterns."""
    project = tmp_path / "project"
    prompts = tmp_path / "shared-prompts"
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
