"""Tests for ``pdd checkup simplify``."""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner

from pdd.checkup_file_selection import discover_simplify_targets
from pdd.checkup_simplify import run_checkup_simplify
from pdd.commands.checkup import checkup


def _init_git_repo(root: Path) -> None:
    subprocess.run(["git", "init"], cwd=root, check=True, capture_output=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=root,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"],
        cwd=root,
        check=True,
        capture_output=True,
    )


def test_discover_simplify_targets_since_ref(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    src = tmp_path / "pdd"
    src.mkdir()
    target = src / "widget.py"
    target.write_text("def run():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "pdd/widget.py"], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "add widget"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    target.write_text("def run():\n    return 2\n", encoding="utf-8")

    _, files = discover_simplify_targets(since="HEAD", cwd=tmp_path, max_files=10)
    rel = [f.name for f in files]
    assert "widget.py" in rel


def test_discover_simplify_targets_staged(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "staged.py"
    module.parent.mkdir(parents=True)
    module.write_text("x = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "pdd/staged.py"], cwd=tmp_path, check=True, capture_output=True)

    _, files = discover_simplify_targets(staged=True, cwd=tmp_path, max_files=10)
    assert any(f.name == "staged.py" for f in files)


def test_discover_since_and_staged_mutually_exclusive(tmp_path: Path) -> None:
    import pytest

    with pytest.raises(ValueError, match="mutually exclusive"):
        discover_simplify_targets(since="HEAD~1", staged=True, cwd=tmp_path)


def test_run_simplify_dry_run_no_file_writes(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "sample.py"
    module.parent.mkdir(parents=True)
    original = "def value():\n    return 42\n"
    module.write_text(original, encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )

    report = {
        "kind": "pdd.checkup.simplify",
        "files_analyzed": ["pdd/sample.py"],
        "suggestions": [{"path": "pdd/sample.py", "items": ["inline redundant return"]}],
        "summary": "1 suggestion",
    }
    agent_output = (
        f"SIMPLIFY_REPORT_JSON: {json.dumps(report)}\n"
        "FILES_MODIFIED: none\n"
    )

    monkeypatch.chdir(tmp_path)

    with patch("pdd.checkup_simplify.get_available_agents", return_value=["claude"]):
        with patch("pdd.checkup_simplify.run_agentic_task", return_value=(True, agent_output, 0.1, "claude")):
            result = run_checkup_simplify(
                path=module,
                mode="dry-run",
                since=None,
                staged=False,
                max_files=5,
                evidence=True,
                verify=False,
                no_format=False,
                quiet=True,
                verbose=False,
                reasoning_time=None,
            )

    assert module.read_text(encoding="utf-8") == original
    assert result.files_modified == []
    assert result.suggestions_count == 1
    assert result.evidence_path is not None
    payload = json.loads(result.evidence_path.read_text(encoding="utf-8"))
    assert payload["kind"] == "pdd.checkup.simplify"
    assert payload["mode"] == "dry-run"


def test_checkup_cli_dispatches_simplify(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "cli_sample.py"
    module.parent.mkdir(parents=True)
    module.write_text("def ok():\n    return True\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    monkeypatch.chdir(tmp_path)

    report = {
        "kind": "pdd.checkup.simplify",
        "files_analyzed": ["pdd/cli_sample.py"],
        "suggestions": [],
        "summary": "clean",
    }
    agent_output = f"SIMPLIFY_REPORT_JSON: {json.dumps(report)}\nFILES_MODIFIED: none\n"

    with patch("pdd.checkup_simplify.get_available_agents", return_value=["claude"]):
        with patch("pdd.checkup_simplify.run_agentic_task", return_value=(True, agent_output, 0.0, "claude")):
            result = CliRunner().invoke(
                checkup,
                ["simplify", str(module), "--evidence"],
                obj={"quiet": False, "verbose": False},
            )

    assert result.exit_code == 0
    assert "PDD Checkup: simplify" in result.output
    evidence_dir = tmp_path / ".pdd" / "evidence" / "checkups"
    assert list(evidence_dir.glob("simplify-*.json"))


def test_apply_and_verify_flags(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "apply_me.py"
    module.parent.mkdir(parents=True)
    module.write_text("def before():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    monkeypatch.chdir(tmp_path)

    report = {
        "kind": "pdd.checkup.simplify",
        "files_analyzed": ["pdd/apply_me.py"],
        "suggestions": [{"path": "pdd/apply_me.py", "items": ["simplified"]}],
        "summary": "applied",
    }
    agent_output = (
        f"SIMPLIFY_REPORT_JSON: {json.dumps(report)}\n"
        "FILES_MODIFIED: pdd/apply_me.py\n"
    )

    verify_calls: list[str] = []

    def fake_verify(**kwargs):
        verify_calls.append("ran")
        return {"format": "passed", "lint": "passed", "tests": "passed"}

    with patch("pdd.checkup_simplify.get_available_agents", return_value=["claude"]):
        with patch("pdd.checkup_simplify.run_agentic_task", return_value=(True, agent_output, 0.2, "claude")):
            with patch("pdd.checkup_simplify._run_verification", side_effect=fake_verify):
                result = run_checkup_simplify(
                    path=module,
                    mode="apply",
                    since=None,
                    staged=False,
                    max_files=5,
                    evidence=False,
                    verify=True,
                    no_format=True,
                    quiet=True,
                    verbose=False,
                    reasoning_time=None,
                )

    assert verify_calls == ["ran"]
    assert "pdd/apply_me.py" in result.files_modified
