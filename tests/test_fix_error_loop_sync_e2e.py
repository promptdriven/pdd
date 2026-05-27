"""Issue #1237 integration tests for the agentic sync dry-run flow.

These tests exercise the user-facing path that failed before the prompt
self-include was added: GitHub issue sync detects a changed prompt from git,
runs dry-run validation, and then performs strict prompt-contract preflight.
External GitHub and child process calls are mocked so the integration point
under test stays deterministic.
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
from pathlib import Path

from pdd.agentic_sync import run_agentic_sync

REPO_ROOT = Path(__file__).resolve().parent.parent
PROMPT_PATH = REPO_ROOT / "pdd" / "prompts" / "fix_error_loop_python.prompt"
MODULE_PATH = REPO_ROOT / "pdd" / "fix_error_loop.py"
ISSUE_URL = "https://github.com/promptdriven/pdd/issues/1237"


def _git(repo: Path, *args: str) -> None:
    subprocess.run(
        ["git", *args],
        cwd=repo,
        capture_output=True,
        text=True,
        check=True,
    )


def _seed_changed_fix_error_loop_project(
    tmp_path: Path,
    *,
    remove_self_include: bool = False,
) -> Path:
    repo = tmp_path / "repo"
    (repo / "prompts").mkdir(parents=True)
    (repo / "pdd").mkdir()

    shutil.copy(MODULE_PATH, repo / "pdd" / "fix_error_loop.py")
    prompt_path = repo / "prompts" / "fix_error_loop_python.prompt"
    shutil.copy(PROMPT_PATH, prompt_path)

    architecture = [
        {
            "filename": "fix_error_loop_python.prompt",
            "filepath": "pdd/fix_error_loop.py",
            "dependencies": ["failure_classification_python.prompt"],
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {
                            "name": "cloud_fix_errors",
                            "signature": "(...)",
                            "returns": "tuple",
                        },
                        {
                            "name": "fix_error_loop",
                            "signature": "(...)",
                            "returns": "tuple",
                        },
                    ]
                },
            },
        }
    ]
    (repo / "architecture.json").write_text(
        json.dumps(architecture),
        encoding="utf-8",
    )

    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "seed")
    _git(repo, "switch", "-q", "-c", "change/issue-1237")

    prompt_text = prompt_path.read_text(encoding="utf-8")
    if remove_self_include:
        prompt_text = re.sub(
            r"<include[^>]*>pdd/fix_error_loop\.py</include>\s*",
            "",
            prompt_text,
        )
    else:
        prompt_text += "\n<!-- issue-1237 prompt-only change -->\n"
    prompt_path.write_text(prompt_text, encoding="utf-8")
    _git(repo, "add", "prompts/fix_error_loop_python.prompt")
    _git(repo, "commit", "-q", "-m", "change prompt")

    return repo


def _fake_issue_response(args: list[str]) -> tuple[bool, str]:
    assert args == ["api", "repos/promptdriven/pdd/issues/1237"]
    return (
        True,
        json.dumps(
            {
                "title": "Fix fix_error_loop prompt-contract preflight before sync",
                "body": "Prompt-only change for fix_error_loop.",
                "comments_url": "",
            }
        ),
    )


def test_agentic_issue_dry_run_reaches_sync_stage_with_self_include(
    tmp_path: Path,
    monkeypatch,
    mocker,
) -> None:
    repo = _seed_changed_fix_error_loop_project(tmp_path)
    monkeypatch.chdir(repo)

    mocker.patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    mocker.patch("pdd.agentic_sync._run_gh_command", side_effect=_fake_issue_response)
    mocker.patch("pdd.agentic_sync._run_single_dry_run", return_value=(True, ""))
    mocker.patch("pdd.agentic_sync.run_agentic_task", side_effect=AssertionError)
    mocker.patch(
        "pdd.agentic_sync._filter_already_synced",
        side_effect=lambda modules, module_cwds, quiet=False: modules,
    )

    success, message, cost, model = run_agentic_sync(
        ISSUE_URL,
        quiet=True,
        dry_run=True,
        use_github_state=False,
    )

    assert success is True
    assert message == "Dry run complete: 1 module(s) would sync: fix_error_loop"
    assert cost == 0.0
    assert model == ""


def test_agentic_issue_dry_run_reports_contract_error_without_self_include(
    tmp_path: Path,
    monkeypatch,
    mocker,
) -> None:
    repo = _seed_changed_fix_error_loop_project(
        tmp_path,
        remove_self_include=True,
    )
    monkeypatch.chdir(repo)

    mocker.patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    mocker.patch("pdd.agentic_sync._run_gh_command", side_effect=_fake_issue_response)
    mocker.patch("pdd.agentic_sync._run_single_dry_run", return_value=(True, ""))
    mocker.patch("pdd.agentic_sync.run_agentic_task", side_effect=AssertionError)
    filter_synced = mocker.patch("pdd.agentic_sync._filter_already_synced")

    success, message, cost, model = run_agentic_sync(
        ISSUE_URL,
        quiet=True,
        dry_run=True,
        use_github_state=False,
    )

    assert success is False
    assert message.startswith("Dry-run validation failed:")
    assert "fix_error_loop: prompt contract preflight failed:" in message
    assert "missing cloud_fix_errors, fix_error_loop" in message
    assert cost == 0.0
    assert model == ""
    filter_synced.assert_not_called()
