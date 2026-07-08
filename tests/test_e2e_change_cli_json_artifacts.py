"""CLI-level regression coverage for `pdd change` JSON step artifacts.

These tests invoke the real Click command and the real agentic change
orchestrator. The agent provider is mocked, and the mock writes the same
JSON artifacts a real agent is expected to write.
"""

import json
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import MagicMock, patch

from click.testing import CliRunner

from pdd import cli as cli_module


ISSUE_URL = "https://github.com/owner/repo/issues/1871"
ISSUE_NUMBER = 1871


def _write_artifact(cwd: Path, filename: str, payload: dict) -> None:
    artifacts_dir = cwd / ".pdd" / "change" / f"issue-{ISSUE_NUMBER}"
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    (artifacts_dir / filename).write_text(json.dumps(payload), encoding="utf-8")


def _write_report(cwd: Path, stem: str, body: str) -> None:
    artifacts_dir = cwd / ".pdd" / "change" / f"issue-{ISSUE_NUMBER}"
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    (artifacts_dir / f"{stem}.md").write_text(body, encoding="utf-8")


def test_pdd_change_cli_uses_json_artifacts_for_step9_and_step11_control_flow(tmp_path):
    """The actual `pdd change` CLI should trust JSON artifacts over prose.

    This reproduces the user-visible bug class from #1850 at the command
    boundary:
    - Step 9 does not emit a legacy FILES_MODIFIED marker, but does write
      09_implement.json. The CLI should still continue and report the file.
    - Step 11 prose says issues were found, but 11_review.json says clean.
      The CLI should skip Step 12 and create the PR.

    On the pre-JSON implementation, this scenario either stops at Step 9 or
    follows the contradictory Step 11 prose into Step 12.
    """
    repo_dir = tmp_path / "repo"
    repo_dir.mkdir()
    (repo_dir / "prompts").mkdir()
    (repo_dir / "architecture.json").write_text("[]", encoding="utf-8")

    seen_labels = []

    def fake_gh_command(args):
        if args[:2] == ["api", "repos/owner/repo/issues/1871"]:
            return (
                True,
                json.dumps(
                    {
                        "title": "Make pdd change structured",
                        "body": "Step decisions should come from JSON artifacts.",
                        "user": {"login": "issue-author"},
                        "comments_url": "https://api.github.com/comments",
                        "updated_at": "2026-07-07T00:00:00Z",
                    }
                ),
            )
        if args[:2] == ["api", "https://api.github.com/comments"]:
            return True, "[]"
        return True, "{}"

    def fake_agentic_task(**kwargs):
        label = kwargs["label"]
        cwd = Path(kwargs["cwd"])
        seen_labels.append(label)

        if label == "step1":
            _write_artifact(cwd, "01_duplicate.json", {"status": "proceed", "duplicates": [], "questions": []})
            _write_report(cwd, "01_duplicate", "No duplicate issue found.")
        elif label == "step2":
            _write_artifact(cwd, "02_docs.json", {"status": "proceed"})
            _write_report(cwd, "02_docs", "Not already implemented.")
        elif label == "step4":
            _write_artifact(cwd, "04_clarify.json", {"status": "proceed", "questions": []})
            _write_report(cwd, "04_clarify", "Requirements are clear.")
        elif label == "step6":
            _write_artifact(cwd, "06_devunits.json", {"status": "proceed", "direct_edit_candidates": []})
            _write_report(cwd, "06_devunits", "Prompt-backed dev unit found.")
        elif label == "step7":
            _write_artifact(cwd, "07_architecture.json", {"status": "proceed", "questions": []})
            _write_report(cwd, "07_architecture", "No architecture decision needed.")
        elif label == "step9":
            prompt_path = cwd / "prompts" / "structured_change_python.prompt"
            prompt_path.write_text("structured change prompt", encoding="utf-8")
            _write_artifact(
                cwd,
                "09_implement.json",
                {
                    "status": "changed",
                    "files_modified": ["prompts/structured_change_python.prompt"],
                    "files_created": [],
                    "direct_edits": [],
                    "manual_review": [],
                },
            )
            _write_report(cwd, "09_implement", "Implemented the prompt change.")
            return True, "Implementation complete without legacy file markers.", 0.1, "mock-model"
        elif label == "step10":
            _write_artifact(
                cwd,
                "10_architecture_update.json",
                {
                    "architecture_files_modified": [],
                    "associated_docs_modified": [],
                    "associated_docs_conflicts": [],
                    "associated_docs_unchanged": [],
                },
            )
            _write_report(cwd, "10_architecture_update", "No architecture updates needed.")
        elif label == "step11_iter1":
            _write_artifact(cwd, "11_review.json", {"status": "clean", "manual_review": []})
            _write_report(cwd, "11_review", "Review is clean.")
            return True, "ISSUES FOUND: prose-only parser would run Step 12.", 0.1, "mock-model"
        elif label.startswith("step12"):
            raise AssertionError("Step 12 should be skipped when 11_review.json status is clean")
        elif label == "step13":
            _write_artifact(
                cwd,
                "13_create_pr.json",
                {
                    "status": "pr_created",
                    "pr_url": "https://github.com/owner/repo/pull/1871",
                },
            )
            _write_report(cwd, "13_create_pr", "PR created.")
            return True, "PR creation completed without a prose URL.", 0.1, "mock-model"

        return True, f"Output for {label}", 0.1, "mock-model"

    completed = MagicMock(stdout="", returncode=0, stderr="")

    patchers = [
        patch("pdd.agentic_change._check_gh_cli", return_value=True),
        patch("pdd.agentic_change._run_gh_command", side_effect=fake_gh_command),
        patch("pdd.agentic_change._setup_repository", return_value=repo_dir),
        patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None),
        patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_change_orchestrator.clear_workflow_state", return_value=None),
        patch("pdd.agentic_change_orchestrator.ensure_issue_steer_cursor_seeded", return_value=False),
        patch("pdd.agentic_change_orchestrator.drain_step_steers", return_value=[]),
        patch("pdd.agentic_change_orchestrator.post_step_comment", return_value=True),
        patch("pdd.agentic_change_orchestrator.post_step_comment_once", return_value=True),
        patch("pdd.agentic_change_orchestrator._setup_worktree", return_value=(repo_dir, None)),
        patch("pdd.agentic_change_orchestrator._preflight_drift_heal", return_value=([], [], [])),
        patch("pdd.agentic_change_orchestrator.discover_associated_documents", return_value=[]),
        patch("pdd.agentic_change_orchestrator.register_untracked_prompts", return_value={"registered": []}),
        patch("pdd.agentic_change_orchestrator.run_pre_checkup_gate", return_value=(True, "ok", 0.0)),
        patch(
            "pdd.agentic_change_orchestrator._generate_user_story_artifacts_for_change",
            return_value=([], "None", 0.0, "", None),
        ),
        patch("pdd.agentic_change_orchestrator._get_git_root", return_value=repo_dir),
        patch("pdd.agentic_change_orchestrator._resolve_main_ref_name", return_value="main"),
        patch("pdd.agentic_change_orchestrator.current_worktree_branch", return_value="change/issue-1871"),
        patch("pdd.agentic_change_orchestrator._pr_url_matches_current_head", return_value=True),
        patch("pdd.agentic_change_orchestrator.subprocess.run", return_value=completed),
        patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=fake_agentic_task),
    ]
    with ExitStack() as stack:
        for patcher in patchers:
            stack.enter_context(patcher)
        result = CliRunner().invoke(
            cli_module.cli,
            [
                "change",
                "--no-github-state",
                "--no-prompt-checkup",
                ISSUE_URL,
            ],
            catch_exceptions=False,
        )

    assert result.exit_code == 0, result.output
    assert "step9" in seen_labels
    assert "step11_iter1" in seen_labels
    assert "step13" in seen_labels
    assert not any(label.startswith("step12") for label in seen_labels)
    assert "prompts/structured_change_python.prompt" in result.output
    assert "PR Created: https://github.com/owner/repo/pull/1871" in result.output
