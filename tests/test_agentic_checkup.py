"""Tests for pdd.agentic_checkup module."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict
from unittest.mock import MagicMock, patch, call

import pytest

from pdd.agentic_checkup import (
    _extract_json_from_text,
    _fetch_comments,
    _fetch_pr_context,
    _load_pddrc_content,
    _post_checkup_comment,
    _post_error_comment,
    _truncate_issue_context,
    run_agentic_checkup,
)


# ---------------------------------------------------------------------------
# _extract_json_from_text
# ---------------------------------------------------------------------------

class TestExtractJsonFromText:
    def test_extracts_from_markdown_code_block(self):
        text = 'Some text\n```json\n{"success": true, "issues": []}\n```\nMore text'
        result = _extract_json_from_text(text)
        assert result is not None
        assert result["success"] is True

    def test_extracts_raw_json(self):
        text = 'Here is the result: {"success": false, "message": "found bugs"} end'
        result = _extract_json_from_text(text)
        assert result is not None
        assert result["success"] is False

    def test_returns_none_for_no_json(self):
        assert _extract_json_from_text("no json here") is None

    def test_returns_none_for_empty_string(self):
        assert _extract_json_from_text("") is None

    def test_returns_none_for_none(self):
        assert _extract_json_from_text(None) is None

    def test_returns_none_for_invalid_json(self):
        assert _extract_json_from_text("{not valid json}") is None

    def test_returns_none_for_json_array(self):
        assert _extract_json_from_text("[1, 2, 3]") is None

    def test_extracts_nested_json(self):
        text = '```json\n{"success": true, "issues": [{"severity": "critical"}]}\n```'
        result = _extract_json_from_text(text)
        assert result is not None
        assert len(result["issues"]) == 1

    def test_extracts_from_code_block_without_json_tag(self):
        text = '```\n{"success": true}\n```'
        result = _extract_json_from_text(text)
        assert result is not None
        assert result["success"] is True


# ---------------------------------------------------------------------------
# _load_pddrc_content
# ---------------------------------------------------------------------------

class TestLoadPddrcContent:
    def test_loads_existing_pddrc(self, tmp_path):
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("project_name: test\ncontexts:\n  - src/")
        result = _load_pddrc_content(tmp_path)
        assert "project_name: test" in result

    def test_returns_message_for_missing_pddrc(self, tmp_path):
        result = _load_pddrc_content(tmp_path)
        assert "No .pddrc found" in result


# ---------------------------------------------------------------------------
# _post_checkup_comment
# ---------------------------------------------------------------------------

class TestPostCheckupComment:
    @patch("pdd.agentic_checkup._run_gh_command")
    def test_posts_success_comment(self, mock_gh):
        mock_gh.return_value = (True, "")
        report = {
            "success": True,
            "message": "All checks passed",
            "tech_stack": ["Python", "TypeScript"],
            "issues": [],
            "changed_files": [],
        }
        _post_checkup_comment("owner", "repo", 1, report)

        mock_gh.assert_called_once()
        args = mock_gh.call_args[0][0]
        assert "repos/owner/repo/issues/1/comments" in args[1]
        body_arg = [a for a in args if a.startswith("body=")][0]
        assert "All checks passed" in body_arg

    @patch("pdd.agentic_checkup._run_gh_command")
    def test_posts_comment_with_issues(self, mock_gh):
        mock_gh.return_value = (True, "")
        report = {
            "success": False,
            "message": "Found 2 issues",
            "tech_stack": ["Python"],
            "issues": [
                {
                    "module": "auth",
                    "file": "src/auth.py",
                    "severity": "critical",
                    "category": "missing_dep",
                    "description": "Missing requests package",
                    "fixed": True,
                },
                {
                    "module": "api",
                    "file": "src/api.py",
                    "severity": "medium",
                    "category": "import_error",
                    "description": "Wrong import path",
                    "fixed": False,
                },
            ],
            "changed_files": ["requirements.txt", "src/auth.py"],
        }
        _post_checkup_comment("owner", "repo", 42, report)

        mock_gh.assert_called_once()
        args = mock_gh.call_args[0][0]
        body_arg = [a for a in args if a.startswith("body=")][0]
        assert "Missing requests package" in body_arg
        assert "requirements.txt" in body_arg


# ---------------------------------------------------------------------------
# _post_error_comment
# ---------------------------------------------------------------------------

class TestPostErrorComment:
    @patch("pdd.agentic_checkup._run_gh_command")
    def test_posts_error_comment(self, mock_gh):
        mock_gh.return_value = (True, "")
        _post_error_comment("owner", "repo", 5, "Something went wrong")

        mock_gh.assert_called_once()
        args = mock_gh.call_args[0][0]
        body_arg = [a for a in args if a.startswith("body=")][0]
        assert "Something went wrong" in body_arg
        assert "Error" in body_arg

    @patch("pdd.agentic_checkup._run_gh_command")
    def test_truncates_long_message(self, mock_gh):
        mock_gh.return_value = (True, "")
        long_msg = "x" * 2000
        _post_error_comment("owner", "repo", 1, long_msg)

        args = mock_gh.call_args[0][0]
        body_arg = [a for a in args if a.startswith("body=")][0]
        # Message should be truncated to 1000 chars
        assert len(body_arg) < 2000


# ---------------------------------------------------------------------------
# _fetch_comments
# ---------------------------------------------------------------------------

class TestFetchComments:
    @patch("pdd.agentic_checkup._run_gh_command")
    def test_fetches_and_formats_comments(self, mock_gh):
        comments = [
            {
                "user": {"login": "alice"},
                "created_at": "2026-04-29T00:00:00Z",
                "body": "Comment 1",
            },
            {"user": {"login": "bob"}, "body": "Comment 2"},
        ]
        mock_gh.return_value = (True, json.dumps(comments))

        result = _fetch_comments("https://api.github.com/repos/o/r/issues/1/comments")
        assert "alice" in result
        assert "2026-04-29T00:00:00Z" in result
        assert "Comment 1" in result
        assert "bob" in result

    @patch("pdd.agentic_checkup._run_gh_command")
    def test_returns_empty_on_failure(self, mock_gh):
        mock_gh.return_value = (False, "404")
        result = _fetch_comments("https://api.github.com/repos/o/r/issues/1/comments")
        assert result == ""


class TestIssueContextTruncation:
    def test_preserves_latest_comments_when_issue_context_is_long(self):
        old_body = "OLD PRD/Tier2 requirement.\n" * 200
        old_comments = "--- Comment by bot ---\nold bot log\n" * 200
        latest = (
            "--- Comment by maintainer at 2026-04-29T00:00:00Z ---\n"
            "Implementation scope lock: Tier 1 only. PRD/Tier2 is out of scope.\n"
        )
        text = f"Title: T\nDescription:\n{old_body}\nComments:\n{old_comments}{latest}"

        result = _truncate_issue_context(text, 3000)

        assert len(result) <= 3000
        assert "Title: T" in result
        assert "Implementation scope lock" in result
        assert "PRD/Tier2 is out of scope" in result
        assert "latest comments preserved" in result


class TestFetchPrContext:
    @patch("pdd.agentic_checkup._run_gh_command")
    def test_fetches_pr_body_files_comments_and_reviews(self, mock_gh):
        mock_gh.side_effect = [
            (
                True,
                json.dumps(
                    {
                        "title": "Improve catalog",
                        "body": "Uses reviewed manifest instead of live fetch.",
                        "state": "open",
                        "mergeable_state": "clean",
                        "head": {"label": "o:feature"},
                        "base": {"label": "o:main"},
                    }
                ),
            ),
            (
                True,
                json.dumps(
                    [
                        {
                            "filename": "pdd/data/arena_elo_manifest.json",
                            "status": "modified",
                            "additions": 5,
                            "deletions": 1,
                            "patch": "@@ source data provenance",
                        }
                    ]
                ),
            ),
            (
                True,
                json.dumps(
                    [
                        {
                            "user": {"login": "maintainer"},
                            "created_at": "2026-04-29T00:00:00Z",
                            "body": "Direction changed for safety.",
                        }
                    ]
                ),
            ),
            (
                True,
                json.dumps(
                    [
                        {
                            "user": {"login": "reviewer"},
                            "submitted_at": "2026-04-29T01:00:00Z",
                            "state": "COMMENTED",
                            "body": "Check variant provenance.",
                        }
                    ]
                ),
            ),
        ]

        context = _fetch_pr_context("o", "r", 1309)

        assert "Title: Improve catalog" in context
        assert "Uses reviewed manifest" in context
        assert "pdd/data/arena_elo_manifest.json" in context
        assert "Direction changed for safety." in context
        assert "Check variant provenance." in context


# ---------------------------------------------------------------------------
# run_agentic_checkup
# ---------------------------------------------------------------------------

class TestRunAgenticCheckup:
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=False)
    def test_fails_without_gh_cli(self, mock_gh):
        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1", quiet=True
        )
        assert not success
        assert "gh" in msg.lower()
        assert cost == 0.0

    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_fails_with_invalid_url(self, mock_gh):
        success, msg, cost, model = run_agentic_checkup(
            "not-a-url", quiet=True
        )
        assert not success
        assert "Invalid" in msg

    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    @patch("pdd.agentic_checkup._run_gh_command")
    def test_fails_when_issue_fetch_fails(self, mock_gh_cmd, mock_gh_cli):
        mock_gh_cmd.return_value = (False, "404 not found")
        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/999", quiet=True
        )
        assert not success
        assert "Failed to fetch issue" in msg

    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    @patch("pdd.agentic_checkup._run_gh_command")
    def test_fails_when_issue_json_invalid(self, mock_gh_cmd, mock_gh_cli):
        mock_gh_cmd.return_value = (True, "not json")
        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1", quiet=True
        )
        assert not success
        assert "parse issue JSON" in msg

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="pddrc: test")
    @patch("pdd.agentic_checkup._load_architecture_json", return_value=([], Path("/tmp/arch.json")))
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_full_flow_success(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        issue_data = {"title": "Check CRM", "body": "Run full checkup"}
        # First call: fetch issue. Second call: fetch comments (paginate).
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (True, "Checkup complete", 0.50, "anthropic")

        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success
        assert msg == "Checkup complete"
        assert cost == pytest.approx(0.50)
        assert model == "anthropic"
        mock_orchestrator.assert_called_once()

    @patch("pdd.agentic_checkup._post_error_comment")
    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch("pdd.agentic_checkup._load_architecture_json", return_value=(None, Path("/tmp/arch.json")))
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_orchestrator_exception_posts_error_comment(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
        mock_post_error,
    ):
        issue_data = {"title": "Check", "body": "check all"}
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_orchestrator.side_effect = RuntimeError("Kaboom")

        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert not success
        assert "Orchestrator failed" in msg
        mock_post_error.assert_called_once()

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch("pdd.agentic_checkup._load_architecture_json", return_value=(None, Path("/tmp/arch.json")))
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_orchestrator_failure_returned(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        issue_data = {"title": "Check", "body": "check"}
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (False, "Step 3 failed", 0.30, "anthropic")

        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert not success
        assert msg == "Step 3 failed"

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch("pdd.agentic_checkup._load_architecture_json", return_value=(None, Path("/tmp/arch.json")))
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_no_fix_mode_passed_through(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        issue_data = {"title": "Check", "body": "check"}
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (True, "report only", 0.10, "anthropic")

        run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            no_fix=True,
        )

        mock_orchestrator.assert_called_once()
        call_kwargs = mock_orchestrator.call_args[1]
        assert call_kwargs["no_fix"] is True

    @patch("pdd.agentic_checkup.run_checkup_review_loop")
    @patch("pdd.agentic_checkup._fetch_pr_context", return_value='PR context {"ok": true}')
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="setting: {raw}")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=([{"name": "{module}"}], Path("/tmp/arch.json")),
    )
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_review_only_mode_passed_to_review_loop_config(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_fetch_pr_context,
        mock_review_loop,
    ):
        issue_data = {
            "title": "Check {workflow}",
            "body": "check {value}",
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_review_loop.return_value = (True, "review report", 0.10, "codex")

        run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            pr_url="https://github.com/owner/repo/pull/2",
            review_loop=True,
            review_only=True,
        )

        config = mock_review_loop.call_args.kwargs["config"]
        context = mock_review_loop.call_args.kwargs["context"]
        assert config.review_only is True
        assert context.issue_title == "Check {workflow}"
        assert "check {value}" in context.issue_content
        assert context.pr_content == 'PR context {"ok": true}'
        assert context.pddrc_content == "setting: {raw}"
        assert '"name": "{module}"' in context.architecture_json
        assert "{{" not in context.issue_content
        assert "{{" not in context.pr_content

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch("pdd.agentic_checkup._load_architecture_json", return_value=(None, Path("/tmp/arch.json")))
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_timeout_adder_passed_through(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        issue_data = {"title": "Check", "body": "check"}
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (True, "ok", 0.10, "anthropic")

        run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            timeout_adder=120.0,
        )

        call_kwargs = mock_orchestrator.call_args[1]
        assert call_kwargs["timeout_adder"] == 120.0

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch("pdd.agentic_checkup._load_architecture_json", return_value=(None, Path("/tmp/arch.json")))
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_use_github_state_passed_through(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        issue_data = {"title": "Check", "body": "check"}
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (True, "ok", 0.10, "anthropic")

        run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            use_github_state=False,
        )

        call_kwargs = mock_orchestrator.call_args[1]
        assert call_kwargs["use_github_state"] is False

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch("pdd.agentic_checkup._load_architecture_json")
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_handles_empty_issue_body(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        """Issue body can be null in GitHub API."""
        issue_data = {"title": "Check", "body": None}
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, "[]"),
        ]
        mock_load_arch.return_value = (None, Path("/tmp/arch.json"))
        mock_orchestrator.return_value = (True, "ok", 0.10, "anthropic")

        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success


# ---------------------------------------------------------------------------
# checkup CLI command
# ---------------------------------------------------------------------------

class TestCheckupCommand:
    """Test the Click command interface."""

    def test_validate_arch_includes_mode_ok(self, tmp_path):
        """--validate-arch-includes runs without TARGET (fixture-style layout)."""
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        (tmp_path / ".git").mkdir()
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "child_Python.prompt").write_text(
            "%\n<include>parent_python.prompt</include>\n", encoding="utf-8"
        )
        (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
        import json

        arch = [
            {"filename": "child_Python.prompt", "dependencies": ["parent_Python.prompt"]},
            {"filename": "parent_Python.prompt", "dependencies": []},
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["--validate-arch-includes", "--project-root", str(tmp_path)],
            obj={"quiet": False},
        )
        assert result.exit_code == 0
        assert "No architecture" in result.output or "mismatches" in result.output

    def test_validate_arch_includes_rejects_extra_target(self):
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["https://github.com/o/r/issues/1", "--validate-arch-includes"],
            obj={"quiet": False},
        )
        assert result.exit_code != 0

    def test_rejects_non_url_target(self):
        """The command should reject non-URL targets."""
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        runner = CliRunner()
        result = runner.invoke(checkup, ["my_module"], obj={"quiet": False})
        assert result.exit_code != 0
        assert "GitHub issue URL" in result.output

    @patch("pdd.commands.checkup.run_agentic_checkup")
    @patch("pdd.commands.checkup._is_github_issue_url", return_value=True)
    def test_dispatches_to_run_agentic_checkup(self, mock_is_url, mock_run):
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        mock_run.return_value = (True, "All good", 0.50, "anthropic")

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["https://github.com/owner/repo/issues/1"],
            obj={"quiet": False, "verbose": False},
        )

        assert result.exit_code == 0
        mock_run.assert_called_once()

    @patch("pdd.commands.checkup.run_agentic_checkup")
    @patch("pdd.commands.checkup._is_github_issue_url", return_value=True)
    def test_passes_no_fix_flag(self, mock_is_url, mock_run):
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        mock_run.return_value = (True, "Report only", 0.20, "anthropic")

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["https://github.com/owner/repo/issues/1", "--no-fix"],
            obj={"quiet": False, "verbose": False},
        )

        assert result.exit_code == 0
        call_kwargs = mock_run.call_args[1]
        assert call_kwargs["no_fix"] is True

    @patch("pdd.commands.checkup.run_agentic_checkup")
    @patch("pdd.commands.checkup._is_github_issue_url", return_value=True)
    def test_passes_timeout_adder_option(self, mock_is_url, mock_run):
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        mock_run.return_value = (True, "Done", 0.10, "anthropic")

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["https://github.com/owner/repo/issues/1", "--timeout-adder", "120.0"],
            obj={"quiet": False, "verbose": False},
        )

        assert result.exit_code == 0
        call_kwargs = mock_run.call_args[1]
        assert call_kwargs["timeout_adder"] == 120.0

    @patch("pdd.commands.checkup.run_agentic_checkup")
    @patch("pdd.commands.checkup._is_github_issue_url", return_value=True)
    def test_passes_no_github_state_flag(self, mock_is_url, mock_run):
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        mock_run.return_value = (True, "Done", 0.10, "anthropic")

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["https://github.com/owner/repo/issues/1", "--no-github-state"],
            obj={"quiet": False, "verbose": False},
        )

        assert result.exit_code == 0
        call_kwargs = mock_run.call_args[1]
        assert call_kwargs["use_github_state"] is False

    @patch("pdd.commands.checkup.run_agentic_checkup")
    @patch("pdd.commands.checkup._is_github_issue_url", return_value=True)
    def test_exits_with_code_1_on_failure(self, mock_is_url, mock_run):
        from click.testing import CliRunner
        from pdd.commands.checkup import checkup

        mock_run.return_value = (False, "Checkup failed", 0.30, "anthropic")

        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["https://github.com/owner/repo/issues/1"],
            obj={"quiet": False, "verbose": False},
        )

        assert result.exit_code == 1
