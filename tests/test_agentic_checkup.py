"""Tests for pdd.agentic_checkup module."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_checkup import (
    _extract_json_from_text,
    _fetch_comments,
    _fetch_pr_context,
    _finalize_hosted_agentic_artifact,
    _hosted_agentic_reviewers,
    _load_pddrc_content,
    _post_checkup_comment,
    _post_error_comment,
    _prepare_hosted_agentic_artifact,
    _publish_hosted_agentic_artifact,
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


class TestHostedAgenticReviewers:
    def test_uses_env_reviewers_only_when_fallback_mirror_enabled(self, monkeypatch):
        monkeypatch.setenv(
            "PDD_AGENTIC_CHECKUP_REVIEWERS",
            "codex:/review,claude:/code-review",
        )

        assert _hosted_agentic_reviewers("codex,claude") == "codex,claude"
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        assert (
            _hosted_agentic_reviewers("codex,claude")
            == "codex:/review,claude:/code-review"
        )

    def test_cli_slash_commands_win_over_env_reviewers(self, monkeypatch):
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        monkeypatch.setenv(
            "PDD_AGENTIC_CHECKUP_REVIEWERS",
            "codex:/review,claude:/code-review",
        )

        assert (
            _hosted_agentic_reviewers("gemini:/review,codex:/review")
            == "gemini:/review,codex:/review"
        )

    def test_ignores_env_reviewers_without_commands(self, monkeypatch):
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        monkeypatch.setenv("PDD_AGENTIC_CHECKUP_REVIEWERS", "gemini,codex")

        assert _hosted_agentic_reviewers("codex,claude") == "codex,claude"


@pytest.mark.parametrize(
    "example_path",
    [
        Path("context/agentic_checkup_example.py"),
        Path("examples/agentic_checkup_example.py"),
    ],
)
def test_agentic_checkup_examples_do_not_log_returned_message(example_path):
    """Returned diagnostics may contain credentials and must stay out of logs."""
    source = example_path.read_text(encoding="utf-8")
    print_lines = [line for line in source.splitlines() if "print(" in line]

    assert all("{message}" not in line for line in print_lines)
    assert all("{_message}" not in line for line in print_lines)
    assert 'print("Message    : omitted from logs")' in source


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
        success, msg, cost, model = run_agentic_checkup("not-a-url", quiet=True)
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
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=([], Path("/tmp/arch.json")),
    )
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
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=(None, Path("/tmp/arch.json")),
    )
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
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=(None, Path("/tmp/arch.json")),
    )
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
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=(None, Path("/tmp/arch.json")),
    )
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

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=(None, Path("/tmp/arch.json")),
    )
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_pr_mode_without_issue_skips_issue_fetch(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        """#1292: ``--pr`` with no issue must not fetch an issue, and the PR
        becomes the comment/state thread while the issue context is empty
        (so the step prompts review the PR on its own merits)."""
        mock_orchestrator.return_value = (True, "Checkup complete", 0.40, "anthropic")

        success, msg, cost, model = run_agentic_checkup(
            None,  # no --issue
            quiet=True,
            pr_url="https://github.com/owner/repo/pull/42",
            use_github_state=False,
        )

        assert success
        assert msg == "Checkup complete"
        # The issue body/comments fetch must be skipped entirely — there is
        # no issue to read. (PR context is fetched inside the orchestrator,
        # which is mocked here.)
        mock_gh_cmd.assert_not_called()
        mock_orchestrator.assert_called_once()
        kwargs = mock_orchestrator.call_args.kwargs
        # Empty issue context — never the literal "None" — drives merit review.
        assert kwargs["issue_url"] == ""
        assert kwargs["issue_content"] == ""
        assert kwargs["issue_title"] == ""
        # Thread/state target aliases to the PR (GitHub treats PRs as issues).
        assert kwargs["issue_number"] == 42
        assert kwargs["repo_owner"] == "owner"
        assert kwargs["repo_name"] == "repo"
        assert kwargs["pr_url"] == "https://github.com/owner/repo/pull/42"
        assert kwargs["pr_number"] == 42

    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_pr_mode_without_issue_rejects_invalid_pr_url(self, mock_gh_cli):
        """#1292: even with no issue, an unparseable --pr URL fails fast."""
        success, msg, cost, model = run_agentic_checkup(
            None,
            quiet=True,
            pr_url="not-a-pr",
            use_github_state=False,
        )
        assert not success
        assert "Invalid GitHub PR URL" in msg

    @patch("pdd.agentic_checkup.run_checkup_review_loop")
    @patch(
        "pdd.agentic_checkup._fetch_pr_context", return_value='PR context {"ok": true}'
    )
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
            reviewer_fallback="gemini",
            allow_same_reviewer_fixer=True,
        )

        config = mock_review_loop.call_args.kwargs["config"]
        context = mock_review_loop.call_args.kwargs["context"]
        assert config.review_only is True
        assert config.reviewer_fallback == "gemini"
        assert config.allow_same_reviewer_fixer is True
        assert context.issue_title == "Check {workflow}"
        assert "check {value}" in context.issue_content
        assert context.pr_content == 'PR context {"ok": true}'
        assert context.pddrc_content == "setting: {raw}"
        assert '"name": "{module}"' in context.architecture_json
        assert "{{" not in context.issue_content
        assert "{{" not in context.pr_content

    @patch("pdd.agentic_checkup.run_checkup_review_loop")
    @patch(
        "pdd.agentic_checkup._fetch_pr_context", return_value='PR context {"ok": true}'
    )
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="setting: {raw}")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=([{"name": "{module}"}], Path("/tmp/arch.json")),
    )
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_agentic_no_fix_maps_to_review_only_config(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_fetch_pr_context,
        mock_review_loop,
        monkeypatch,
        tmp_path,
    ):
        mock_review_loop.return_value = (True, "review report", 0.10, "codex")
        private_artifact = tmp_path / "private-agentic-verdict.json"
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        monkeypatch.setenv(
            "PDD_AGENTIC_CHECKUP_ARTIFACT_PATH",
            str(tmp_path / "hosted-agentic-verdict.json"),
        )

        run_agentic_checkup(
            None,
            quiet=True,
            pr_url="https://github.com/owner/repo/pull/2",
            agentic_review_loop=True,
            agentic_artifact_path=str(private_artifact),
            no_fix=True,
        )

        config = mock_review_loop.call_args.kwargs["config"]
        assert config.agentic_mode is True
        assert config.agentic_artifact_path == str(private_artifact)
        assert config.no_fix is True
        assert config.review_only is True

    @patch("pdd.agentic_checkup.load_final_state")
    @patch("pdd.agentic_checkup.clear_final_state")
    @patch("pdd.agentic_checkup._load_layer1_step5_evidence", return_value=None)
    @patch("pdd.agentic_checkup.run_checkup_review_loop")
    @patch(
        "pdd.agentic_checkup._fetch_pr_context", return_value='PR context {"ok": true}'
    )
    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="setting: {raw}")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=([{"name": "{module}"}], Path("/tmp/arch.json")),
    )
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_final_gate_env_contract_enables_agentic_artifact_path(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
        mock_fetch_pr_context,
        mock_review_loop,
        mock_layer1_evidence,
        mock_clear_final_state,
        mock_load_final_state,
        monkeypatch,
    ):
        issue_data = {
            "title": "Check {workflow}",
            "body": "check {value}",
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_orchestrator.return_value = (True, "layer 1 passed", 0.10, "claude")
        mock_review_loop.return_value = (True, "review report", 0.20, "codex")
        mock_load_final_state.side_effect = [
            None,
            {
                "fresh_final_status": "clean",
                "reviewer_status": {"codex": "clean"},
                "active_reviewer": "codex",
                "findings": [],
                "issue_aligned": True,
            },
        ]
        artifact_path = "/tmp/pdd-cloud/agentic-checkup.json"
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        monkeypatch.setenv("PDD_AGENTIC_CHECKUP_ARTIFACT_PATH", artifact_path)
        monkeypatch.setenv(
            "PDD_AGENTIC_CHECKUP_REVIEWERS", "gemini:/review,claude:/review"
        )

        success, msg, cost, model = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            pr_url="https://github.com/owner/repo/pull/2",
            final_gate=True,
            use_github_state=False,
        )

        assert success is True
        assert "Final gate" in msg
        assert cost == pytest.approx(0.30)
        assert model == "codex"
        config = mock_review_loop.call_args.kwargs["config"]
        assert config.agentic_mode is True
        assert config.agentic_artifact_path != artifact_path
        assert Path(config.agentic_artifact_path).parent == Path(artifact_path).parent
        assert config.agentic_artifact_path.endswith(".invocation.tmp")
        assert config.review_only is False
        assert config.no_fix is False
        assert config.reviewers == ("codex", "claude")
        assert config.adversarial_prompt is None
        assert config.fresh_final_review_role is None
        assert config.reviewer_commands == {
            "codex": "",
            "claude": "",
        }
        assert config.artifact_reviewer_commands == {
            "gemini": "/review",
            "claude": "/review",
        }
        # Authority is finalized only after the complete final-gate verdict is
        # known; Layer 2 must not be pre-labeled as canonical pass.
        loop_context = mock_review_loop.call_args.kwargs["context"]
        assert loop_context.final_gate_canonical_status == ""

    def test_prepare_hosted_artifact_replaces_stale_pass(self, tmp_path):
        path = tmp_path / "agentic.json"
        path.write_text(
            json.dumps(
                {
                    "schema_version": "pdd.checkup.agentic.v1",
                    "status": "passed",
                    "authority": "canonical_pass_agentic_mirror_clean",
                    "verdict": {"decision": "pass"},
                }
            ),
            encoding="utf-8",
        )

        reservation = _prepare_hosted_agentic_artifact(
            str(path), pr_owner="promptdriven", pr_repo="pdd", pr_number=1790
        )
        assert reservation is not None
        assert reservation.private_path != path

        payload = json.loads(path.read_text(encoding="utf-8"))
        assert payload["schema_version"] == "pdd.checkup.agentic.v1"
        assert payload["status"] != "passed"
        assert payload["authority"] == "canonical_unknown_agentic_fallback_blocking"
        assert payload["verdict"]["decision"] == "block"

    def test_prepare_hosted_artifact_accepts_equivalent_normalized_path(
        self, tmp_path, monkeypatch
    ):
        monkeypatch.chdir(tmp_path)

        assert _prepare_hosted_agentic_artifact("./agentic.json") is not None

        payload = json.loads((tmp_path / "agentic.json").read_text(encoding="utf-8"))
        assert payload["status"] != "passed"
        assert payload["verdict"]["decision"] == "block"

    def test_prepare_hosted_artifact_scrubs_identity_fields(self, tmp_path):
        path = tmp_path / "agentic.json"
        secret_owner = "ghp_ABCDEFGHIJKLMNOPQRSTUVWXYZ123456"
        reservation = _prepare_hosted_agentic_artifact(
            str(path), pr_owner=secret_owner, pr_repo=secret_owner, pr_number=1
        )
        assert reservation is not None
        payload_text = path.read_text(encoding="utf-8")
        assert secret_owner not in payload_text
        assert secret_owner not in reservation.identity_digest
        reservation.cleanup()

    def test_hosted_early_return_cleans_private_and_owner_files(
        self, tmp_path, monkeypatch
    ):
        public = tmp_path / "agentic.json"
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        monkeypatch.setenv("PDD_AGENTIC_CHECKUP_ARTIFACT_PATH", str(public))

        with (
            patch("pdd.agentic_checkup._find_project_root", return_value=tmp_path),
            patch("pdd.agentic_checkup._check_gh_cli", return_value=False),
        ):
            success, _message, _cost, _model = run_agentic_checkup(
                "https://github.com/owner/repo/issues/1", quiet=True, cwd=tmp_path
            )

        assert success is False
        assert public.exists()
        assert json.loads(public.read_text(encoding="utf-8"))["status"] != "passed"
        assert not list(tmp_path.glob("*.invocation.tmp"))
        assert not list(tmp_path.glob("*.owner.json"))

    def test_prepare_hosted_artifact_failure_replaces_stale_pass_with_blocker(
        self, tmp_path
    ):
        path = tmp_path / "agentic.json"
        stale = {
            "schema_version": "pdd.checkup.agentic.v1",
            "status": "passed",
            "authority": "canonical_pass_agentic_mirror_clean",
            "verdict": {"decision": "pass"},
        }
        path.write_text(json.dumps(stale), encoding="utf-8")

        with (
            patch.object(Path, "unlink", side_effect=PermissionError),
            patch(
                "pdd.agentic_checkup.write_final_gate_fallback_artifact",
                return_value=None,
            ),
        ):
            assert _prepare_hosted_agentic_artifact(str(path)) is None

        persisted = json.loads(path.read_text(encoding="utf-8"))
        assert persisted["status"] != "passed"
        assert persisted["verdict"]["decision"] == "block"

    @pytest.mark.parametrize("payload", ["not-json", "{}"])
    def test_prepare_hosted_artifact_rejects_malformed_readback(
        self, tmp_path, payload
    ):
        path = tmp_path / "agentic.json"

        def malformed_writer(**kwargs):
            private = Path(kwargs["artifact_path"])
            private.write_text(payload, encoding="utf-8")
            return str(private)

        with patch(
            "pdd.agentic_checkup.write_final_gate_fallback_artifact",
            side_effect=malformed_writer,
        ):
            assert _prepare_hosted_agentic_artifact(str(path)) is None

    def test_hosted_run_stops_before_other_early_returns_without_provenance(
        self, tmp_path, monkeypatch
    ):
        monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
        monkeypatch.setenv(
            "PDD_AGENTIC_CHECKUP_ARTIFACT_PATH", str(tmp_path / "agentic.json")
        )

        with (
            patch(
                "pdd.agentic_checkup._prepare_hosted_agentic_artifact",
                return_value=None,
            ),
            patch("pdd.agentic_checkup._check_gh_cli") as check_gh,
        ):
            success, message, cost, model = run_agentic_checkup(
                "https://github.com/owner/repo/issues/1", quiet=True, cwd=tmp_path
            )

        assert success is False
        assert "provenance" in message
        assert cost == 0.0
        assert model == ""
        check_gh.assert_not_called()

    def test_hosted_overlapping_run_cannot_publish_into_newer_slot(self, tmp_path):
        path = tmp_path / "agentic.json"
        older = _prepare_hosted_agentic_artifact(
            str(path), pr_owner="promptdriven", pr_repo="pdd", pr_number=1790
        )
        newer = _prepare_hosted_agentic_artifact(
            str(path), pr_owner="promptdriven", pr_repo="pdd", pr_number=1790
        )
        assert older is not None and newer is not None
        assert older.invocation_id != newer.invocation_id

        older_payload = json.loads(older.private_path.read_text(encoding="utf-8"))
        older_payload.update(
            status="passed",
            authority="canonical_pass_agentic_mirror_clean",
            layer1={"status": "pass", "blockers": []},
            verdict={"decision": "pass", "reason": "older clean run"},
        )
        older.private_path.write_text(json.dumps(older_payload), encoding="utf-8")

        # The older invocation finishes after the newer invocation claimed the
        # public slot. Its PASS must be discarded by the invocation-ID CAS.
        assert _publish_hosted_agentic_artifact(older, canonical_passed=True) is None
        owner_payload = json.loads(newer.owner_path.read_text(encoding="utf-8"))
        assert owner_payload["invocation_id"] == newer.invocation_id
        public_payload = json.loads(path.read_text(encoding="utf-8"))
        assert public_payload["status"] != "passed"
        assert public_payload["verdict"]["decision"] == "block"

    def test_finalize_hosted_artifact_canonical_fail_dominates_stale_pass(
        self, tmp_path
    ):
        path = tmp_path / "agentic.json"
        path.write_text(
            json.dumps(
                {
                    "schema_version": "pdd.checkup.agentic.v1",
                    "status": "passed",
                    "authority": "canonical_pass_agentic_mirror_clean",
                    "layer1": {"status": "pass", "blockers": []},
                    "verdict": {"decision": "pass", "reason": "clean"},
                }
            ),
            encoding="utf-8",
        )

        assert _finalize_hosted_agentic_artifact(
            str(path), canonical_passed=False
        ) == str(path)

        payload = json.loads(path.read_text(encoding="utf-8"))
        assert payload["layer1"]["status"] == "fail"
        assert payload["status"] == "failed"
        assert payload["authority"] == "canonical_fail_agentic_not_authoritative"
        assert payload["verdict"]["decision"] == "block"

    def test_finalize_hosted_artifact_failclosed_when_publish_fails(self, tmp_path):
        """Issue #1788: a canonical FAILURE must never leave a consumable pass,
        even when the atomic publish itself fails."""
        path = tmp_path / "agentic.json"
        # A Layer 2 mirror left a PASSING artifact on disk.
        path.write_text(
            json.dumps(
                {
                    "schema_version": "pdd.checkup.agentic.v1",
                    "status": "passed",
                    "authority": "canonical_pass_agentic_mirror_clean",
                    "layer1": {"status": "pass", "blockers": []},
                    "verdict": {"decision": "pass", "reason": "clean"},
                }
            ),
            encoding="utf-8",
        )
        # Canonical gate FAILED, but every atomic publish (os.replace) fails.
        with patch("pdd.agentic_checkup.os.replace", side_effect=OSError("no rename")):
            result = _finalize_hosted_agentic_artifact(
                str(path), canonical_passed=False
            )
        assert result is None
        # The prior PASS must not survive: removed, or left non-pass.
        if path.exists():
            payload = json.loads(path.read_text(encoding="utf-8"))
            assert payload.get("status") != "passed"
            assert payload.get("verdict", {}).get("decision") != "pass"

    def test_finalize_hosted_artifact_failclosed_on_unreadable(self, tmp_path):
        """Issue #1788: when the prior artifact cannot be parsed and the
        canonical gate FAILED, replace it with a blocking tombstone rather than
        leaving an ambiguous/consumable file."""
        path = tmp_path / "agentic.json"
        path.write_text("{ not valid json", encoding="utf-8")
        result = _finalize_hosted_agentic_artifact(str(path), canonical_passed=False)
        assert result is None
        assert path.exists()
        payload = json.loads(path.read_text(encoding="utf-8"))
        assert payload["status"] == "failed"
        assert payload["authority"] == "canonical_fail_agentic_not_authoritative"
        assert payload["verdict"]["decision"] == "block"

    def test_finalize_hosted_artifact_canonical_pass_untouched_on_bad_schema(
        self, tmp_path
    ):
        """A canonical PASS must not fabricate/alter an unrelated file: an
        invalid-schema artifact is left as-is (returns None, no tombstone)."""
        path = tmp_path / "agentic.json"
        original = json.dumps({"schema_version": "something.else", "x": 1})
        path.write_text(original, encoding="utf-8")
        result = _finalize_hosted_agentic_artifact(str(path), canonical_passed=True)
        assert result is None
        assert path.read_text(encoding="utf-8") == original

    def _seed_passing_hosted_reservation(self, tmp_path):
        """Reserve a hosted slot whose private artifact holds a mirror PASS.

        This models the review loop having written a passing
        ``pdd.checkup.agentic.v1`` mirror to the invocation-private path before
        the outer final gate downgrades authority.
        """
        path = tmp_path / "agentic.json"
        reservation = _prepare_hosted_agentic_artifact(
            str(path), pr_owner="promptdriven", pr_repo="pdd", pr_number=1790
        )
        assert reservation is not None
        payload = json.loads(reservation.private_path.read_text(encoding="utf-8"))
        payload.update(
            status="passed",
            authority="canonical_unknown_agentic_fallback_pass",
            layer1={"status": "unknown", "blockers": []},
            verdict={"decision": "pass", "reason": "mirror clean"},
        )
        reservation.private_path.write_text(json.dumps(payload), encoding="utf-8")
        return path, reservation

    def test_publish_hosted_artifact_terminal_when_finalization_fails_canonical_fail(
        self, tmp_path
    ):
        """Issue #1788 P1: when canonical finalization cannot downgrade the
        private artifact (returns None), the pre-finalization payload — a stale
        PASS — must NEVER be published. Regression through
        ``_publish_hosted_agentic_artifact``, not the isolated finalizer: the
        public slot must retain its blocking placeholder."""
        path, reservation = self._seed_passing_hosted_reservation(tmp_path)

        # Canonical gate FAILED and finalization could neither downgrade nor
        # tombstone the artifact (returns None, private payload unchanged).
        with patch(
            "pdd.agentic_checkup._finalize_hosted_agentic_artifact",
            return_value=None,
        ):
            result = _publish_hosted_agentic_artifact(
                reservation, canonical_passed=False
            )

        assert result is None
        public_payload = json.loads(path.read_text(encoding="utf-8"))
        assert public_payload.get("status") != "passed"
        assert public_payload.get("verdict", {}).get("decision") == "block"

    def test_publish_hosted_artifact_terminal_when_finalization_fails_canonical_pass(
        self, tmp_path
    ):
        """Issue #1788 P1: a canonical PASS whose finalization fails (returns
        None) is also terminal — the un-finalized private payload must not be
        published; the public slot keeps its blocking placeholder."""
        path, reservation = self._seed_passing_hosted_reservation(tmp_path)

        with patch(
            "pdd.agentic_checkup._finalize_hosted_agentic_artifact",
            return_value=None,
        ):
            result = _publish_hosted_agentic_artifact(
                reservation, canonical_passed=True
            )

        assert result is None
        public_payload = json.loads(path.read_text(encoding="utf-8"))
        assert public_payload.get("status") != "passed"
        assert public_payload.get("verdict", {}).get("decision") == "block"

    def test_publish_hosted_artifact_terminal_when_finalization_returns_wrong_path(
        self, tmp_path
    ):
        """Issue #1788 P1: a finalizer result that is not this invocation's
        private path is terminal — never publish the original private payload."""
        path, reservation = self._seed_passing_hosted_reservation(tmp_path)

        with patch(
            "pdd.agentic_checkup._finalize_hosted_agentic_artifact",
            return_value=str(tmp_path / "somewhere-else.json"),
        ):
            result = _publish_hosted_agentic_artifact(
                reservation, canonical_passed=False
            )

        assert result is None
        public_payload = json.loads(path.read_text(encoding="utf-8"))
        assert public_payload.get("status") != "passed"

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=(None, Path("/tmp/arch.json")),
    )
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
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=(None, Path("/tmp/arch.json")),
    )
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
            {
                "filename": "child_Python.prompt",
                "dependencies": ["parent_Python.prompt"],
            },
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


class TestRunAgenticCheckupCwdParameter:
    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="pddrc: test")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=([], Path("/tmp/arch.json")),
    )
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_cwd_forwarded_to_find_project_root(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
        tmp_path,
    ):
        mock_gh_cmd.side_effect = [
            (True, json.dumps({"title": "t", "body": "b"})),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (True, "ok", 0.0, "fake-model")

        run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            cwd=tmp_path,
            use_github_state=False,
        )

        assert mock_find_root.call_args.args[0] == tmp_path

    @patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
    @patch("pdd.agentic_checkup._load_pddrc_content", return_value="pddrc: test")
    @patch(
        "pdd.agentic_checkup._load_architecture_json",
        return_value=([], Path("/tmp/arch.json")),
    )
    @patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/project"))
    @patch("pdd.agentic_checkup._run_gh_command")
    @patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
    def test_cwd_none_falls_back_to_path_cwd(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_find_root,
        mock_load_arch,
        mock_load_pddrc,
        mock_orchestrator,
    ):
        mock_gh_cmd.side_effect = [
            (True, json.dumps({"title": "t", "body": "b"})),
            (True, "[]"),
        ]
        mock_orchestrator.return_value = (True, "ok", 0.0, "fake-model")

        with patch("pdd.agentic_checkup.Path.cwd", return_value=Path("/fallback/cwd")):
            run_agentic_checkup(
                "https://github.com/owner/repo/issues/1",
                quiet=True,
                use_github_state=False,
            )

        assert mock_find_root.call_args.args[0] == Path("/fallback/cwd")


# ---------------------------------------------------------------------------
# Issue #1788: final-gate short-circuit failures emit the canonical-fail
# mirror artifact for hosted consumers.
# ---------------------------------------------------------------------------


def _run_final_gate_short_circuit(
    tmp_path,
    monkeypatch,
    *,
    orchestrator,
    github_gate,
    full_suite_source="local",
    test_scope="full",
):
    artifact_path = tmp_path / "agentic-checkup.json"
    monkeypatch.setenv("PDD_CHECKUP_FALLBACK_MIRROR", "1")
    monkeypatch.setenv("PDD_AGENTIC_CHECKUP_ARTIFACT_PATH", str(artifact_path))
    issue_data = {"title": "t", "body": "b", "comments_url": ""}
    stack = [
        patch("pdd.agentic_checkup._check_gh_cli", return_value=True),
        patch(
            "pdd.agentic_checkup._run_gh_command",
            return_value=(True, json.dumps(issue_data)),
        ),
        patch("pdd.agentic_checkup._find_project_root", return_value=tmp_path),
        patch(
            "pdd.agentic_checkup._load_architecture_json",
            return_value=(None, tmp_path / "arch.json"),
        ),
        patch("pdd.agentic_checkup._load_pddrc_content", return_value=""),
        patch("pdd.agentic_checkup._load_layer1_step5_evidence", return_value=None),
        patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=orchestrator,
        ),
    ]
    if github_gate is not None:
        stack.append(
            patch(
                "pdd.agentic_checkup.run_github_checks_gate",
                return_value=github_gate,
            )
        )
    from contextlib import ExitStack

    with ExitStack() as es:
        for cm in stack:
            es.enter_context(cm)
        result = run_agentic_checkup(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            pr_url="https://github.com/owner/repo/pull/2",
            final_gate=True,
            full_suite_source=full_suite_source,
            test_scope=test_scope,
            use_github_state=False,
        )
    return result, artifact_path


def test_final_gate_layer1_failure_writes_canonical_fail_artifact(
    tmp_path, monkeypatch
):
    (success, msg, _cost, _model), artifact_path = _run_final_gate_short_circuit(
        tmp_path,
        monkeypatch,
        orchestrator=(False, "layer 1 boom", 0.1, "claude"),
        github_gate=None,
    )
    assert success is False
    assert "Final gate Layer 1 failed" in msg
    assert artifact_path.exists()
    data = json.loads(artifact_path.read_text())
    assert data["schema_version"] == "pdd.checkup.agentic.v1"
    assert data["authority"] == "canonical_fail_agentic_not_authoritative"
    assert data["layer1"]["status"] == "fail"
    assert data["layer1"]["blockers"]


def test_final_gate_github_checks_failure_writes_canonical_fail_artifact(
    tmp_path, monkeypatch
):
    (success, msg, _cost, _model), artifact_path = _run_final_gate_short_circuit(
        tmp_path,
        monkeypatch,
        orchestrator=(True, "layer 1 passed", 0.1, "claude"),
        github_gate=(False, "required check failing", "deadbeef"),
        full_suite_source="github-checks",
        test_scope="targeted",
    )
    assert success is False
    assert "GitHub checks gate failed" in msg
    assert artifact_path.exists()
    data = json.loads(artifact_path.read_text())
    assert data["authority"] == "canonical_fail_agentic_not_authoritative"
    assert data["layer1"]["status"] == "fail"
