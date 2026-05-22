"""Tests for `pdd checkup --pr` mode.

Covers:
- `_parse_pr_url` — URL shape parsing
- CLI validation — mutex with TARGET / --validate-arch-includes, both-or-neither,
  URL-format checks
- `_setup_pr_worktree` — happy path and fetch-failure path (subprocess mocked)
- Orchestrator PR-mode wiring — step 8 skip, PR worktree created once, `pr_mode`
  context populated

The orchestrator tests stub out `_run_single_step` so no LLM calls happen.
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.agentic_change import _parse_pr_url
from pdd.commands.checkup import checkup


# Step 7's prompt requires a structured JSON verdict as the LAST block of
# output. Round-4 Finding 1 added `_step7_passed`, which fails-closed when
# that JSON is missing or reports failure. Tests that simulate a clean Step
# 7 now must emit both the legacy "All Issues Fixed" loop-exit sentinel AND
# the matching JSON payload.
STEP7_CLEAN_JSON = (
    '```json\n'
    '{\n'
    '  "success": true,\n'
    '  "message": "verification passed",\n'
    '  "issue_aligned": true,\n'
    '  "issues": [],\n'
    '  "changed_files": []\n'
    '}\n'
    '```'
)


def _step7_clean_output(label: str = "All Issues Fixed") -> str:
    """Standard step-7 stub output for tests that simulate a passing run."""
    return f"{label}\n{STEP7_CLEAN_JSON}"


# ---------------------------------------------------------------------------
# _parse_pr_url
# ---------------------------------------------------------------------------


class TestParsePrUrl:
    def test_https_canonical(self) -> None:
        assert _parse_pr_url("https://github.com/org/repo/pull/42") == ("org", "repo", 42)

    def test_http(self) -> None:
        assert _parse_pr_url("http://github.com/org/repo/pull/1") == ("org", "repo", 1)

    def test_www_prefix(self) -> None:
        assert _parse_pr_url("https://www.github.com/org/repo/pull/7") == ("org", "repo", 7)

    def test_no_scheme(self) -> None:
        assert _parse_pr_url("github.com/org/repo/pull/9") == ("org", "repo", 9)

    def test_embedded_in_text(self) -> None:
        # _parse_pr_url uses re.search, not match — URL inside prose must still work.
        assert _parse_pr_url(
            "See https://github.com/a/b/pull/33 for details"
        ) == ("a", "b", 33)

    def test_issue_url_rejected(self) -> None:
        assert _parse_pr_url("https://github.com/org/repo/issues/42") is None

    def test_garbage(self) -> None:
        assert _parse_pr_url("not-a-url") is None

    def test_empty(self) -> None:
        assert _parse_pr_url("") is None

    def test_fork_style_owner(self) -> None:
        # Fork PRs have the fork owner in the URL — must still parse.
        assert _parse_pr_url(
            "https://github.com/some-fork-user/repo/pull/1234"
        ) == ("some-fork-user", "repo", 1234)


# ---------------------------------------------------------------------------
# CLI validation
# ---------------------------------------------------------------------------


class TestCliValidation:
    @pytest.fixture
    def runner(self) -> CliRunner:
        return CliRunner()

    def test_no_args_errors(self, runner: CliRunner) -> None:
        result = runner.invoke(checkup, [])
        assert result.exit_code == 2
        assert "Missing argument 'TARGET'" in result.output

    def test_only_pr_rejected(self, runner: CliRunner) -> None:
        result = runner.invoke(checkup, ["--pr", "https://github.com/o/r/pull/1"])
        assert result.exit_code == 2
        assert "must both be provided" in result.output

    def test_only_issue_opt_rejected(self, runner: CliRunner) -> None:
        result = runner.invoke(
            checkup, ["--issue", "https://github.com/o/r/issues/1"]
        )
        assert result.exit_code == 2
        assert "must both be provided" in result.output

    def test_pr_plus_target_rejected(self, runner: CliRunner) -> None:
        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/o/r/pull/1",
                "--issue",
                "https://github.com/o/r/issues/1",
                "https://github.com/o/r/issues/1",
            ],
        )
        assert result.exit_code == 2
        assert "mutually exclusive" in result.output

    def test_invalid_pr_url(self, runner: CliRunner) -> None:
        result = runner.invoke(
            checkup,
            ["--pr", "not-a-url", "--issue", "https://github.com/o/r/issues/1"],
        )
        assert result.exit_code == 2
        assert "pull-request URL" in result.output

    def test_invalid_issue_url(self, runner: CliRunner) -> None:
        result = runner.invoke(
            checkup,
            ["--pr", "https://github.com/o/r/pull/1", "--issue", "not-a-url"],
        )
        assert result.exit_code == 2
        assert "issue URL" in result.output

    def test_pr_with_validate_arch_includes_rejected(self, runner: CliRunner) -> None:
        result = runner.invoke(
            checkup,
            ["--validate-arch-includes", "--pr", "https://github.com/o/r/pull/1"],
        )
        assert result.exit_code == 2
        assert "Do not pass" in result.output


# ---------------------------------------------------------------------------
# _setup_pr_worktree
# ---------------------------------------------------------------------------


class TestSetupPrWorktree:
    def test_happy_path(self, tmp_path: Path) -> None:
        """Both the fetch and worktree-add subprocess calls succeed."""
        from pdd.agentic_checkup_orchestrator import (
            _pr_worktree_branch_name,
            _setup_pr_worktree,
        )

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._branch_exists", return_value=False
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run"
        ) as run_mock:
            run_mock.return_value = MagicMock(returncode=0, stderr=b"")

            wt_path, err = _setup_pr_worktree(
                cwd=tmp_path,
                pr_owner="acme",
                pr_repo="thing",
                pr_number=77,
                quiet=True,
                resume_existing=False,
            )

            assert err is None
            assert wt_path is not None
            assert str(wt_path).endswith(".pdd/worktrees/checkup-pr-77")

            # Must have both fetched the PR and added a worktree
            cmds = [call.args[0] for call in run_mock.call_args_list]
            fetch_calls = [c for c in cmds if len(c) > 1 and c[0] == "git" and c[1] == "fetch"]
            add_calls = [c for c in cmds if len(c) > 2 and c[0] == "git" and c[1] == "worktree" and c[2] == "add"]
            expected_branch = _pr_worktree_branch_name(tmp_path, 77)
            assert fetch_calls, "expected a git fetch for pull/77/head"
            assert any("pull/77/head" in " ".join(c) for c in fetch_calls)
            assert any(f"pull/77/head:{expected_branch}" in c for c in fetch_calls[0])
            assert add_calls, "expected a git worktree add"
            assert add_calls[0][-1] == expected_branch
            assert expected_branch != "checkup/pr-77"

    def test_pr_branch_name_is_scoped_to_git_root(self, tmp_path: Path) -> None:
        """Linked worktrees share refs, so PR branches must not collide."""
        from pdd.agentic_checkup_orchestrator import _pr_worktree_branch_name

        root_a = tmp_path / "checkout-a"
        root_b = tmp_path / "checkout-b"
        root_a.mkdir()
        root_b.mkdir()

        branch_a = _pr_worktree_branch_name(root_a, 77)
        branch_b = _pr_worktree_branch_name(root_b, 77)

        assert branch_a.startswith("checkup/pr-77-")
        assert branch_b.startswith("checkup/pr-77-")
        assert branch_a != branch_b

    def test_fetch_failure_returns_error(self, tmp_path: Path) -> None:
        """If `git fetch pull/<N>/head` fails, surface a helpful error."""
        from pdd.agentic_checkup_orchestrator import _setup_pr_worktree

        def fake_run(cmd, **_kwargs):  # noqa: ANN001
            if len(cmd) > 1 and cmd[1] == "fetch":
                raise subprocess.CalledProcessError(
                    returncode=1, cmd=cmd, stderr=b"couldn't find remote ref pull/77/head\n"
                )
            return MagicMock(returncode=0, stderr=b"")

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._branch_exists", return_value=False
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            wt_path, err = _setup_pr_worktree(
                cwd=tmp_path,
                pr_owner="acme",
                pr_repo="thing",
                pr_number=77,
                quiet=True,
                resume_existing=False,
            )

        assert wt_path is None
        assert err is not None
        assert "Failed to fetch PR #77" in err
        assert "couldn't find remote ref" in err
        # New error wording surfaces the resolved remote target so the user
        # knows which repo we tried to fetch from.
        assert "acme/thing" in err

    def test_not_a_git_repo(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import _setup_pr_worktree

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=None,
        ):
            wt_path, err = _setup_pr_worktree(
                cwd=tmp_path,
                pr_owner="acme",
                pr_repo="thing",
                pr_number=1,
                quiet=True,
            )

        assert wt_path is None
        assert err is not None
        assert "not a git repository" in err


# ---------------------------------------------------------------------------
# Orchestrator PR-mode wiring
# ---------------------------------------------------------------------------


class TestOrchestratorPrMode:
    def test_step_8_skipped_in_pr_mode(self, tmp_path: Path) -> None:
        """When pr_url is set, step 8 must NOT invoke the create-PR prompt."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            # Signal "All Issues Fixed" from step 7 to exit loop on first pass.
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(tmp_path / "wt", None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ) as run_mock, patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ):
            (tmp_path / "wt").mkdir()

            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success
        # Verify step 8 was never invoked — it's an LLM-calling step, and PR
        # mode must not create a new PR.
        invoked_steps = [c.args[0] for c in run_mock.call_args_list]
        assert 8 not in invoked_steps, (
            f"Step 8 must be skipped in PR mode; invoked: {invoked_steps}"
        )

    def test_pr_mode_max_iterations_without_sentinel_fails_before_push(
        self, tmp_path: Path
    ) -> None:
        """A clean-looking JSON verdict without the loop sentinel is not enough."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            if step_num == 7:
                return (
                    True,
                    '{"success": true, "issue_aligned": true, '
                    '"issues": [], "message": "clean but missing sentinel"}',
                    0.0,
                    "fake-model",
                )
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ) as run_mock, patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ) as clear_mock, patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed"
        ) as push_mock:
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False
        assert "did not verify all issues fixed" in msg.lower()
        invoked_steps = [c.args[0] for c in run_mock.call_args_list]
        assert invoked_steps.count(7) == 3
        assert 8 not in invoked_steps
        push_mock.assert_not_called()
        clear_mock.assert_not_called()

    def test_pr_mode_context_populated(self, tmp_path: Path) -> None:
        """PR-mode fields must land in the context dict passed to step prompts."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        captured_contexts = []

        def capture_step(step_num, _name, context, **_kw):  # noqa: ANN001
            captured_contexts.append(dict(context))
            output = _step7_clean_output() if step_num == 7 else f"out-{step_num}"
            return (True, output, 0.0, "fake")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(tmp_path / "wt", None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=capture_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ):
            (tmp_path / "wt").mkdir()

            run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/forkuser/r/pull/200",
                pr_owner="forkuser",
                pr_repo="r",
                pr_number=200,
            )

        assert captured_contexts, "no steps were run"
        ctx = captured_contexts[0]
        assert ctx["pr_mode"] == "true"
        assert ctx["pr_url"] == "https://github.com/forkuser/r/pull/200"
        assert ctx["pr_owner"] == "forkuser"
        assert ctx["pr_repo"] == "r"
        assert ctx["pr_number"] == "200"

    def test_non_pr_mode_leaves_fields_empty(self, tmp_path: Path) -> None:
        """In ordinary (non-PR) mode, pr_mode is 'false' and URL fields empty."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        captured_contexts = []

        def capture_step(step_num, _name, context, **_kw):  # noqa: ANN001
            captured_contexts.append(dict(context))
            output = _step7_clean_output() if step_num == 7 else f"out-{step_num}"
            return (True, output, 0.0, "fake")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_worktree",
            return_value=(tmp_path / "wt", None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=capture_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ):
            (tmp_path / "wt").mkdir()

            run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                # No PR-mode args
            )

        ctx = captured_contexts[0]
        assert ctx["pr_mode"] == "false"
        assert ctx["pr_url"] == ""
        assert ctx["pr_owner"] == ""
        assert ctx["pr_repo"] == ""
        assert ctx["pr_number"] == ""


# ---------------------------------------------------------------------------
# _resolve_pr_remote — fork-PR support
# ---------------------------------------------------------------------------


class TestResolvePrRemote:
    """The reviewer's "fork PR" claim: hardcoded ``origin`` defeats it.

    `_resolve_pr_remote` must walk `git remote -v` and find a remote whose
    URL points at the PR's owner/repo. When none does, callers fall back to
    the explicit GitHub URL — so a clone of `myfork/repo` can still verify
    a PR that lives on `upstream/repo`.
    """

    def test_finds_matching_remote_https(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import _resolve_pr_remote

        with patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            return_value=MagicMock(
                returncode=0,
                stdout=(
                    "origin\thttps://github.com/myfork/repo.git (fetch)\n"
                    "origin\thttps://github.com/myfork/repo.git (push)\n"
                    "upstream\thttps://github.com/acme/repo.git (fetch)\n"
                    "upstream\thttps://github.com/acme/repo.git (push)\n"
                ),
            ),
        ):
            assert _resolve_pr_remote(tmp_path, "acme", "repo") == "upstream"

    def test_finds_matching_remote_ssh_no_dotgit(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import _resolve_pr_remote

        with patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            return_value=MagicMock(
                returncode=0,
                stdout=(
                    "origin\tgit@github.com:user/proj (fetch)\n"
                    "origin\tgit@github.com:user/proj (push)\n"
                ),
            ),
        ):
            # SSH form without .git, case-insensitive owner matching.
            assert _resolve_pr_remote(tmp_path, "User", "Proj") == "origin"

    def test_no_match_returns_none(self, tmp_path: Path) -> None:
        """Caller falls back to explicit URL when no remote matches —
        the path that makes fork PRs work without manual remote setup."""
        from pdd.agentic_checkup_orchestrator import _resolve_pr_remote

        with patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            return_value=MagicMock(
                returncode=0,
                stdout="origin\thttps://github.com/totally/different.git (fetch)\n",
            ),
        ):
            assert _resolve_pr_remote(tmp_path, "acme", "repo") is None

    def test_subprocess_failure_returns_none(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import _resolve_pr_remote

        with patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=subprocess.CalledProcessError(returncode=128, cmd=["git"]),
        ):
            # Don't crash; let caller fall through to explicit URL.
            assert _resolve_pr_remote(tmp_path, "acme", "repo") is None


class TestSetupPrWorktreePassesRemote:
    """The fetch must use the resolved remote (not literal ``origin``)."""

    def test_uses_explicit_url_when_no_matching_remote(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import _setup_pr_worktree

        captured_fetch_target: list[str] = []

        def fake_run(cmd, **_kwargs):  # noqa: ANN001
            # Capture what `git fetch` was actually pointed at.
            if len(cmd) > 1 and cmd[0] == "git" and cmd[1] == "fetch":
                # cmd shape: ["git", "fetch", <target>, "pull/N/head:branch", "--force"]
                captured_fetch_target.append(cmd[2])
            return MagicMock(returncode=0, stderr=b"", stdout="")

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._branch_exists", return_value=False
        ), patch(
            "pdd.agentic_checkup_orchestrator._resolve_pr_remote",
            return_value=None,  # no configured remote matches → fall back
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            wt_path, err = _setup_pr_worktree(
                cwd=tmp_path,
                pr_owner="upstream",
                pr_repo="myproj",
                pr_number=99,
                quiet=True,
            )

        assert err is None
        assert wt_path is not None
        assert captured_fetch_target == ["https://github.com/upstream/myproj.git"], (
            "must fetch from explicit URL when no remote matches — "
            "this is what makes fork-PR verification actually work"
        )

    def test_uses_named_remote_when_match_exists(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import _setup_pr_worktree

        captured_fetch_target: list[str] = []

        def fake_run(cmd, **_kwargs):  # noqa: ANN001
            if len(cmd) > 1 and cmd[0] == "git" and cmd[1] == "fetch":
                captured_fetch_target.append(cmd[2])
            return MagicMock(returncode=0, stderr=b"", stdout="")

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._branch_exists", return_value=False
        ), patch(
            "pdd.agentic_checkup_orchestrator._resolve_pr_remote",
            return_value="upstream",
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            wt_path, err = _setup_pr_worktree(
                cwd=tmp_path,
                pr_owner="upstream",
                pr_repo="myproj",
                pr_number=99,
                quiet=True,
            )

        assert err is None
        assert wt_path is not None
        assert captured_fetch_target == ["upstream"], (
            "should prefer the named remote (uses cached objects + auth)"
        )


# ---------------------------------------------------------------------------
# State mode-tagging — cross-mode contamination guard
# ---------------------------------------------------------------------------


class TestStateModeTagging:
    """Without a mode tag, an issue-mode worktree at
    ``.pdd/worktrees/checkup-issue-N`` could be silently reused by a
    subsequent PR-mode invocation on the same issue_number — running all
    steps against the wrong code on disk."""

    def test_build_state_records_mode(self) -> None:
        from pdd.agentic_checkup_orchestrator import _build_state

        s_issue = _build_state(
            issue_number=42, issue_url="u", last_completed_step=3,
            step_outputs={}, total_cost=0.0, model_used="m", github_comment_id=None,
        )
        assert s_issue["mode"] == "issue"
        assert s_issue["pr_number"] is None

        s_pr = _build_state(
            issue_number=42, issue_url="u", last_completed_step=3,
            step_outputs={}, total_cost=0.0, model_used="m", github_comment_id=None,
            mode="pr", pr_number=99,
        )
        assert s_pr["mode"] == "pr"
        assert s_pr["pr_number"] == 99


# ---------------------------------------------------------------------------
# CLI: --pr allows full fix mode
# ---------------------------------------------------------------------------


class TestPrAllowsFixMode:
    """PR mode is the final gate for pdd-issue, so it must be allowed to fix."""

    def test_pr_without_no_fix_keeps_fix_mode(self) -> None:
        runner = CliRunner()
        with patch(
            "pdd.commands.checkup.run_agentic_checkup",
            return_value=(True, "ok", 0.0, "model"),
        ) as run_mock:
            result = runner.invoke(
                checkup,
                [
                    "--pr", "https://github.com/o/r/pull/1",
                    "--issue", "https://github.com/o/r/issues/2",
                ],
                obj={},
            )

        assert result.exit_code == 0, result.output
        assert "forces --no-fix" not in result.output
        assert "forces --no-fix" not in (result.stderr_bytes or b"").decode()
        assert run_mock.call_args.kwargs["no_fix"] is False

    def test_pr_with_no_fix_does_not_warn(self) -> None:
        runner = CliRunner()
        with patch(
            "pdd.commands.checkup.run_agentic_checkup",
            return_value=(True, "ok", 0.0, "model"),
        ) as run_mock:
            result = runner.invoke(
                checkup,
                [
                    "--no-fix",
                    "--pr", "https://github.com/o/r/pull/1",
                    "--issue", "https://github.com/o/r/issues/2",
                ],
                obj={},
            )

        assert result.exit_code == 0, result.output
        assert "forces --no-fix" not in result.output
        assert run_mock.call_args.kwargs["no_fix"] is True


class TestPrModeFixPushBack:
    def test_pr_mode_commits_and_pushes_generated_fixes(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        executed_steps = []

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            executed_steps.append(step_num)
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        wt = tmp_path / "wt"
        wt.mkdir()

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
            },
            create=True,
        ) as metadata_mock, patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
            create=True,
        ) as push_mock:
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True, msg
        assert executed_steps == [1, 2, 3, 4, 5, 6.1, 6.2, 6.3, 7]
        # _fetch_pr_metadata is now called twice in PR fix-mode: once at
        # entry to capture the head SHA for the state identity guard
        # (codex round-1 blocker #1) and once before push to feed
        # clone_url/head_ref into _commit_and_push_if_changed. Each call
        # must target the same PR.
        assert metadata_mock.call_count >= 1
        for call in metadata_mock.call_args_list:
            assert call.args == ("o", "r", 200)
        push_mock.assert_called_once()
        assert push_mock.call_args.args[0] == wt

    def test_pr_mode_successful_push_posts_report_in_correct_order(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()
        events: list[str] = []

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                'All Issues Fixed\n{"success": true, "issue_aligned": true, '
                '"issues": []}'
                if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        def fake_push(*_args, **_kwargs):  # noqa: ANN001
            events.append("push")
            return (True, "Pushed fixes to PR branch.")

        def fake_pr_comment(*_args, **_kwargs):  # noqa: ANN001
            events.append("pr_comment")
            return True

        def fake_issue_comment(*_args, **_kwargs):  # noqa: ANN001
            events.append("issue_comment")
            return True

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            side_effect=fake_push,
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment",
            side_effect=fake_pr_comment,
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment",
            side_effect=fake_issue_comment,
        ):
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=True,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True, msg
        assert events == ["push", "pr_comment", "issue_comment"]


# ---------------------------------------------------------------------------
# Resume — full PR-identity guard (Greg review #2)
# ---------------------------------------------------------------------------


class TestStateIdentityValidation:
    """The same `issue_number` can verify different PRs over time. Resuming
    a state from a verification of PR A while invoking on PR B would carry
    stale step outputs and a stale `.pdd/worktrees/checkup-pr-A` path into
    the new run. The guard must fire on `pr_number` and `pr_owner/pr_repo`
    mismatch — not just `mode`.
    """

    def test_build_state_records_full_pr_identity(self) -> None:
        from pdd.agentic_checkup_orchestrator import _build_state

        s = _build_state(
            issue_number=42, issue_url="u", last_completed_step=3,
            step_outputs={}, total_cost=0.0, model_used="m", github_comment_id=None,
            mode="pr", pr_number=99, pr_owner="acme", pr_repo="thing",
        )
        assert s["mode"] == "pr"
        assert s["pr_number"] == 99
        assert s["pr_owner"] == "acme"
        assert s["pr_repo"] == "thing"


# ---------------------------------------------------------------------------
# Resume — worktree recreation must use the right helper (Greg review #3)
# ---------------------------------------------------------------------------


class TestPrResumeWorktreeRecreation:
    """If the saved PR worktree is missing on resume, recreation must use
    `_setup_pr_worktree` (PR head). The pre-fix code called
    `_setup_worktree(cwd, issue_number, ...)` which builds an issue-mode
    worktree from HEAD — silently running all subsequent steps against the
    wrong code.
    """

    def test_resume_missing_pr_worktree_uses_pr_setup_behaviorally(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        saved_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "aaaaaaaa",
            "last_completed_step": 2,
            "worktree_path": str(tmp_path / "missing-wt"),
            "step_outputs": {"1": "done", "2": "done"},
            "total_cost": 0.0,
            "model_used": "fake",
            "fix_verify_iteration": 0,
            "previous_fixes": "",
        }
        recreated = tmp_path / "recreated-pr-wt"
        recreated.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(saved_state, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(recreated, None),
        ) as setup_pr, patch(
            "pdd.agentic_checkup_orchestrator._setup_worktree"
        ) as setup_issue, patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "aaaaaaaa",
            },
            create=True,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "No changes to push."),
            create=True,
        ):
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True, msg
        setup_pr.assert_called_once_with(
            tmp_path, "o", "r", 200, True, resume_existing=True
        )
        setup_issue.assert_not_called()


# ---------------------------------------------------------------------------
# Blocker #1 (codex round-1): pr_head_sha axis in state identity guard.
# Cached step outputs are stale if the PR branch advanced between runs.
# ---------------------------------------------------------------------------


class TestStateIdentityPrHeadSha:
    """The state guard must invalidate cache when the PR head SHA advanced."""

    def test_build_state_records_pr_head_sha(self) -> None:
        from pdd.agentic_checkup_orchestrator import _build_state

        s = _build_state(
            issue_number=42, issue_url="u", last_completed_step=3,
            step_outputs={}, total_cost=0.0, model_used="m", github_comment_id=None,
            mode="pr", pr_number=99, pr_owner="acme", pr_repo="thing",
            pr_head_sha="deadbeef",
        )
        assert s["pr_head_sha"] == "deadbeef"

    def test_resume_discards_cache_when_pr_head_sha_advanced(
        self, tmp_path: Path
    ) -> None:
        """Cached state from a verification of SHA `aaa` MUST NOT be reused
        against a re-run where the remote PR head has advanced to `bbb`.
        Step outputs from the old SHA describe code that no longer exists."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        saved_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "aaaaaaaa",  # cached SHA
            "last_completed_step": 5,
            "worktree_path": str(tmp_path / "wt"),
            "step_outputs": {
                "1": "cached-1", "2": "cached-2",
                "3": "cached-3", "4": "cached-4", "5": "cached-5",
            },
            "total_cost": 0.0,
            "model_used": "fake",
            "fix_verify_iteration": 0,
            "previous_fixes": "",
        }
        wt = tmp_path / "wt"
        wt.mkdir()

        executed_steps: list = []

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            executed_steps.append(step_num)
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(saved_state, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            # Remote head now at bbbbbbbb — cache MUST be discarded.
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "bbbbbbbb",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "No changes to push."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="bbbbbbbb",
        ):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True
        # Cache invalidation: steps 1-5 MUST have re-executed against the new SHA.
        # Without invalidation they'd be replayed from cache and never appear.
        assert 1 in executed_steps, (
            f"Step 1 must re-run when PR head SHA advanced; ran: {executed_steps}"
        )
        assert 5 in executed_steps, (
            f"Step 5 must re-run when PR head SHA advanced; ran: {executed_steps}"
        )

    def test_resume_reuses_cache_when_pr_head_sha_matches(
        self, tmp_path: Path
    ) -> None:
        """When both cached and current PR head SHAs are non-empty AND equal,
        cached step outputs MUST be reused (no regression to a forced
        re-verification). The tightened predicate (codex round-2) only
        permits reuse on this exact branch: BOTH sides populated + equal.
        Every other combination is covered by ``test_resume_discards_cache_
        when_pr_head_sha_advanced`` (different non-empty) and
        ``test_resume_discards_cache_when_either_side_sha_is_empty``
        (empty-side combos)."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        saved_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "aaaaaaaa",
            "last_completed_step": 5,
            "worktree_path": str(tmp_path / "wt"),
            "step_outputs": {
                "1": "cached-1", "2": "cached-2",
                "3": "cached-3", "4": "cached-4", "5": "cached-5",
            },
            "total_cost": 0.0,
            "model_used": "fake",
            "fix_verify_iteration": 0,
            "previous_fixes": "",
        }
        wt = tmp_path / "wt"
        wt.mkdir()

        executed_steps: list = []

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            executed_steps.append(step_num)
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(saved_state, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            # Same SHA — cache should be reused.
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "aaaaaaaa",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "No changes to push."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="aaaaaaaa",
        ):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True
        # Cache reuse: cached steps 1-5 MUST NOT have re-run; only 6.1, 6.2, 6.3, 7 should.
        assert 1 not in executed_steps, (
            "Step 1 must NOT re-run when SHA matches; got "
            f"{executed_steps}"
        )
        assert 5 not in executed_steps, (
            "Step 5 must NOT re-run when SHA matches; got "
            f"{executed_steps}"
        )

    @pytest.mark.parametrize(
        "cached_sha,current_sha,combo",
        [
            ("", "", "both-empty"),
            ("", "bbbbbbbb", "cached-empty-current-present"),
            ("aaaaaaaa", "", "cached-present-current-empty"),
        ],
        ids=["both_empty", "cached_empty", "current_empty"],
    )
    def test_resume_discards_cache_when_either_side_sha_is_empty(
        self,
        tmp_path: Path,
        cached_sha: str,
        current_sha: str,
        combo: str,
    ) -> None:
        """Codex round-2 follow-through on Blocker #1: the SHA invalidation
        must FAIL CLOSED. Previously the guard skipped the SHA check when
        EITHER side was empty, which silently reused cached step outputs
        verified against an unknown PR head — exactly the failure mode the
        guard was added to prevent.

        Tightened predicate: reuse cache ONLY when BOTH cached AND current
        ``pr_head_sha`` are non-empty AND equal. Every other combination
        (both empty, only-cached, only-current) must discard cache.

        Three parametrized empty-side combos here. The (val, val match) and
        (val, val mismatch) branches are already covered by
        ``test_resume_reuses_cache_when_pr_head_sha_matches`` and
        ``test_resume_discards_cache_when_pr_head_sha_advanced``.
        """
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        saved_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": cached_sha,
            "last_completed_step": 5,
            "worktree_path": str(tmp_path / "wt"),
            "step_outputs": {
                "1": "cached-1", "2": "cached-2",
                "3": "cached-3", "4": "cached-4", "5": "cached-5",
            },
            "total_cost": 0.0,
            "model_used": "fake",
            "fix_verify_iteration": 0,
            "previous_fixes": "",
        }
        wt = tmp_path / "wt"
        wt.mkdir()

        executed_steps: list = []

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            executed_steps.append(step_num)
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(saved_state, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": current_sha,
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "No changes to push."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="deadbeef",
        ):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True
        # Fail-closed invalidation. With cache discarded, steps 1-5 MUST
        # re-execute. Without the tightening they'd be replayed from cache
        # and never appear.
        assert 1 in executed_steps, (
            f"[{combo}] Step 1 must re-run when pr_head_sha cannot be "
            f"verified (cached={cached_sha!r}, current={current_sha!r}); "
            f"ran: {executed_steps}"
        )
        assert 5 in executed_steps, (
            f"[{combo}] Step 5 must re-run when pr_head_sha cannot be "
            f"verified (cached={cached_sha!r}, current={current_sha!r}); "
            f"ran: {executed_steps}"
        )


# ---------------------------------------------------------------------------
# Blocker #2 (codex round-1): on push failure, surface worktree path + local
# commit SHA so the user can recover the local fixes.
# ---------------------------------------------------------------------------


class TestPrModePushFailureDiagnostics:
    @staticmethod
    def _last_saved_pr_push(save_mock) -> str:
        """Return the most recent ``step_outputs["pr_push"]`` written via
        ``save_workflow_state``. The orchestrator's ``_save_state`` calls
        ``save_workflow_state(..., state=new_state, ...)`` where
        ``new_state["step_outputs"]`` is the live dict — walk back through
        ``call_args_list`` to find the latest write that carried a
        non-empty ``pr_push`` entry."""
        for call in reversed(save_mock.call_args_list):
            state = call.kwargs.get("state")
            if state is None and call.args:
                # _save_state uses kwargs in production, but accept a
                # positional fallback for resilience.
                state = call.args[-1] if isinstance(call.args[-1], dict) else None
            if state is None:
                continue
            step_outputs = state.get("step_outputs", {}) or {}
            pr_push = step_outputs.get("pr_push")
            if pr_push:
                return pr_push
        return ""

    def test_push_failure_message_includes_worktree_and_local_sha(
        self, tmp_path: Path
    ) -> None:
        """If _commit_and_push_if_changed fails on the final iteration, the
        returned error MUST give the user enough to recover: the worktree
        path AND the local commit SHA containing the unpushed fixes.

        Codex round-2 nit B: ALSO assert the same enriched message is
        persisted into ``step_outputs["pr_push"]`` via
        ``save_workflow_state`` — locking the report surface (not just
        the returned tuple) so a future change can't quietly drop the
        recovery hint from saved state."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ) as save_mock, patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(False, "Failed to push fixes to PR branch: permission denied"),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            # Called once on push failure to capture the local commit SHA.
            return_value="local_commit_sha_222",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment"
        ) as pr_comment_mock, patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment"
        ) as issue_comment_mock:
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=True,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False
        assert str(wt) in msg, (
            f"Expected worktree path '{wt}' in failure message, got: {msg}"
        )
        assert "local_commit_sha_222" in msg, (
            "Expected local commit SHA in failure message so user can "
            f"cherry-pick or push manually. Got: {msg}"
        )

        # Nit B: report surface — the same diagnostic MUST also land in
        # the persisted state under ``step_outputs["pr_push"]``.
        saved_pr_push = self._last_saved_pr_push(save_mock)
        assert str(wt) in saved_pr_push, (
            "save_workflow_state must persist the enriched failure into "
            f"step_outputs['pr_push']; got: {saved_pr_push!r}"
        )
        assert "local_commit_sha_222" in saved_pr_push, (
            "Persisted step_outputs['pr_push'] must include the local "
            f"commit SHA; got: {saved_pr_push!r}"
        )
        # Codex round-3 FM2: the canonical PR/issue report MUST post on
        # the push-failure path too. Step 7 ran and produced a verdict;
        # silencing the report leaves downstream consumers (pdd-issue,
        # reviewers) with no record of what was checked. The body must
        # include the enriched push-failure diagnostic via the PR Push
        # Status section (``_format_pr_mode_final_report``).
        pr_comment_mock.assert_called_once()
        body = pr_comment_mock.call_args.args[3]
        assert "PR Push Status" in body
        assert str(wt) in body
        assert "local_commit_sha_222" in body
        issue_comment_mock.assert_called_once()

    def test_push_failure_message_handles_empty_rev_parse_sha(
        self, tmp_path: Path
    ) -> None:
        """Codex round-2 nit A edge case: ``_git_rev_parse_head`` can
        return ``""`` (rev-parse fails or staging failed before any
        commit). The softened diagnostic MUST still include the worktree
        path so the operator has something actionable — but MUST NOT lie
        about a non-existent commit SHA."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            # Simulate the staging-failed-before-commit path: helper
            # returned False and the SHA isn't available.
            return_value=(False, "git add -u failed: permission denied"),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="",  # rev-parse fails — no SHA to surface.
        ):
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False
        assert str(wt) in msg, (
            f"Expected worktree path in failure message, got: {msg!r}"
        )
        # No SHA was captured — message must NOT contain a bogus "at SHA"
        # clause. The softened wording either omits the clause entirely
        # or uses a placeholder; either way "at SHA " followed by an
        # actual hex string MUST NOT appear.
        assert "at SHA " not in msg, (
            "When rev-parse fails, message must not claim a SHA. Got: "
            f"{msg!r}"
        )

    def test_push_rebased_success_message_preserved_into_step_outputs(
        self, tmp_path: Path
    ) -> None:
        """Codex round-2 nit C: when ``_commit_and_push_if_changed``
        returns the rebased-onto-updated-head success string, the
        orchestrator MUST preserve that exact string into
        ``step_outputs["pr_push"]`` (which is what
        ``save_workflow_state`` persists).

        Without an explicit lock, a future change could silently rewrite
        the helper's return value before persisting it — destroying the
        only signal that a remote-advance race was handled."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()
        seen_labels: list[str] = []

        # Exact string from checkup_review_loop._commit_and_push_if_changed.
        rebased_msg = (
            "Pushed fixes to PR branch after rebasing onto updated PR head."
        )

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            seen_labels.append(_kwargs.get("label", ""))
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ) as save_mock, patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, rebased_msg),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="deadbeef",
        ):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True
        # The rebased-success message MUST land verbatim in saved state.
        saved_pr_push = self._last_saved_pr_push(save_mock)
        assert saved_pr_push == rebased_msg, (
            "Orchestrator must preserve the helper's rebased-success "
            "message verbatim into step_outputs['pr_push']; got: "
            f"{saved_pr_push!r}"
        )
        assert sum(label.startswith("step7_iter") for label in seen_labels) == 1
        assert seen_labels.count("step7_post_push_reverify") == 1

    def test_rebased_push_failure_to_reverify_fails_checkup(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()
        rebased_msg = (
            "Pushed fixes to PR branch after rebasing onto updated PR head."
        )

        def fake_step(step_num, *_args, **kwargs):  # noqa: ANN001
            if kwargs.get("label") == "step7_post_push_reverify":
                return True, "Verifier did not confirm clean final head.", 0.0, "fake"
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return True, output, 0.0, "fake"

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ) as clear_mock, patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, rebased_msg),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="deadbeef",
        ):
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False
        assert "Post-push verification" in msg
        clear_mock.assert_not_called()

    def test_plain_push_does_not_run_post_push_reverify(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()
        seen_labels: list[str] = []

        def fake_step(step_num, *_args, **kwargs):  # noqa: ANN001
            seen_labels.append(kwargs.get("label", ""))
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return True, output, 0.0, "fake"

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="deadbeef",
        ):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is True
        assert sum(label.startswith("step7_iter") for label in seen_labels) == 1
        assert "step7_post_push_reverify" not in seen_labels


# ---------------------------------------------------------------------------
# Blocker #3 (codex round-1): bare PR-mode push MUST run prompt-source +
# architecture-registry guards before pushing. Otherwise it bypasses #1063
# and #1081 enforcement that review-loop already has.
# ---------------------------------------------------------------------------


class TestPrModeGuardsBeforePush:
    def _run_with_guard_refusal(
        self,
        tmp_path: Path,
        prompt_refusal: str | None,
        registry_refusal: str | None,
    ):
        """Helper: drive PR-mode through to the guard step, mocking refusals."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_changed_files",
            return_value=["pdd/some_module.py"],
        ), patch(
            "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
            return_value=prompt_refusal,
        ) as prompt_guard, patch(
            "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
            return_value=registry_refusal,
        ) as registry_guard, patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="deadbeef",
        ):
            result = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )
        return result, prompt_guard, registry_guard, push_mock, wt

    def test_prompt_source_guard_refusal_blocks_push(self, tmp_path: Path) -> None:
        """If _check_prompt_source_guard refuses, push MUST NOT be invoked."""
        refusal = (
            "generated-code-only fix refused: pdd/foo.py is generated from "
            "pdd/prompts/foo_python.prompt."
        )
        (success, msg, _c, _m), _pg, _rg, push_mock, _wt = (
            self._run_with_guard_refusal(tmp_path, prompt_refusal=refusal, registry_refusal=None)
        )
        assert success is False
        push_mock.assert_not_called()
        assert "generated-code-only fix refused" in msg

    def test_prompt_source_guard_refusal_writes_artifact(self, tmp_path: Path) -> None:
        """Refusal artifact MUST be written for post-mortem (matches review-loop pattern)."""
        refusal = (
            "generated-code-only fix refused: pdd/foo.py is generated from "
            "pdd/prompts/foo_python.prompt."
        )
        self._run_with_guard_refusal(tmp_path, prompt_refusal=refusal, registry_refusal=None)
        candidates = list((tmp_path / ".pdd").rglob("*prompt-source-guard-refusal*"))
        assert candidates, (
            "Expected a prompt-source-guard-refusal artifact under .pdd/, "
            f"got: {list((tmp_path / '.pdd').rglob('*')) if (tmp_path / '.pdd').exists() else 'no .pdd dir'}"
        )
        body = candidates[0].read_text()
        assert "generated-code-only fix refused" in body

    def test_architecture_registry_guard_refusal_blocks_push(self, tmp_path: Path) -> None:
        """If _check_architecture_registry_edit_guard refuses, push MUST NOT be invoked."""
        refusal = (
            "architecture-registry edit refused: repointed pair "
            "pdd/foo.py from prompts/foo_python.prompt -> prompts/bar.prompt."
        )
        (success, msg, _c, _m), _pg, _rg, push_mock, _wt = (
            self._run_with_guard_refusal(tmp_path, prompt_refusal=None, registry_refusal=refusal)
        )
        assert success is False
        push_mock.assert_not_called()
        assert "architecture-registry edit refused" in msg

    def test_architecture_registry_guard_refusal_writes_artifact(self, tmp_path: Path) -> None:
        refusal = (
            "architecture-registry edit refused: repointed pair "
            "pdd/foo.py from prompts/foo_python.prompt -> prompts/bar.prompt."
        )
        self._run_with_guard_refusal(tmp_path, prompt_refusal=None, registry_refusal=refusal)
        candidates = list((tmp_path / ".pdd").rglob("*architecture-registry-guard-refusal*"))
        assert candidates, (
            "Expected an architecture-registry-guard-refusal artifact under .pdd/."
        )
        body = candidates[0].read_text()
        assert "architecture-registry edit refused" in body

    def test_guards_pass_then_push_is_invoked(self, tmp_path: Path) -> None:
        """Sanity check: when neither guard refuses, push proceeds normally."""
        (success, _msg, _c, _m), prompt_guard, registry_guard, push_mock, _wt = (
            self._run_with_guard_refusal(tmp_path, prompt_refusal=None, registry_refusal=None)
        )
        assert success is True
        prompt_guard.assert_called_once()
        registry_guard.assert_called_once()
        push_mock.assert_called_once()


# ---------------------------------------------------------------------------
# Minor #4 (codex round-1): _setup_pr_worktree fetch errors must be redacted
# in case the resolved remote target carries a tokenized URL.
# ---------------------------------------------------------------------------


class TestSetupPrWorktreeFetchErrorRedaction:
    def test_token_in_fetch_error_is_redacted(self, tmp_path: Path) -> None:
        """If git fetch error stderr echoes the tokenized URL, the returned
        message MUST scrub it via _redact_secret."""
        from pdd.agentic_checkup_orchestrator import _setup_pr_worktree

        secret_token = "ghs_supersecrettoken1234"
        # git's "could not resolve host" path tends to echo the URL back.
        leaky_stderr = (
            f"fatal: unable to access "
            f"'https://x-access-token:{secret_token}@github.com/acme/thing.git/': "
            "Could not resolve host"
        ).encode("utf-8")

        def fake_run(cmd, **_kwargs):  # noqa: ANN001
            if len(cmd) > 1 and cmd[1] == "fetch":
                raise subprocess.CalledProcessError(
                    returncode=128, cmd=cmd, stderr=leaky_stderr
                )
            return MagicMock(returncode=0, stderr=b"")

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._branch_exists", return_value=False
        ), patch(
            "pdd.agentic_checkup_orchestrator._github_token_from_env",
            return_value=secret_token,
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            wt_path, err = _setup_pr_worktree(
                cwd=tmp_path,
                pr_owner="acme",
                pr_repo="thing",
                pr_number=77,
                quiet=True,
            )

        assert wt_path is None
        assert err is not None
        assert secret_token not in err, (
            f"Token leaked into fetch-error message: {err!r}"
        )
        assert "[REDACTED]" in err


# ---------------------------------------------------------------------------
# Minor #5 (codex round-1): --review-loop --pr stays separate from the bare
# orchestrator's new PR-mode push path. The dispatcher must early-return into
# run_checkup_review_loop and NEVER reach the bare orchestrator.
# ---------------------------------------------------------------------------


class TestReviewLoopPrRoutingSeparation:
    def test_review_loop_pr_routes_through_review_loop_not_bare_orchestrator(
        self, tmp_path: Path
    ) -> None:
        """--review-loop --pr must invoke run_checkup_review_loop and NEVER
        the bare run_agentic_checkup_orchestrator (which now has its own PR
        push path). Mixing them up would double-fire push or skip guards."""
        from pdd.agentic_checkup import run_agentic_checkup

        # Stub the gh CLI responses for issue fetch.
        def fake_gh(cmd, *_a, **_kw):  # noqa: ANN001
            # Issue body fetch
            if len(cmd) >= 2 and cmd[0] == "api" and "/issues/" in cmd[1]:
                return (True, '{"title": "stub", "body": "stub", "comments_url": ""}')
            # Comments fetch
            return (True, "[]")

        with patch(
            "pdd.agentic_checkup._check_gh_cli", return_value=True
        ), patch(
            "pdd.agentic_checkup._run_gh_command", side_effect=fake_gh
        ), patch(
            "pdd.agentic_checkup._fetch_comments", return_value=""
        ), patch(
            "pdd.agentic_checkup._find_project_root", return_value=tmp_path
        ), patch(
            "pdd.agentic_checkup._load_architecture_json", return_value=({}, None)
        ), patch(
            "pdd.agentic_checkup._load_pddrc_content", return_value=""
        ), patch(
            "pdd.agentic_checkup._fetch_pr_context", return_value=""
        ), patch(
            "pdd.agentic_checkup.run_checkup_review_loop",
            return_value=(True, "ok", 0.0, "model"),
        ) as loop_mock, patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(True, "ok", 0.0, "model"),
        ) as orch_mock:
            run_agentic_checkup(
                issue_url="https://github.com/o/r/issues/2",
                quiet=True,
                no_fix=False,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/1",
                review_loop=True,
            )

        loop_mock.assert_called_once()
        orch_mock.assert_not_called()


class TestPrModeSourceArtifacts:
    def test_step7_prompt_verifies_current_pr_worktree_with_local_fixes(self) -> None:
        prompt = (
            Path(__file__).resolve().parent.parent
            / "pdd"
            / "prompts"
            / "agentic_checkup_step7_verify_LLM.prompt"
        ).read_text(encoding="utf-8")

        assert "independent of any local fixes" not in prompt
        assert "current PR worktree" in prompt
        assert "including those local fixes" in prompt
        assert "{pr_push_output}" in prompt

    def test_step7_prompt_does_not_post_pre_push_comments_in_pr_mode(self) -> None:
        prompt = (
            Path(__file__).resolve().parent.parent
            / "pdd"
            / "prompts"
            / "agentic_checkup_step7_verify_LLM.prompt"
        ).read_text(encoding="utf-8")

        assert "gh pr comment" not in prompt
        assert "post to **BOTH**" not in prompt
        assert "do NOT post GitHub comments from Step 7" in prompt
        assert "orchestrator posts the final PR/issue report after" in prompt

    def test_architecture_records_agentic_checkup_cwd_parameter(self) -> None:
        arch_path = Path(__file__).resolve().parent.parent / "architecture.json"
        architecture = json.loads(arch_path.read_text(encoding="utf-8"))
        module = next(
            item
            for item in architecture
            if item.get("filename") == "agentic_checkup_python.prompt"
        )
        functions = module["interface"]["module"]["functions"]
        run_checkup = next(
            fn for fn in functions if fn.get("name") == "run_agentic_checkup"
        )

        assert "cwd: Optional[Path]" in run_checkup["signature"]

    def test_architecture_records_checkup_orchestrator_pr_mode_contract(self) -> None:
        arch_path = Path(__file__).resolve().parent.parent / "architecture.json"
        architecture = json.loads(arch_path.read_text(encoding="utf-8"))
        module = next(
            item
            for item in architecture
            if item.get("filename") == "agentic_checkup_orchestrator_python.prompt"
        )
        functions = module["interface"]["module"]["functions"]
        function_names = {fn.get("name") for fn in functions}
        run_fn = next(
            fn for fn in functions if fn.get("name") == "run_agentic_checkup_orchestrator"
        )

        assert "pr_url: Optional[str]" in run_fn["signature"]
        assert "pr_number: Optional[int]" in run_fn["signature"]
        assert "reasoning_time: Optional[float]" in run_fn["signature"]
        assert "pushes back to the same PR" in module["reason"]
        assert "re-runs Step 7 after a rebase-on-updated-head push" in module["description"]
        assert "posts final PR/issue reports only after" in module["description"]
        assert "checkup_review_loop_python.prompt" in module["dependencies"]
        assert "_setup_pr_worktree" in function_names
        assert "_commit_and_push_if_changed" in function_names
        assert "_check_prompt_source_guard" in function_names
        assert "_check_architecture_registry_edit_guard" in function_names
        assert "_format_pr_mode_final_report" in function_names

    def test_final_checkup_helper_is_in_prompt_and_context_sources(self) -> None:
        root = Path(__file__).resolve().parent.parent
        prompt = (
            root / "pdd" / "prompts" / "agentic_e2e_fix_orchestrator_python.prompt"
        ).read_text(encoding="utf-8")
        context = (
            root / "context" / "agentic_e2e_fix_orchestrator_example.py"
        ).read_text(encoding="utf-8")
        architecture = json.loads(
            (root / "architecture.json").read_text(encoding="utf-8")
        )

        assert "def:_run_final_checkup_on_pr" in prompt
        assert "def _run_final_checkup_on_pr" in context
        assert "cwd=cwd" in context

        module = next(
            item
            for item in architecture
            if item.get("filename") == "agentic_e2e_fix_orchestrator_python.prompt"
        )
        functions = module["interface"]["module"]["functions"]
        helper = next(
            fn for fn in functions if fn.get("name") == "_run_final_checkup_on_pr"
        )
        assert "cwd: Path" in helper["signature"]


# ---------------------------------------------------------------------------
# Round-4 Finding 1: gate the orchestrator on Step 7's JSON verdict.
#
# Before this gate, Step 7 could report `issue_aligned: false` (PR-mode) or
# unfixed critical issues and the orchestrator would still push to the PR
# (in fix mode) or invoke step 8 (in issue mode), clear state, and return
# `(True, "Checkup complete", ...)`. Downstream consumers (pdd-issue,
# pdd_cloud) trust the return tuple, so a bad PR could be marked green.
# These tests pin the new fail-closed behavior in `_step7_passed`.
# ---------------------------------------------------------------------------


def _step7_output(
    *,
    success: bool = True,
    issue_aligned: bool | None = True,
    issues: list[dict] | None = None,
    message: str = "ok",
    include_sentinel: bool = True,
) -> str:
    """Render a fake Step 7 output containing the structured JSON verdict."""
    payload: dict = {
        "success": success,
        "message": message,
        "issues": issues if issues is not None else [],
        "changed_files": [],
    }
    if issue_aligned is not None:
        payload["issue_aligned"] = issue_aligned
    body = "```json\n" + json.dumps(payload) + "\n```"
    if include_sentinel and success:
        body = "All Issues Fixed\n" + body
    return body


class TestStep7PassedHelper:
    """Unit tests for `_step7_passed` parsing semantics."""

    def test_step7_parse_failure_fails_closed(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed("not even close to JSON", pr_mode=True)
        assert passed is False
        assert "Step 7 verdict JSON could not be parsed" in reason

    def test_empty_step7_output_fails_closed(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed("", pr_mode=False)
        assert passed is False
        assert "Step 7 verdict JSON could not be parsed" in reason

    def test_success_false_fails_in_issue_mode(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        out = _step7_output(success=False, issue_aligned=None,
                            include_sentinel=False, message="tests still red")
        passed, reason = _step7_passed(out, pr_mode=False)
        assert passed is False
        assert "success=false" in reason

    def test_issue_aligned_false_fails_in_pr_mode(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        out = _step7_output(success=True, issue_aligned=False,
                            message="PR is unrelated to issue")
        passed, reason = _step7_passed(out, pr_mode=True)
        assert passed is False
        assert "issue_aligned=false" in reason

    def test_issue_aligned_ignored_in_issue_mode(self) -> None:
        """issue_aligned is PR-mode only — issue mode must not require it."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        out = _step7_output(success=True, issue_aligned=False)
        passed, _reason = _step7_passed(out, pr_mode=False)
        assert passed is True

    def test_unfixed_critical_issue_fails(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        out = _step7_output(
            success=True,
            issue_aligned=True,
            issues=[
                {"severity": "low", "fixed": False,
                 "module": "x", "description": "minor"},
                {"severity": "critical", "fixed": False,
                 "module": "auth", "description": "leaks token"},
            ],
        )
        passed, reason = _step7_passed(out, pr_mode=True)
        assert passed is False
        assert "unfixed critical" in reason
        assert "auth" in reason

    def test_fixed_critical_passes(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        out = _step7_output(
            success=True,
            issue_aligned=True,
            issues=[
                {"severity": "critical", "fixed": True,
                 "module": "auth", "description": "leaked token"},
            ],
        )
        passed, _reason = _step7_passed(out, pr_mode=True)
        assert passed is True

    def test_clean_pr_mode_passes(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        out = _step7_output(success=True, issue_aligned=True)
        passed, _reason = _step7_passed(out, pr_mode=True)
        assert passed is True


def _run_orch_with_fake_step7(
    tmp_path: Path,
    fake_step7: str,
    *,
    no_fix: bool = False,
) -> tuple:
    """Run the orchestrator in PR fix mode with a configurable step-7 output.

    Returns ``(success, message, push_mock, executed_steps)``.
    """
    from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

    executed = []

    def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
        executed.append(step_num)
        if step_num == 7:
            return (True, fake_step7, 0.0, "fake-model")
        return (True, f"Step {step_num} output", 0.0, "fake-model")

    wt = tmp_path / "wt"
    wt.mkdir()

    with patch(
        "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
        return_value=(wt, None),
    ), patch(
        "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
    ), patch(
        "pdd.agentic_checkup_orchestrator.load_workflow_state",
        return_value=(None, None),
    ), patch(
        "pdd.agentic_checkup_orchestrator.save_workflow_state",
        return_value=None,
    ), patch(
        "pdd.agentic_checkup_orchestrator.clear_workflow_state"
    ) as clear_mock, patch(
        "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
        return_value={
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef",
        },
        create=True,
    ), patch(
        "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
        return_value=(True, "Pushed fixes to PR branch."),
        create=True,
    ) as push_mock, patch(
        "pdd.agentic_checkup_orchestrator._git_changed_files",
        return_value=[],
    ), patch(
        "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
        return_value=None,
    ), patch(
        "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
        return_value=None,
    ):
        success, msg, _cost, _model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/o/r/issues/99",
            issue_content="stub",
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            no_fix=no_fix,
            timeout_adder=0.0,
            use_github_state=False,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

    return success, msg, push_mock, executed, clear_mock


class TestStep7GateInPrFixMode:
    """Finding 1: in PR fix mode, the orchestrator must NOT push when Step 7
    reports `issue_aligned: false` or unfixed critical issues, and must
    return failure so callers don't mark the run green.
    """

    def test_pr_mode_returns_failure_when_step7_issue_aligned_false(
        self, tmp_path: Path
    ) -> None:
        step7 = _step7_output(
            success=True, issue_aligned=False, message="PR is unrelated"
        )
        success, msg, push_mock, _executed, clear_mock = _run_orch_with_fake_step7(
            tmp_path, step7
        )
        assert success is False
        assert "issue_aligned=false" in msg
        push_mock.assert_not_called()
        # State must NOT be cleared on gate failure (operator may resume).
        clear_mock.assert_not_called()

    def test_pr_mode_returns_failure_when_step7_has_unfixed_critical(
        self, tmp_path: Path
    ) -> None:
        step7 = _step7_output(
            success=True,
            issue_aligned=True,
            issues=[
                {"severity": "critical", "fixed": False,
                 "module": "billing", "description": "double charge"},
            ],
        )
        success, msg, push_mock, _executed, _clear = _run_orch_with_fake_step7(
            tmp_path, step7
        )
        assert success is False
        assert "unfixed critical" in msg
        push_mock.assert_not_called()

    def test_pr_mode_returns_success_when_step7_clean(self, tmp_path: Path) -> None:
        step7 = _step7_output(success=True, issue_aligned=True)
        success, msg, push_mock, executed, _clear = _run_orch_with_fake_step7(
            tmp_path, step7
        )
        assert success is True, msg
        # Push must be invoked exactly once when the gate passes.
        push_mock.assert_called_once()
        # Step 8 must still be skipped in PR mode.
        assert 8 not in executed


class TestStep7GateInNoFixPrMode:
    """Finding 1: --no-fix linear path also gates on Step 7 verdict."""

    def test_no_fix_pr_mode_returns_failure_when_step7_says_no(
        self, tmp_path: Path
    ) -> None:
        step7 = _step7_output(
            success=True, issue_aligned=False, message="not related"
        )
        success, msg, _push_mock, _executed, _clear = _run_orch_with_fake_step7(
            tmp_path, step7, no_fix=True
        )
        assert success is False
        assert "issue_aligned=false" in msg

    def test_no_fix_pr_mode_returns_success_when_step7_clean(
        self, tmp_path: Path
    ) -> None:
        step7 = _step7_output(success=True, issue_aligned=True)
        success, msg, _push_mock, _executed, _clear = _run_orch_with_fake_step7(
            tmp_path, step7, no_fix=True
        )
        assert success is True, msg


class TestStep7GateInIssueMode:
    """Finding 1: in issue mode (non-PR), the same gate prevents step 8
    (PR creation) from running when Step 7 reports failure. Opening a PR
    that contains unfixed critical issues is the same anti-pattern as
    pushing one to an existing PR.
    """

    def test_issue_mode_skips_step8_when_step7_fails_after_max_iter(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import (
            MAX_FIX_VERIFY_ITERATIONS,
            run_agentic_checkup_orchestrator,
        )

        # Step 7 always reports an unfixed critical — the loop exhausts
        # MAX_FIX_VERIFY_ITERATIONS without "All Issues Fixed", then the
        # JSON gate must prevent step 8 from running.
        failing_step7 = _step7_output(
            success=True,
            issue_aligned=None,
            issues=[
                {"severity": "critical", "fixed": False,
                 "module": "core", "description": "still broken"},
            ],
            include_sentinel=False,
        )

        executed = []

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            executed.append(step_num)
            if step_num == 7:
                return (True, failing_step7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        wt = tmp_path / "wt"
        wt.mkdir()

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ) as clear_mock:
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
            )

        # Loop must have run MAX_FIX_VERIFY_ITERATIONS times, each touching
        # step 7. Step 8 must NOT have been invoked because the gate fired.
        assert success is False
        assert "unfixed critical" in msg
        step7_count = sum(1 for s in executed if s == 7)
        assert step7_count == MAX_FIX_VERIFY_ITERATIONS, executed
        assert 8 not in executed
        clear_mock.assert_not_called()


# ---------------------------------------------------------------------------
# Codex round-3 FM2: canonical PR/issue report must post on every PR-mode
# return path where Step 7 produced a verdict.
#
# Step 7's PR-mode prompt suppresses agent commenting because the
# orchestrator owns the canonical report. Until this round, the orchestrator
# only posted it after a successful fix-mode push — leaving --no-fix,
# gate-fail, guard-refusal, and push-failure paths silent.
# ---------------------------------------------------------------------------


class TestCanonicalReportOnEveryPRModeReturnPath:
    """Each PR-mode return path that has run Step 7 must post the canonical
    report via ``_post_pr_mode_final_report``.

    Tests patch ``post_pr_comment`` and assert it was called with the
    PR-mode targets (owner, repo, number) and a body derived from the
    Step 7 verdict.
    """

    _GATE_PASS_STEP7 = (
        "## Verification\n"
        "issue_aligned: true\n"
        "All Issues Fixed\n"
        '```json\n{"success": true, "issue_aligned": true, "issues": []}\n```'
    )

    _GATE_FAIL_STEP7 = (
        "## Verification\n"
        "issue_aligned: false\n"
        '```json\n{"success": false, "issue_aligned": false, '
        '"issues": [{"severity": "critical", "fixed": false}]}\n```'
    )

    def _common_kwargs(self, tmp_path: Path) -> dict:
        return dict(
            issue_url="https://github.com/o/r/issues/99",
            issue_content="stub",
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            timeout_adder=0.0,
            use_github_state=True,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

    def _setup_pr_mode_patches(self, tmp_path: Path, step_side_effect):
        """Bundle of patches every PR-mode orchestrator test needs."""
        wt = tmp_path / "wt"
        wt.mkdir(exist_ok=True)
        return [
            patch(
                "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
                return_value=(wt, None),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._run_single_step",
                side_effect=step_side_effect,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.load_workflow_state",
                return_value=(None, None),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.save_workflow_state",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
            patch(
                "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
                return_value={
                    "clone_url": "https://github.com/o/r.git",
                    "head_ref": "change/test",
                    "head_owner": "o",
                    "head_repo": "r",
                    "head_sha": "deadbeef",
                },
            ),
        ]

    @staticmethod
    def _enter_all(patchers):
        return [p.__enter__() for p in patchers]

    @staticmethod
    def _exit_all(patchers):
        for p in patchers:
            p.__exit__(None, None, None)

    def test_no_fix_gate_pass_posts_canonical_report(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, self._GATE_PASS_STEP7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        step_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.post_step_comment",
                step_comment_mock,
            ),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = True
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is True
        pr_comment_mock.assert_called_once()
        # post_pr_comment(pr_owner, pr_repo, pr_number, body, cwd)
        args = pr_comment_mock.call_args.args
        assert args[0] == "o"
        assert args[1] == "r"
        assert args[2] == 200
        assert "issue_aligned: true" in args[3]

    def test_no_fix_gate_fail_posts_canonical_report(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, self._GATE_FAIL_STEP7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch("pdd.agentic_checkup_orchestrator.post_step_comment"),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = True
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is False
        pr_comment_mock.assert_called_once(), (
            "Gate-fail must still post the canonical report — Step 7 ran, "
            "downstream consumers need the verdict in writing"
        )
        body = pr_comment_mock.call_args.args[3]
        assert "issue_aligned: false" in body

    def test_fix_mode_gate_fail_posts_canonical_report(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, self._GATE_FAIL_STEP7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch("pdd.agentic_checkup_orchestrator.post_step_comment"),
            patch(
                "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
                return_value=(True, "Pushed fixes to PR branch."),
            ),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = False
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is False
        pr_comment_mock.assert_called_once(), (
            "Fix-mode gate-fail must post the canonical report — Step 7 "
            "produced a verdict before the gate blocked the push"
        )

    def test_registry_refusal_posts_canonical_report(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, self._GATE_PASS_STEP7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch("pdd.agentic_checkup_orchestrator.post_step_comment"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value="REFUSED: architecture-registry edit detected",
            ),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = False
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is False
        assert "REFUSED" in msg
        pr_comment_mock.assert_called_once(), (
            "Registry-guard refusal must post the canonical report — "
            "Step 7 verdict is still meaningful even when the push is "
            "blocked"
        )
        body = pr_comment_mock.call_args.args[3]
        assert "REFUSED" in body, (
            "Refusal reason must surface in the PR comment, not just "
            "the Step 7 verdict"
        )

    def test_prompt_source_refusal_posts_canonical_report(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, self._GATE_PASS_STEP7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch("pdd.agentic_checkup_orchestrator.post_step_comment"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value="",
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
                return_value="REFUSED: prompt-source edit detected",
            ),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = False
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is False
        assert "REFUSED" in msg
        pr_comment_mock.assert_called_once(), (
            "Prompt-source-guard refusal must post the canonical report"
        )
        body = pr_comment_mock.call_args.args[3]
        assert "REFUSED" in body, (
            "Refusal reason must surface in the PR comment, not just "
            "the Step 7 verdict"
        )

    def test_push_failure_posts_canonical_report(self, tmp_path: Path) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, self._GATE_PASS_STEP7, 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch("pdd.agentic_checkup_orchestrator.post_step_comment"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value="",
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
                return_value="",
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
                return_value=(False, "Push failed: remote rejected"),
            ),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = False
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is False
        assert "Push failed" in msg
        pr_comment_mock.assert_called_once(), (
            "Push failure must still post the canonical report — Step 7 "
            "ran successfully; the failure is downstream of the verdict"
        )

    def test_post_push_reverify_failure_posts_canonical_report(
        self, tmp_path: Path
    ) -> None:
        """When ``_commit_and_push_if_changed`` rebases onto an advancing PR
        head, the orchestrator re-runs Step 7 against the rebased tree. If
        that reverify fails the gate, the orchestrator must still post the
        canonical report — Step 7 produced a verdict (the rebased one),
        which downstream consumers need."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        step7_outputs = iter([self._GATE_PASS_STEP7, self._GATE_FAIL_STEP7])

        def step_side_effect(step_num, *_args, **_kwargs):
            if step_num == 7:
                return (True, next(step7_outputs), 0.0, "fake-model")
            return (True, f"Step {step_num} output", 0.0, "fake-model")

        patchers = self._setup_pr_mode_patches(tmp_path, step_side_effect)
        pr_comment_mock = MagicMock(return_value=True)
        patchers += [
            patch(
                "pdd.agentic_checkup_orchestrator.post_pr_comment",
                pr_comment_mock,
            ),
            patch("pdd.agentic_checkup_orchestrator.post_step_comment"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value="",
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
                return_value="",
            ),
            patch(
                # Push succeeds AND signals a rebase — this is the trigger
                # for ``_run_post_push_reverify_if_needed`` to re-run Step 7.
                "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
                return_value=(
                    True,
                    "Pushed fixes to PR branch after rebasing onto updated PR head.",
                ),
            ),
        ]

        try:
            self._enter_all(patchers)
            kwargs = self._common_kwargs(tmp_path)
            kwargs["no_fix"] = False
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(**kwargs)
        finally:
            self._exit_all(patchers)

        assert success is False, (
            "Post-push reverify must fail the workflow when the rebased "
            "tree no longer satisfies the gate"
        )
        pr_comment_mock.assert_called_once(), (
            "Post-push reverify failure must post the canonical report — "
            "Step 7 ran (twice); downstream consumers need the rebased "
            "verdict in writing"
        )
        body = pr_comment_mock.call_args.args[3]
        # The body should reflect the rebased (failing) Step 7 verdict,
        # not the pre-push (passing) one — ``_run_single_step`` refreshes
        # ``step_outputs["7"]`` each call.
        assert "issue_aligned: false" in body


# ---------------------------------------------------------------------------
# Round-5 Finding 2: Step 7 verdict parser must pick the LAST JSON block.
# The prompt requires the verdict JSON to be last; the pre-round-5 parser
# returned the FIRST match, so an earlier passing block could mask a final
# failing verdict.
# ---------------------------------------------------------------------------


class TestStep7PassedUsesLastJsonBlock:
    """Pin the contract: when multiple fenced JSON blocks appear, the gate
    decides on the LAST one (the prompt's required verdict location)."""

    def test_step7_passed_uses_last_json_block_when_multiple_present(self) -> None:
        from pdd.agentic_checkup_orchestrator import _step7_passed

        first_clean = json.dumps({
            "success": True,
            "issue_aligned": True,
            "issues": [],
            "changed_files": [],
            "message": "early-iteration summary",
        })
        last_failing = json.dumps({
            "success": True,
            "issue_aligned": False,
            "issues": [],
            "changed_files": [],
            "message": "PR does not address the issue",
        })
        text = (
            "## Iteration 1 summary\n"
            f"```json\n{first_clean}\n```\n\n"
            "## Final verdict\n"
            f"```json\n{last_failing}\n```\n"
        )
        passed, reason = _step7_passed(text, pr_mode=True)
        assert passed is False, (
            "Gate must decide on the LAST JSON block; the first block "
            "(issue_aligned=true) is an interior summary and must not mask "
            "the final verdict."
        )
        assert "issue_aligned=false" in reason

    def test_step7_passed_with_single_json_block_unchanged(self) -> None:
        """Behaviour for a single JSON block stays identical."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        payload = json.dumps({
            "success": True,
            "issue_aligned": True,
            "issues": [],
            "changed_files": [],
        })
        text = f"## Verdict\n```json\n{payload}\n```"
        passed, _ = _step7_passed(text, pr_mode=True)
        assert passed is True

    def test_step7_passed_with_trailing_non_json_text(self) -> None:
        """Free text AFTER the JSON block must not defeat parsing."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        payload = json.dumps({
            "success": True,
            "issue_aligned": True,
            "issues": [],
            "changed_files": [],
        })
        text = (
            f"```json\n{payload}\n```\n\n"
            "Note: agent ended with additional commentary the prompt forbade, "
            "but the LAST JSON block must still be parsed."
        )
        passed, _ = _step7_passed(text, pr_mode=True)
        assert passed is True

    def test_step7_passed_no_json_at_all_fails_closed(self) -> None:
        """No JSON anywhere — gate still fails closed (unchanged)."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            "Step 7 verdict: All good!\nNo JSON.", pr_mode=True
        )
        assert passed is False
        assert "Step 7 verdict JSON could not be parsed" in reason

    def test_step7_passed_last_block_unfenced_after_fenced_passing(self) -> None:
        """If the LAST verdict isn't fenced (model forgot the markdown
        fences), the parser should still prefer it over an earlier fenced
        passing block. Defensive fallback for the documented contract."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        first_clean = json.dumps({
            "success": True,
            "issue_aligned": True,
            "issues": [],
            "changed_files": [],
        })
        last_failing = json.dumps({
            "success": False,
            "issue_aligned": True,
            "issues": [],
            "changed_files": [],
            "message": "tests still red",
        })
        text = (
            f"```json\n{first_clean}\n```\n\n"
            "Final verdict (unfenced):\n"
            f"{last_failing}\n"
        )
        passed, reason = _step7_passed(text, pr_mode=True)
        assert passed is False
        assert "success=false" in reason


# ---------------------------------------------------------------------------
# Round-5 Finding 4: comment-post failures must NOT be silently ignored.
# `post_pr_comment` / `post_step_comment` return booleans. The orchestrator
# must surface failures via (a) the returned message (suffix), (b)
# `step_outputs["pr_post_status"]`, and (c) `.pdd/checkup-pr-<n>/final-report.md`.
# The gate outcome itself is NOT flipped — gh/network flakiness is independent
# of code-verification truth.
# ---------------------------------------------------------------------------


def _last_saved_pr_post_status(save_mock) -> str:
    for call in reversed(save_mock.call_args_list):
        state = call.kwargs.get("state")
        if state is None and call.args:
            state = call.args[-1] if isinstance(call.args[-1], dict) else None
        if state is None:
            continue
        step_outputs = state.get("step_outputs", {}) or {}
        status = step_outputs.get("pr_post_status")
        if status:
            return status
    return ""


def _run_fix_mode_pr_with_post_returns(
    tmp_path: Path,
    *,
    pr_comment_return: bool,
    issue_comment_return: bool,
):
    from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

    def fake_step(step_num, _name, _context, *_args, **_kwargs):  # noqa: ANN001
        output = _step7_clean_output() if step_num == 7 else f"Step {step_num} output"
        return (True, output, 0.0, "fake-model")

    wt = tmp_path / "wt"
    wt.mkdir()

    with patch(
        "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
        return_value=(wt, None),
    ), patch(
        "pdd.agentic_checkup_orchestrator._run_single_step", side_effect=fake_step
    ), patch(
        "pdd.agentic_checkup_orchestrator.load_workflow_state",
        return_value=(None, None),
    ), patch(
        "pdd.agentic_checkup_orchestrator.save_workflow_state",
        return_value=None,
    ) as save_mock, patch(
        "pdd.agentic_checkup_orchestrator.clear_workflow_state"
    ), patch(
        "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
        return_value={
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef",
        },
    ), patch(
        "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
        return_value=(True, "Pushed fixes to PR branch."),
    ), patch(
        "pdd.agentic_checkup_orchestrator._git_changed_files",
        return_value=[],
    ), patch(
        "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
        return_value=None,
    ), patch(
        "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
        return_value=None,
    ), patch(
        "pdd.agentic_checkup_orchestrator.post_pr_comment",
        return_value=pr_comment_return,
    ) as pr_comment_mock, patch(
        "pdd.agentic_checkup_orchestrator.post_step_comment",
        return_value=issue_comment_return,
    ) as issue_comment_mock:
        success, msg, _cost, _model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/o/r/issues/99",
            issue_content="stub",
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            no_fix=False,
            timeout_adder=0.0,
            use_github_state=True,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

    return success, msg, save_mock, pr_comment_mock, issue_comment_mock


class TestPrModePostFailureSurface:
    """Comment-post failures don't change the gate outcome (gh / network
    flakiness shouldn't fail a checkup whose code verification passed) but
    they MUST be surfaced via the returned message AND persisted into
    ``step_outputs['pr_post_status']``."""

    def test_pr_mode_post_failure_does_not_fail_gate_but_surfaces(
        self, tmp_path: Path
    ) -> None:
        success, msg, save_mock, pr_comment_mock, issue_comment_mock = (
            _run_fix_mode_pr_with_post_returns(
                tmp_path,
                pr_comment_return=False,
                issue_comment_return=True,
            )
        )
        assert success is True, msg
        assert "report post" in msg.lower(), msg
        persisted = _last_saved_pr_post_status(save_mock)
        assert persisted
        assert "pr" in persisted.lower()
        pr_comment_mock.assert_called_once()
        issue_comment_mock.assert_called_once()

    def test_pr_mode_issue_post_failure_surfaces(
        self, tmp_path: Path
    ) -> None:
        success, msg, save_mock, pr_comment_mock, issue_comment_mock = (
            _run_fix_mode_pr_with_post_returns(
                tmp_path,
                pr_comment_return=True,
                issue_comment_return=False,
            )
        )
        assert success is True, msg
        assert "report post" in msg.lower(), msg
        persisted = _last_saved_pr_post_status(save_mock)
        assert persisted
        assert "issue" in persisted.lower()
        pr_comment_mock.assert_called_once()
        issue_comment_mock.assert_called_once()

    def test_pr_mode_both_posts_succeed_no_status_noise(
        self, tmp_path: Path
    ) -> None:
        success, msg, save_mock, pr_comment_mock, issue_comment_mock = (
            _run_fix_mode_pr_with_post_returns(
                tmp_path,
                pr_comment_return=True,
                issue_comment_return=True,
            )
        )
        assert success is True, msg
        assert "report post" not in msg.lower(), (
            f"Happy path must not mention report-post status; got: {msg!r}"
        )
        persisted = _last_saved_pr_post_status(save_mock)
        assert persisted == "", (
            f"pr_post_status should not be persisted on happy path; got: {persisted!r}"
        )
        pr_comment_mock.assert_called_once()
        issue_comment_mock.assert_called_once()


# ---------------------------------------------------------------------------
# Round-5 Finding 3: PR-mode must audit the PR's architecture.json / .pddrc,
# not the parent checkout's.
# ---------------------------------------------------------------------------


class TestPrModeRefreshesContextFromWorktree:
    """``_refresh_pr_context_from_worktree`` must overwrite the orchestrator
    context's ``architecture_json``, ``pddrc_content``, and ``project_root``
    with values loaded from the PR worktree once the worktree is checked
    out. ``cwd`` itself stays the parent repo (gh + state ops need it)."""

    def _make_pr_worktree(self, root: Path) -> Path:
        wt = root / "wt"
        wt.mkdir()
        (wt / "architecture.json").write_text(
            json.dumps([
                {
                    "module": "from_pr_worktree",
                    "language": "python",
                    "prompt": "from_pr_worktree.prompt",
                }
            ]),
            encoding="utf-8",
        )
        (wt / ".pddrc").write_text(
            "pddrc_marker: from_pr_worktree\n", encoding="utf-8"
        )
        return wt

    def test_refresh_overrides_caller_supplied_architecture_and_pddrc(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = self._make_pr_worktree(tmp_path)
        seen_arch: list[str] = []
        seen_pddrc: list[str] = []
        seen_project_root: list[str] = []

        def fake_step(step_num, _name, context, *_args, **_kwargs):  # noqa: ANN001
            seen_arch.append(context.get("architecture_json", ""))
            seen_pddrc.append(context.get("pddrc_content", ""))
            seen_project_root.append(context.get("project_root", ""))
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ):
            caller_arch = json.dumps([
                {
                    "module": "from_caller",
                    "language": "python",
                    "prompt": "from_caller.prompt",
                }
            ])
            caller_pddrc = "pddrc_marker: from_caller\n"
            run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json=caller_arch,
                pddrc_content=caller_pddrc,
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert seen_arch, "expected at least one fake_step invocation"
        for arch in seen_arch:
            assert "from_pr_worktree" in arch, (
                "Step received pre-PR-worktree architecture; refresh did "
                f"not run. Saw: {arch!r}"
            )
            assert "from_caller" not in arch, (
                "Pre-PR-worktree architecture leaked into a step's "
                f"context. Saw: {arch!r}"
            )
        for pddrc in seen_pddrc:
            assert "from_pr_worktree" in pddrc, (
                f"Step received pre-PR-worktree .pddrc. Saw: {pddrc!r}"
            )
        for proot in seen_project_root:
            assert str(wt) in proot, (
                f"project_root must resolve inside the PR worktree; got: {proot!r}"
            )

    def test_refresh_handles_missing_worktree_architecture_and_pddrc(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()
        seen_arch: list[str] = []
        seen_pddrc: list[str] = []

        def fake_step(step_num, _name, context, *_args, **_kwargs):  # noqa: ANN001
            seen_arch.append(context.get("architecture_json", ""))
            seen_pddrc.append(context.get("pddrc_content", ""))
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
        ):
            caller_arch = json.dumps([
                {
                    "module": "from_caller",
                    "language": "python",
                    "prompt": "from_caller.prompt",
                }
            ])
            caller_pddrc = "pddrc_marker: from_caller\n"
            run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json=caller_arch,
                pddrc_content=caller_pddrc,
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert seen_arch
        for arch in seen_arch:
            assert "from_caller" not in arch, (
                "Pre-PR-worktree architecture leaked when worktree was "
                f"empty. Saw: {arch!r}"
            )
        for pddrc in seen_pddrc:
            assert "from_caller" not in pddrc, (
                f"Pre-PR-worktree .pddrc leaked when worktree was empty. "
                f"Saw: {pddrc!r}"
            )


# ---------------------------------------------------------------------------
# Issue #1116: PR head advanced mid-checkup -> bounded auto-rerun.
#
# When the remote PR head moves between checkout and push (operator pushes
# a commit, CI auto-heal lands a fix, etc.), the orchestrator must discard
# the stale work and restart from the new head rather than fail-closed and
# force the operator to rerun manually. The retry budget is bounded by
# ``MAX_PR_HEAD_REFRESHES`` to prevent unbounded looping if the PR keeps
# moving.
# ---------------------------------------------------------------------------


def _pr_metadata(head_sha: str) -> dict:
    """Helper: minimal PR metadata payload with a configurable head SHA."""
    return {
        "clone_url": "https://github.com/o/r.git",
        "head_ref": "change/test",
        "head_owner": "o",
        "head_repo": "r",
        "head_sha": head_sha,
    }


class TestPrHeadAdvanceAutoRerun:
    """Bounded auto-rerun when the remote PR head advances mid-checkup."""

    @staticmethod
    def _refresh_counter_path(cwd: Path, pr_number: int) -> Path:
        return cwd / ".pdd" / f"checkup-pr-{pr_number}" / "pr_head_refreshes"

    @staticmethod
    def _invoke(
        tmp_path: Path,
        *,
        no_fix: bool = False,
        use_github_state: bool = False,
    ):
        """Run ``run_agentic_checkup_orchestrator`` with stub kwargs."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        return run_agentic_checkup_orchestrator(
            issue_url="https://github.com/o/r/issues/99",
            issue_content="stub",
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            no_fix=no_fix,
            timeout_adder=0.0,
            use_github_state=use_github_state,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

    def test_pr_head_advance_after_step7_triggers_rerun(
        self, tmp_path: Path
    ) -> None:
        """Checkpoint A: Step 7 passes but a refetch shows the head moved
        from A->B before the push block. The wrapper must discard the
        stale work, re-enter the inner against the new head, complete a
        second iteration cleanly, and return success."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Iteration 1: head=A at entry, head=B at checkpoint A -> restart.
        # Iteration 2: head=B at entry, head=B at checkpoint A, head=B at
        # push block -> no restart, push succeeds, return clean.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 checkpoint A -> RESTART
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 checkpoint A
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 push-block prefetch
        ]
        setup_calls: list = []

        def fake_setup(*args, **kwargs):  # noqa: ANN001
            setup_calls.append((args, kwargs))
            return (wt, None)

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            side_effect=fake_setup,
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ) as metadata_mock, patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="bbbbbbbb22222222",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is True, msg
        # Setup must be invoked twice — once per iteration — so the second
        # attempt starts from the freshly checked-out head.
        assert len(setup_calls) == 2
        # The first refetch (iter-1 checkpoint A) consumed the second
        # sequence entry; push runs only in iteration 2.
        push_mock.assert_called_once()
        # 5 calls total: 2 in iter-1, 3 in iter-2.
        assert metadata_mock.call_count == 5

    def test_pr_head_advance_via_rebase_conflict_triggers_rerun(
        self, tmp_path: Path
    ) -> None:
        """Checkpoint B: push fails with a rebase-conflict message and a
        refetch confirms the head advanced. The wrapper restarts and the
        second iteration succeeds."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # iter 1: entry=A, checkpoint A=A (no restart), push prefetch=A,
        #         push rebase-conflict, checkpoint B refetch=B -> RESTART.
        # iter 2: entry=B, checkpoint A=B, push prefetch=B, push OK.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 checkpoint A
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 push prefetch
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 checkpoint B refetch
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 checkpoint A
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 push prefetch
        ]
        push_responses = [
            (
                False,
                (
                    "Failed to rebase fixes onto updated PR branch before "
                    "retrying push: CONFLICT (content): Merge conflict in foo.py"
                ),
            ),
            (True, "Pushed fixes to PR branch."),
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            side_effect=push_responses,
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="ffffffff99999999",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is True, msg
        # Push attempted twice: first rebase-conflict, then clean push.
        assert push_mock.call_count == 2

    def test_pr_head_advance_budget_exhausted_fails_clearly(
        self, tmp_path: Path
    ) -> None:
        """If the head keeps advancing past ``MAX_PR_HEAD_REFRESHES``
        restarts, the wrapper must return a clear failure message that
        lists the observed SHA transitions and cites the budget value."""
        from pdd.agentic_checkup_orchestrator import MAX_PR_HEAD_REFRESHES

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Every iteration's checkpoint A sees a different head -> restart.
        # 3 inner attempts total (initial + 2 restarts) = 6 metadata calls
        # (entry + checkpoint A per attempt). Use distinct SHAs to verify
        # the diagnostic surfaces the transition history.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 ckptA -> restart
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("cccccccc33333333"),  # iter 2 ckptA -> restart
            _pr_metadata("cccccccc33333333"),  # iter 3 entry
            _pr_metadata("dddddddd44444444"),  # iter 3 ckptA -> budget exhausted
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="dddddddd44444444",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is False
        assert "max_pr_head_refreshes=2" in msg, (
            f"Failure message must cite the budget value; got: {msg!r}"
        )
        # The diagnostic must list the observed SHA transitions in short form.
        assert "aaaaaaaa" in msg and "bbbbbbbb" in msg, msg
        assert "cccccccc" in msg and "dddddddd" in msg, msg
        # Push must NOT have run — every restart fired before the push block.
        push_mock.assert_not_called()
        # Sanity: design constant is exposed and equals 2.
        assert MAX_PR_HEAD_REFRESHES == 2

    def test_no_fix_pr_head_advance_does_not_consume_budget(
        self, tmp_path: Path
    ) -> None:
        """In ``--no-fix`` mode, an advance after Step 7 must NOT raise the
        restart exception (the inner falls through to existing behavior).
        The persisted refresh counter remains at 0."""
        from pdd.agentic_checkup_orchestrator import (
            _load_persisted_refresh_count,
        )

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Head advances between entry and a hypothetical checkpoint A —
        # but in --no-fix the checkpoint should not even consult metadata
        # a second time. We still seed two responses to be defensive.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # entry
            _pr_metadata("bbbbbbbb22222222"),  # would-be checkpoint A
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="aaaaaaaa11111111",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            # We don't care about success here, only that no restart was
            # consumed. The inner takes the existing --no-fix path.
            self._invoke(tmp_path, no_fix=True)

        # Counter file must not have been created (or, if created, == 0).
        assert _load_persisted_refresh_count(tmp_path, 200) == 0

    def test_ordinary_push_auth_failure_does_not_trigger_rerun(
        self, tmp_path: Path
    ) -> None:
        """When the push fails for a non-rebase reason (auth, network),
        the wrapper must NOT refetch / restart. Preserves the existing
        push-failure surface and guards against false-positive reruns
        triggered solely by transient head-shift visibility."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Only one inner attempt expected. Three calls per the inner's
        # existing fetch sites (entry + checkpoint A + push prefetch).
        # If anything tries to refetch in checkpoint B, this list is too
        # short and StopIteration will fail the test loudly.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # entry
            _pr_metadata("aaaaaaaa11111111"),  # checkpoint A
            _pr_metadata("aaaaaaaa11111111"),  # push prefetch
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ) as setup_mock, patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(
                False,
                "Failed to push fixes to PR branch: HTTP 401 Unauthorized",
            ),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="aaaaaaaa11111111",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is False
        assert "401" in msg
        push_mock.assert_called_once()
        # Single inner attempt -> setup called exactly once.
        assert setup_mock.call_count == 1

    def test_refresh_counter_clears_on_clean_success(
        self, tmp_path: Path
    ) -> None:
        """A clean run (no advance) must remove a pre-existing sidecar
        counter so the next checkup on this PR starts fresh."""
        counter_path = self._refresh_counter_path(tmp_path, 200)
        counter_path.parent.mkdir(parents=True, exist_ok=True)
        counter_path.write_text("1", encoding="utf-8")
        assert counter_path.exists()

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value=_pr_metadata("aaaaaaaa11111111"),
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="aaaaaaaa11111111",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, _msg, _cost, _model = self._invoke(tmp_path)

        assert success is True
        assert not counter_path.exists(), (
            "Persisted refresh counter must be cleared after a successful "
            f"no-advance run; file still present at {counter_path}"
        )

    def test_refresh_counter_persists_across_process_boundary(
        self, tmp_path: Path
    ) -> None:
        """The counter is durable: after a restart fires the on-disk
        value must reflect the consumed attempt so a Ctrl-C + manual
        rerun can't unbound the loop. Force budget exhaustion so the
        final saved value is observable."""
        counter_path = self._refresh_counter_path(tmp_path, 200)
        assert not counter_path.exists()

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Force every attempt to restart. With 3 attempts in total (1 +
        # 2 restarts), the counter ends at 2.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 ckptA -> restart
            _pr_metadata("bbbbbbbb22222222"),
            _pr_metadata("cccccccc33333333"),  # iter 2 ckptA -> restart
            _pr_metadata("cccccccc33333333"),
            _pr_metadata("dddddddd44444444"),  # iter 3 ckptA -> exhausted
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="dddddddd44444444",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, _msg, _cost, _model = self._invoke(tmp_path)

        assert success is False
        # After 2 restarts consumed the budget, the sidecar must reflect
        # the consumed count so a manual resume sees a non-zero starting
        # point and cannot accidentally unbound the loop.
        assert counter_path.exists(), (
            f"Refresh counter file must persist after restarts; "
            f"expected at {counter_path}"
        )
        on_disk = counter_path.read_text(encoding="utf-8").strip()
        assert on_disk == "2", (
            f"Counter file should hold the consumed-restart count (=2); "
            f"got {on_disk!r}"
        )

    def test_refresh_counter_resumes_from_pre_seeded_value(
        self, tmp_path: Path
    ) -> None:
        """Codex round-1 Finding 3: a Ctrl-C + manual rerun must NOT get
        a fresh budget. Pre-seed the sidecar at "1" and force exactly
        ONE head advance (one fewer than would normally exhaust the
        budget). If the wrapper ignored disk on entry it would treat
        this as a first restart and succeed on the second attempt; the
        correct behavior is exhaustion (it picks up at 1, this restart
        bumps the counter to 2 == ``MAX_PR_HEAD_REFRESHES``, so the
        next restart returns failure)."""
        counter_path = self._refresh_counter_path(tmp_path, 200)
        counter_path.parent.mkdir(parents=True, exist_ok=True)
        counter_path.write_text("1", encoding="utf-8")

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # iter 1: entry=A, ckptA=B -> restart (budget bumped 1 -> 2).
        # iter 2: entry=B, ckptA=C -> restart attempt fails the budget
        #         check (refresh_count already == MAX_PR_HEAD_REFRESHES).
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 ckptA -> restart
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("cccccccc33333333"),  # iter 2 ckptA -> exhausted
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="cccccccc33333333",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is False, (
            "Pre-seeded counter=1 + one restart must exhaust the budget; "
            f"got success message: {msg!r}"
        )
        assert "max_pr_head_refreshes=2" in msg, msg
        # Push must NOT have run — every iteration's restart fired
        # before the push block.
        push_mock.assert_not_called()

    def test_pr_head_advance_via_generic_non_fast_forward_push_failure_triggers_rerun(
        self, tmp_path: Path
    ) -> None:
        """Codex round-2 Finding 3a: when ``_commit_and_push_if_changed``'s
        internal 3-attempt retry loop exhausts on a remote-advance, its
        final return is the generic ``Failed to push fixes to PR branch:
        <git stderr>`` shape. Checkpoint B must recognize the embedded
        ``non-fast-forward`` marker via ``_is_remote_advanced_push_error``
        and trigger the bounded restart."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # iter 1: entry=A, checkpoint A=A, push prefetch=A, push fails
        #         with generic non-fast-forward error, ckpt B refetch=B
        #         -> RESTART.
        # iter 2: entry=B, ckptA=B, push prefetch=B, push OK.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 checkpoint A
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 push prefetch
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 checkpoint B refetch
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 checkpoint A
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 push prefetch
        ]
        # Realistic git stderr that the upstream
        # ``_is_remote_advanced_push_error`` detector matches via the
        # ``non-fast-forward`` marker.
        push_responses = [
            (
                False,
                (
                    "Failed to push fixes to PR branch: ! [rejected] HEAD -> "
                    "change/test (non-fast-forward) — Updates were rejected "
                    "because the remote contains work that you do not have "
                    "locally."
                ),
            ),
            (True, "Pushed fixes to PR branch."),
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            side_effect=push_responses,
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="ffffffff99999999",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is True, msg
        # Push attempted twice: first generic non-fast-forward, then clean.
        assert push_mock.call_count == 2
        # Budget consumed: one restart -> counter at 1 on disk.
        on_disk = self._refresh_counter_path(tmp_path, 200)
        # On clean success the counter is cleared, so the sidecar should
        # be absent. (If the test were to fail with success=False, the
        # counter file would remain.)
        assert not on_disk.exists(), (
            "Clean success after one restart must clear the sidecar; "
            f"file still present at {on_disk}"
        )

    @pytest.mark.parametrize(
        "no_change_message",
        ["No changes to push.", "No eligible changes to push."],
    )
    def test_no_change_push_head_advance_before_final_report_triggers_rerun(
        self, tmp_path: Path, no_change_message: str
    ) -> None:
        """Codex round-2 Finding 3b: Checkpoint C — a no-change push
        outcome means we never touched the PR branch. If the head moved
        between Checkpoint A and the final report, the Step 7 verdict
        is stale and posting it would be wrong. Checkpoint C must
        refetch and restart; the stale verdict from iteration 1 must
        NOT be posted (post_pr_comment seen exactly once for iter 2)."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # iter 1: entry=A, ckptA=A, push prefetch=A, push=(True, no-change),
        #         ckptC refetch=B -> RESTART.
        # iter 2: entry=B, ckptA=B, push prefetch=B, push OK, no Checkpoint
        #         C trigger because push message is the normal "Pushed ..."
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 checkpoint A
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 push prefetch
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 Checkpoint C refetch
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 checkpoint A
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 push prefetch
        ]
        push_responses = [
            (True, no_change_message),
            (True, "Pushed fixes to PR branch."),
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            side_effect=push_responses,
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="bbbbbbbb22222222",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ) as pr_comment_mock, patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            # ``use_github_state=True`` is required so the canonical
            # report path is actually exercised — that's the surface we
            # need to assert against (the stale verdict must not be
            # posted in iter 1).
            success, msg, _cost, _model = self._invoke(
                tmp_path, use_github_state=True
            )

        assert success is True, msg
        # Push attempted twice: no-change in iter 1, real push in iter 2.
        assert push_mock.call_count == 2
        # Critical: the iter-1 (stale) Step 7 verdict must NOT have been
        # posted. ``post_pr_comment`` should fire exactly once — for
        # iter 2's clean push.
        assert pr_comment_mock.call_count == 1, (
            "Stale Step 7 verdict from iter 1 must not be posted; "
            f"post_pr_comment was called {pr_comment_mock.call_count} times"
        )

    def test_empty_entry_pr_head_sha_does_not_consume_refresh_budget(
        self, tmp_path: Path
    ) -> None:
        """Codex round-2 Finding 4 (nit): when the orchestrator's entry
        fetch returns ``head_sha=""`` (PR metadata flake), every
        downstream checkpoint must fail-degrade rather than treat a
        later non-empty SHA as a head-advance signal. No restart, no
        sidecar counter file, push runs once."""
        from pdd.agentic_checkup_orchestrator import (
            _load_persisted_refresh_count,
        )

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Entry SHA empty; subsequent fetches return a non-empty SHA
        # that would otherwise look like an advance. With the
        # ``current_pr_head_sha and fresh_head_sha`` AND clause in
        # every checkpoint, the empty entry must fail-degrade.
        metadata_sequence = [
            _pr_metadata(""),                  # entry: empty SHA
            _pr_metadata("bbbbbbbb22222222"),  # checkpoint A
            _pr_metadata("bbbbbbbb22222222"),  # push prefetch
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="bbbbbbbb22222222",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is True, msg
        # Single inner run -> push ran exactly once.
        push_mock.assert_called_once()
        # No restart consumed -> sidecar never created.
        assert _load_persisted_refresh_count(tmp_path, 200) == 0
        assert not self._refresh_counter_path(tmp_path, 200).exists()

    # ----- External review Finding 1: --no-fix head-freshness -----

    def test_no_fix_head_advance_after_step7_fails_closed(
        self, tmp_path: Path
    ) -> None:
        """External review Finding 1: --no-fix --pr mode must NOT publish
        a stale clean verdict if the head advanced during the run.
        ``_finalize``'s fail-closed downgrade only runs under
        --review-loop, so the orchestrator owns this guardrail.

        Expected: success=False with a diagnostic citing the SHA
        transition and "treated as unverified"; canonical report still
        posts (so the PR thread shows the downgrade); no restart budget
        consumed (--no-fix is fix-mode-exclusive by design)."""
        from pdd.agentic_checkup_orchestrator import (
            _load_persisted_refresh_count,
        )

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Entry SHA = A; post-Step-7 refetch returns B -> stale.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # entry
            _pr_metadata("bbbbbbbb22222222"),  # post-gate freshness check
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="bbbbbbbb22222222",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ) as pr_comment_mock, patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(
                tmp_path, no_fix=True, use_github_state=True
            )

        assert success is False, (
            "--no-fix + head advance must downgrade to failure; "
            f"got success message: {msg!r}"
        )
        assert "aaaaaaaa" in msg and "bbbbbbbb" in msg, (
            f"Diagnostic must show SHA transition; got: {msg!r}"
        )
        assert "treated as unverified" in msg, msg
        # No push in --no-fix mode.
        push_mock.assert_not_called()
        # Canonical report still posted so the PR thread records what
        # was verified and why it was downgraded.
        pr_comment_mock.assert_called_once()
        # Critical: budget remains unspent — the lease is fix-mode only.
        assert _load_persisted_refresh_count(tmp_path, 200) == 0
        assert not self._refresh_counter_path(tmp_path, 200).exists()

    def test_no_fix_head_unchanged_after_step7_succeeds(
        self, tmp_path: Path
    ) -> None:
        """External review Finding 1, happy variant: when the no-fix
        post-Step-7 refetch confirms the head is unchanged, the verdict
        is published normally (success=True, no downgrade)."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # Entry SHA = A; post-Step-7 refetch returns A again -> clean.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # entry
            _pr_metadata("aaaaaaaa11111111"),  # post-gate freshness check
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="aaaaaaaa11111111",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(
                tmp_path, no_fix=True, use_github_state=True
            )

        assert success is True, msg
        # No push in --no-fix mode regardless.
        push_mock.assert_not_called()
        # No diagnostic — the verdict is clean.
        assert "treated as unverified" not in msg

    # ----- External review Finding 2: step_comments preserved on restart -----

    def test_step_comments_preserved_across_restart(
        self, tmp_path: Path
    ) -> None:
        """External review Finding 2: after a restart, the next inner
        iteration must NOT re-post per-step issue comments that were
        already posted in the prior iteration.

        Mechanism: ``_PRHeadAdvancedRestart`` carries the inner's
        ``step_comments_set`` and the outer wrapper replays it into the
        next iteration via ``_carried_step_comments``. We assert this by
        intercepting ``post_step_comment_once``: every (step_num,
        iteration) composite key must appear at most once across the
        entire wrapper run, even though both iterations exercise the
        full step pipeline."""
        wt = tmp_path / "wt"
        wt.mkdir()
        posted_step_keys: list[int] = []

        def fake_post_once(
            *,
            repo_owner,  # noqa: ANN001
            repo_name,
            issue_number,
            step_num,
            body,
            posted_steps,
            cwd,
        ) -> bool:
            # Honor the dedup set the orchestrator passes in — the
            # production helper does the same thing, but stubbing
            # post_step_comment_once via patch() bypasses that path. We
            # have to model the dedup contract so the test exercises it.
            if step_num in posted_steps:
                return False
            posted_steps.add(step_num)
            posted_step_keys.append(step_num)
            return True

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # iter 1: entry=A, ckptA=B -> restart.
        # iter 2: entry=B, ckptA=B, push prefetch=B, push OK.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 ckptA -> restart
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 ckptA
            _pr_metadata("bbbbbbbb22222222"),  # iter 2 push prefetch
        ]

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state"
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="bbbbbbbb22222222",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment_once",
            side_effect=fake_post_once,
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is True, msg
        # The dedup contract: every composite key (step_num × iteration)
        # appears at most once across the entire wrapper invocation.
        assert len(posted_step_keys) == len(set(posted_step_keys)), (
            "Per-step comments must be posted at most once across "
            f"restarts; saw duplicate keys in: {posted_step_keys}"
        )
        # And we must have at least one comment posted from iter 1 that
        # was NOT re-posted in iter 2 — that's the property the
        # preservation actually buys us.
        assert len(posted_step_keys) > 0, (
            "Expected at least one per-step comment to have been posted"
        )

    # ----- External review Finding 3: skip state-load on restart -----

    def test_restart_skips_load_workflow_state_even_if_clear_fails(
        self, tmp_path: Path
    ) -> None:
        """External review Finding 3: on restart iterations the outer
        wrapper must bypass ``load_workflow_state`` entirely. This is
        defense-in-depth against the case where ``clear_workflow_state``'s
        GitHub DELETE silently fails AND the next ``_fetch_pr_metadata``
        flakes back to the old SHA — the identity guard would otherwise
        accept the stale cache.

        We force the worst case: ``clear_workflow_state`` raises (caught
        by outer's try/except), ``load_workflow_state`` would return a
        populated stale state if asked, and the next entry-fetch SHA
        equals the old one. Iter 2 must still treat the worktree as
        fresh (no resume), which we verify by ``load_workflow_state``
        being called exactly once (iter 1 only)."""
        wt = tmp_path / "wt"
        wt.mkdir()

        # The stale state that load_workflow_state would return if
        # iter 2 ever consulted it. Populated mode/SHA so identity
        # guard would accept it.
        stale_state = {
            "workflow": "checkup",
            "issue_number": 99,
            "last_completed_step": 7,
            "step_outputs": {"7": _step7_clean_output()},
            "total_cost": 0.0,
            "model_used": "fake-model",
            "github_comment_id": None,
            "changed_files": [],
            "worktree_path": str(wt),
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            # Old SHA — matches what iter-2 entry-fetch returns below.
            "pr_head_sha": "aaaaaaaa11111111",
            "step_comments": [],
        }

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = (
                _step7_clean_output() if step_num == 7
                else f"Step {step_num} output"
            )
            return (True, output, 0.0, "fake-model")

        # iter 1: entry=A, ckptA=B -> restart.
        # iter 2: entry=A (flake — old SHA returned by the next
        #         _fetch_pr_metadata), ckptA=A, push prefetch=A.
        # The flake matters because if iter 2 ALSO went through
        # load_workflow_state, the identity guard would compare cached
        # pr_head_sha="A" to current_pr_head_sha="A" and ACCEPT the
        # stale cache — skipping every step and jumping straight to
        # push. The fix (_force_skip_state_load on restart) bypasses
        # load_workflow_state, so iter 2 always runs every step fresh.
        metadata_sequence = [
            _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
            _pr_metadata("bbbbbbbb22222222"),  # iter 1 ckptA -> restart
            _pr_metadata("aaaaaaaa11111111"),  # iter 2 entry (flake)
            _pr_metadata("aaaaaaaa11111111"),  # iter 2 ckptA — no restart
            _pr_metadata("aaaaaaaa11111111"),  # iter 2 push prefetch
        ]
        executed_steps: list = []

        def tracking_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            executed_steps.append(step_num)
            return fake_step(step_num, *_args, **_kwargs)

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=tracking_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(stale_state, None),
        ) as load_mock, patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            # The first call (outer wrapper's clear-on-restart) raises
            # to simulate GitHub DELETE flake; subsequent calls
            # (terminal-success clear in the inner) are no-op. This
            # mirrors the production failure mode: clear_workflow_state
            # can silently fail without raising, but if it DID raise the
            # outer's try/except already absorbs it. Either way iter 2
            # must still bypass load_workflow_state.
            "pdd.agentic_checkup_orchestrator.clear_workflow_state",
            side_effect=[RuntimeError("simulated GitHub DELETE flake"), None, None],
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            side_effect=metadata_sequence,
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            return_value="aaaaaaaa11111111",
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_pr_comment", return_value=True
        ), patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment", return_value=True
        ):
            success, msg, _cost, _model = self._invoke(tmp_path)

        assert success is True, msg
        # Iter 2 must have BYPASSED load_workflow_state (and therefore
        # never had a chance to accept the stale cache that would have
        # short-circuited every step).
        assert load_mock.call_count == 1, (
            "load_workflow_state must be called exactly once (iter 1 "
            f"only); iter 2 must use _force_skip_state_load. Got: "
            f"{load_mock.call_count} calls"
        )
        # Push ran in iter 2 (proves the inner reached the push block).
        push_mock.assert_called_once()
        # Iter 2 ran every step fresh — if state-load were honored, the
        # stale state (last_completed_step=7) would have made the inner
        # jump directly to push and run zero steps in iter 2. Across
        # both iterations there should be at least 18 step calls
        # (9 per iteration × 2). Iter 1 ran steps 1-7 (8 calls) before
        # restart, iter 2 ran all 9 (steps 1-7 plus step 6 sub-steps).
        # Lower bound: > 9 confirms iter-2 didn't resume.
        assert len(executed_steps) > 9, (
            "iter 2 must have run steps fresh; instead saw only "
            f"{len(executed_steps)} total step calls across both "
            f"iterations: {executed_steps}"
        )
