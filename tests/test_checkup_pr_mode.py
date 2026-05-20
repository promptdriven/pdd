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

import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.agentic_change import _parse_pr_url
from pdd.commands.checkup import checkup


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
        from pdd.agentic_checkup_orchestrator import _setup_pr_worktree

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
            assert fetch_calls, "expected a git fetch for pull/77/head"
            assert any("pull/77/head" in " ".join(c) for c in fetch_calls)
            assert add_calls, "expected a git worktree add"

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
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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

    def test_pr_mode_context_populated(self, tmp_path: Path) -> None:
        """PR-mode fields must land in the context dict passed to step prompts."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        captured_contexts = []

        def capture_step(step_num, _name, context, **_kw):  # noqa: ANN001
            captured_contexts.append(dict(context))
            output = "All Issues Fixed" if step_num == 7 else f"out-{step_num}"
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
            output = "All Issues Fixed" if step_num == 7 else f"out-{step_num}"
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
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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
        """When the remote PR head SHA matches the cached SHA, cached step
        outputs MUST be reused (no regression to a forced re-verification)."""
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
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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


# ---------------------------------------------------------------------------
# Blocker #2 (codex round-1): on push failure, surface worktree path + local
# commit SHA so the user can recover the local fixes.
# ---------------------------------------------------------------------------


class TestPrModePushFailureDiagnostics:
    def test_push_failure_message_includes_worktree_and_local_sha(
        self, tmp_path: Path
    ) -> None:
        """If _commit_and_push_if_changed fails on the final iteration, the
        returned error MUST give the user enough to recover: the worktree
        path AND the local commit SHA containing the unpushed fixes."""
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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
            return_value=(False, "Failed to push fixes to PR branch: permission denied"),
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_rev_parse_head",
            # Called once on push failure to capture the local commit SHA.
            return_value="local_commit_sha_222",
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
            f"Expected worktree path '{wt}' in failure message, got: {msg}"
        )
        assert "local_commit_sha_222" in msg, (
            "Expected local commit SHA in failure message so user can "
            f"cherry-pick or push manually. Got: {msg}"
        )


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
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
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
