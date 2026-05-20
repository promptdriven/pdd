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
        metadata_mock.assert_called_once_with("o", "r", 200)
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
# Regression tests — checkup PR #1112 / issue #1104
# ---------------------------------------------------------------------------


class TestPrModeNoFixSkipsPushHelpers:
    """PR-mode + --no-fix must skip _fetch_pr_metadata / _commit_and_push_if_changed.

    Regression for the fix in pdd/agentic_checkup_orchestrator.py: in --no-fix
    PR mode there are no fixes to push, so a verify-only run must not make the
    extra `gh api` call to fetch PR metadata or attempt a commit/push.
    """

    def _run_in_pr_no_fix_mode(self, tmp_path: Path):
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(tmp_path / "wt", None),
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
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata"
        ) as fetch_mock, patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "pushed"),
        ) as push_mock:
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
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )
            return success, fetch_mock, push_mock

    def test_no_fix_skips_metadata_fetch_and_push(self, tmp_path: Path) -> None:
        success, fetch_mock, push_mock = self._run_in_pr_no_fix_mode(tmp_path)
        assert success
        assert not fetch_mock.called, (
            "_fetch_pr_metadata must not be called under --no-fix "
            "(no fixes to push → no extra gh api call)"
        )
        assert not push_mock.called, (
            "_commit_and_push_if_changed must not be called under --no-fix"
        )

    def test_fix_mode_still_invokes_push_helpers(self, tmp_path: Path) -> None:
        """Sanity check: with no_fix=False the push helpers DO fire.

        Locks the symmetry — the skip is conditioned on `not no_fix`, not a
        wholesale removal of the push path.
        """
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(tmp_path / "wt", None),
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
            return_value={"clone_url": "https://github.com/o/r.git", "head_ref": "feat"},
        ) as fetch_mock, patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "pushed"),
        ) as push_mock:
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
                no_fix=False,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )
            assert fetch_mock.called
            assert push_mock.called


# ---------------------------------------------------------------------------
# Integration tests — checkup PR #1112 / issue #1104
#
# These exercise the *cross-module* chain end to end:
#
#   agentic_e2e_fix_orchestrator._run_final_checkup_on_pr
#     -> agentic_checkup.run_agentic_checkup
#       -> agentic_checkup._find_project_root            (uses `cwd`)
#       -> agentic_checkup_orchestrator.run_agentic_checkup_orchestrator
#         -> _fetch_pr_metadata / _commit_and_push_if_changed
#            (gated by `no_fix`)
#
# Regression tests in test_agentic_checkup.py and test_agentic_e2e_fix_orchestrator.py
# already pin each module in isolation. These tests verify that `cwd` and
# `no_fix` propagate through the *whole* call chain without being lost or
# rewritten by an intermediate layer.
# ---------------------------------------------------------------------------


class TestFinalCheckupIntegrationChain:
    """End-to-end propagation of `cwd` / `no_fix` through 3 modules."""

    def _common_orchestrator_patches(self, tmp_path):
        """Patches that stub orchestrator side effects without faking the
        run_agentic_checkup → orchestrator boundary itself."""
        wt = tmp_path / "wt"
        wt.mkdir()

        def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
            output = "All Issues Fixed" if step_num == 7 else f"Step {step_num} output"
            return (True, output, 0.0, "fake-model")

        return wt, fake_step

    def test_final_checkup_propagates_cwd_to_project_root_resolver(
        self, tmp_path
    ) -> None:
        """e2e_fix.`_run_final_checkup_on_pr` → agentic_checkup.`_find_project_root`.

        The integration concern: when `_run_final_checkup_on_pr` is given a
        worktree that differs from the process CWD, the inner
        `run_agentic_checkup` call must locate the project root using that
        worktree, not the ambient CWD. This pins the full forwarding chain
        across both modules at once.
        """
        from pdd.agentic_e2e_fix_orchestrator import _run_final_checkup_on_pr

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._find_open_pr_number",
            return_value=200,
        ), patch(
            "pdd.agentic_checkup._find_project_root",
            return_value=tmp_path,
        ) as find_root_mock, patch(
            "pdd.agentic_checkup._load_pddrc_content", return_value=""
        ), patch(
            "pdd.agentic_checkup._load_architecture_json",
            return_value=([], tmp_path / "arch.json"),
        ), patch(
            "pdd.agentic_checkup._check_gh_cli", return_value=True
        ), patch(
            "pdd.agentic_checkup._run_gh_command"
        ) as gh_mock, patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(True, "Checkup complete", 0.0, "fake-model"),
        ):
            import json as _json
            gh_mock.side_effect = [
                (True, _json.dumps({"title": "t", "body": "b"})),
                (True, "[]"),
            ]

            success, _msg, _cost, _model = _run_final_checkup_on_pr(
                issue_url="https://github.com/o/r/issues/99",
                repo_owner="o",
                repo_name="r",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                timeout_adder=0.0,
                use_github_state=False,
                reasoning_time=None,
            )

        assert success
        assert find_root_mock.called, (
            "run_agentic_checkup must reach _find_project_root through the chain"
        )
        called_with = find_root_mock.call_args.args[0]
        assert called_with == tmp_path, (
            f"cwd lost through chain: _find_project_root saw {called_with!r}, "
            f"not the worktree {tmp_path!r}"
        )

    def test_final_checkup_forwards_pr_url_to_orchestrator(self, tmp_path) -> None:
        """e2e_fix → agentic_checkup → orchestrator: PR URL + no_fix=False reach
        the orchestrator unchanged so PR-mode fixing is actually triggered."""
        from pdd.agentic_e2e_fix_orchestrator import _run_final_checkup_on_pr

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._find_open_pr_number",
            return_value=200,
        ), patch(
            "pdd.agentic_checkup._find_project_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup._load_pddrc_content", return_value=""
        ), patch(
            "pdd.agentic_checkup._load_architecture_json",
            return_value=([], tmp_path / "arch.json"),
        ), patch(
            "pdd.agentic_checkup._check_gh_cli", return_value=True
        ), patch(
            "pdd.agentic_checkup._run_gh_command"
        ) as gh_mock, patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(True, "Checkup complete", 0.0, "fake-model"),
        ) as orch_mock:
            import json as _json
            gh_mock.side_effect = [
                (True, _json.dumps({"title": "t", "body": "b"})),
                (True, "[]"),
            ]

            _run_final_checkup_on_pr(
                issue_url="https://github.com/o/r/issues/99",
                repo_owner="o",
                repo_name="r",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                timeout_adder=0.0,
                use_github_state=False,
                reasoning_time=None,
            )

        assert orch_mock.called
        kwargs = orch_mock.call_args.kwargs
        # _run_final_checkup_on_pr hard-codes no_fix=False — verify it survives
        # the agentic_checkup → orchestrator hop.
        assert kwargs["no_fix"] is False, (
            "no_fix=False lost between run_agentic_checkup and the orchestrator"
        )
        # PR URL must be carried through so orchestrator enters PR mode.
        assert kwargs["pr_url"] == "https://github.com/o/r/pull/200"
        assert kwargs["pr_number"] == 200
        assert kwargs["pr_owner"] == "o"
        assert kwargs["pr_repo"] == "r"
        # cwd at the orchestrator layer is the project root, not the raw cwd
        # parameter — confirm it is at least set.
        assert kwargs["cwd"] is not None

    def test_pr_mode_no_fix_chain_skips_push_helpers(self, tmp_path) -> None:
        """Full chain: e2e → agentic_checkup → orchestrator → push helpers.

        When the chain is invoked with no_fix semantics (here exercised via the
        orchestrator directly because `_run_final_checkup_on_pr` pins
        no_fix=False) we still want to lock in that the push-helper gate honors
        `no_fix` at the orchestrator level — this is the contract the e2e
        orchestrator depends on for any future code path that passes a
        verification-only invocation through.
        """
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        wt, fake_step = self._common_orchestrator_patches(tmp_path)

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
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata"
        ) as fetch_mock, patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "pushed"),
        ) as push_mock:
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
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success
        assert not fetch_mock.called
        assert not push_mock.called

    def test_no_pr_path_short_circuits_without_touching_checkup(
        self, tmp_path
    ) -> None:
        """e2e → no PR found → does not call into agentic_checkup at all.

        Integration concern: the short-circuit branch in
        `_run_final_checkup_on_pr` must not invoke `run_agentic_checkup`, even
        accidentally. This prevents wasted gh API calls / spurious worktree
        setup when there is no PR to gate.
        """
        from pdd.agentic_e2e_fix_orchestrator import _run_final_checkup_on_pr

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._find_open_pr_number",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator"
        ) as orch_mock, patch(
            "pdd.agentic_checkup._check_gh_cli", return_value=True
        ) as gh_check_mock:
            success, msg, _cost, _model = _run_final_checkup_on_pr(
                issue_url="https://github.com/o/r/issues/99",
                repo_owner="o",
                repo_name="r",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                timeout_adder=0.0,
                use_github_state=False,
                reasoning_time=None,
            )

        assert success is True
        assert "No open PR" in msg
        assert not orch_mock.called
        assert not gh_check_mock.called
