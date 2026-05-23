"""End-to-end integration tests for the PR-head freshness lease (issue #1116).

Step 6c of the agentic checkup for issue #1116. The fix-verify work on
PR #1134 spans two collaborating modules:

* ``pdd.agentic_checkup_orchestrator`` — owns the outer rerun loop, the
  ``_PRHeadAdvancedRestart`` exception, and the on-disk refresh-counter
  sidecar.
* ``pdd.checkup_review_loop`` — owns the underlying git/push helpers
  (``_commit_and_push_if_changed``, ``_git_changed_files``,
  ``_git_rev_parse_head``, ``_is_remote_advanced_push_error``) that the
  orchestrator re-exports via lazy wrappers to keep the import cycle
  one-directional.

Unit-level coverage of each side lives in ``test_agentic_checkup_orches
trator.py``, ``test_checkup_review_loop.py``, and ``test_checkup_pr_mode
.py``. This file covers the **cross-module integration points** between
those two modules and ``pdd.agentic_common`` — the seams a future refactor
is most likely to break silently:

1. The lazy wrapper round-trip: the orchestrator's
   ``_commit_and_push_if_changed`` must return exactly what the review
   loop's implementation returns (the 2-tuple contract noted in Step 4).
2. The git helper wrappers must resolve to the same review-loop callables
   and produce identical results against a real worktree.
3. The refresh-counter sidecar path must NOT overlap the workflow-state
   path that the orchestrator wipes on restart — otherwise
   ``clear_workflow_state`` would clobber the durable retry budget.
4. The exhaustion message surfaced by ``run_agentic_checkup_orchestrator``
   must include the full chain of observed PR head SHAs (acceptance
   criterion from the issue).
"""
from __future__ import annotations

import subprocess
from pathlib import Path
from typing import List
from unittest.mock import patch

import pytest

from pdd import agentic_checkup_orchestrator as orch
from pdd import checkup_review_loop as loop


# ---------------------------------------------------------------------------
# Real-worktree fixture
# ---------------------------------------------------------------------------


@pytest.fixture
def real_git_worktree(tmp_path: Path) -> Path:
    """Initialise a minimal git worktree with one committed file.

    Uses real ``git`` so the helpers under test exercise their actual
    subprocess paths — that is the cross-module integration we are
    verifying, so mocks would defeat the purpose.
    """
    wt = tmp_path / "wt"
    wt.mkdir()
    env = {
        "GIT_AUTHOR_NAME": "Test",
        "GIT_AUTHOR_EMAIL": "test@example.com",
        "GIT_COMMITTER_NAME": "Test",
        "GIT_COMMITTER_EMAIL": "test@example.com",
    }
    for cmd in (
        ["git", "init", "-q", "-b", "main"],
        ["git", "config", "user.email", "test@example.com"],
        ["git", "config", "user.name", "Test"],
    ):
        subprocess.run(cmd, cwd=wt, check=True, env={**env})
    (wt / "seed.txt").write_text("seed\n", encoding="utf-8")
    subprocess.run(["git", "add", "seed.txt"], cwd=wt, check=True, env={**env})
    subprocess.run(
        ["git", "commit", "-q", "-m", "seed"],
        cwd=wt,
        check=True,
        env={**env},
    )
    return wt


# ---------------------------------------------------------------------------
# 1. Lazy-import wrapper round-trip
# ---------------------------------------------------------------------------


def test_orchestrator_commit_push_wrapper_returns_review_loop_2tuple(
    real_git_worktree: Path,
) -> None:
    """Orchestrator ↔ review-loop: ``_commit_and_push_if_changed`` boundary.

    The orchestrator imports the helper lazily inside its own
    same-named wrapper. If the review-loop side ever changes its return
    shape (the prior 4-tuple-vs-2-tuple drift noted in Step 4 is the
    canonical regression here), the orchestrator's Checkpoint B/C path
    would either crash with ``ValueError: too many values to unpack`` or
    silently mis-classify a push as a rebase conflict. Pin the wrapper
    against the real implementation in a real worktree where there are
    no changes to push — the helper short-circuits before any network
    call, so we get a deterministic ``(True, "No changes to push.")``
    out of the underlying implementation.
    """
    pr_metadata = {
        "clone_url": "https://example.invalid/o/r.git",
        "head_ref": "main",
        "head_owner": "o",
        "head_repo": "r",
        "head_sha": "deadbeefdeadbeef",
    }

    result = orch._commit_and_push_if_changed(
        real_git_worktree, pr_metadata, "test message"
    )
    direct = loop._commit_and_push_if_changed(
        real_git_worktree, pr_metadata, "test message"
    )

    assert result == direct, (
        "Lazy orchestrator wrapper must round-trip the review-loop "
        f"helper's return value verbatim. Got {result!r} via wrapper, "
        f"{direct!r} via direct call."
    )
    assert isinstance(result, tuple) and len(result) == 2, (
        f"Boundary contract is the 2-tuple (bool, str); got {result!r}"
    )
    pushed, message = result
    assert pushed is True
    assert message == "No changes to push."


# ---------------------------------------------------------------------------
# 2. Git helper wrappers
# ---------------------------------------------------------------------------


def test_orchestrator_git_helper_wrappers_delegate_to_review_loop(
    real_git_worktree: Path,
) -> None:
    """Every lazy git-helper wrapper must produce the same value the
    review-loop callable would. Drift here is silent: the orchestrator's
    Checkpoint A SHA comparison and the prompt-source guard both rely on
    these helpers returning exactly what the review loop computes when
    its own internal code paths invoke them.
    """
    # _git_rev_parse_head: identical SHA from both sides.
    assert orch._git_rev_parse_head(real_git_worktree) == loop._git_rev_parse_head(
        real_git_worktree
    )
    # Sanity: the SHA is a non-empty 40-char hex (real git output).
    sha = orch._git_rev_parse_head(real_git_worktree)
    assert len(sha) == 40 and all(c in "0123456789abcdef" for c in sha)

    # _git_changed_files: introduce a tracked-file modification and an
    # untracked file; both sides must report the same set.
    (real_git_worktree / "seed.txt").write_text("seed\nmore\n", encoding="utf-8")
    (real_git_worktree / "untracked.txt").write_text("x\n", encoding="utf-8")
    assert sorted(orch._git_changed_files(real_git_worktree)) == sorted(
        loop._git_changed_files(real_git_worktree)
    )

    # _is_remote_advanced_push_error: pure-function detector, both
    # sides must agree on the canonical remote-advance stderr shapes
    # the Checkpoint B classifier depends on.
    samples = (
        " ! [rejected]        main -> main (fetch first)",
        "error: failed to push some refs",
        "Updates were rejected because the tip of your current branch is behind",
        "remote contains work that you do not have locally",
        "HTTP 401 Unauthorized",  # NOT a remote-advance error
        "",
    )
    for sample in samples:
        assert orch._is_remote_advanced_push_error(
            sample
        ) == loop._is_remote_advanced_push_error(sample), (
            f"Detector wrappers disagree on sample: {sample!r}"
        )


# ---------------------------------------------------------------------------
# 3. Sidecar path isolation from workflow-state path
# ---------------------------------------------------------------------------


def test_refresh_counter_sidecar_isolated_from_workflow_state_dir(
    tmp_path: Path,
) -> None:
    """Cross-module guarantee: the orchestrator wipes workflow state on
    restart (``clear_workflow_state`` from ``agentic_common``) but the
    PR-head refresh counter must survive — otherwise the durable retry
    budget would reset to zero on every restart and the
    ``MAX_PR_HEAD_REFRESHES`` bound would be moot.

    The guarantee is structural: the two paths live in disjoint
    directories. Pin that here so a refactor that moves either side
    into the same directory tree fails this test instead of silently
    unbounding the loop.
    """
    pr_number = 200
    issue_number = 99

    sidecar = orch._refresh_count_path(tmp_path, pr_number)
    state_dir = orch._get_state_dir(tmp_path)
    state_file = state_dir / f"checkup_state_{issue_number}.json"

    # The sidecar must NOT live inside the workflow-state directory tree
    # — clear_workflow_state targets state_dir/<workflow>_state_<n>.json
    # explicitly, but a future "rm -rf state_dir" cleanup would still
    # need to leave the counter alone.
    sidecar_resolved = sidecar.resolve()
    state_dir_resolved = state_dir.resolve()
    assert state_dir_resolved not in sidecar_resolved.parents, (
        f"Refresh-counter sidecar at {sidecar_resolved} lives inside "
        f"workflow-state dir {state_dir_resolved}; clear_workflow_state "
        "could wipe the retry budget."
    )
    assert sidecar_resolved != state_file.resolve()

    # End-to-end: write the sidecar, simulate clear_workflow_state on
    # the same cwd, confirm the sidecar still exists.
    orch._save_persisted_refresh_count(tmp_path, pr_number, 1)
    assert sidecar.exists()
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file.write_text("{}", encoding="utf-8")

    from pdd.agentic_common import clear_workflow_state

    clear_workflow_state(
        cwd=tmp_path,
        issue_number=issue_number,
        workflow_type="checkup",
        state_dir=state_dir,
        repo_owner="o",
        repo_name="r",
        use_github_state=False,
    )

    assert not state_file.exists(), (
        "clear_workflow_state should have removed the workflow-state file"
    )
    assert sidecar.exists(), (
        "clear_workflow_state must not touch the refresh-counter sidecar; "
        f"sidecar at {sidecar} vanished alongside the workflow-state file."
    )
    assert orch._load_persisted_refresh_count(tmp_path, pr_number) == 1


# ---------------------------------------------------------------------------
# 4. Exhaustion message contains the observed PR-head chain
# ---------------------------------------------------------------------------


# Match the canonical Step 7 stub from ``test_checkup_pr_mode.py`` — the
# orchestrator's Step 7 gate fails closed without a structured JSON
# payload, so the fake-step generator below must emit it for step 7.
_STEP7_CLEAN = (
    "All Issues Fixed\n"
    "```json\n"
    "{\n"
    '  "success": true,\n'
    '  "message": "verification passed",\n'
    '  "issue_aligned": true,\n'
    '  "issues": [],\n'
    '  "changed_files": []\n'
    "}\n"
    "```"
)


def _pr_metadata(head_sha: str) -> dict:
    return {
        "clone_url": "https://github.com/o/r.git",
        "head_ref": "change/test",
        "head_owner": "o",
        "head_repo": "r",
        "head_sha": head_sha,
    }


def test_exhaustion_message_includes_observed_head_sha_chain(
    tmp_path: Path,
) -> None:
    """Acceptance criterion (issue #1116):

        "The retry loop is bounded and reports the latest observed PR
        head SHAs in the failure message if exhausted."

    Drive the full ``run_agentic_checkup_orchestrator`` end-to-end with
    a sequence of head SHAs that exhaust the budget, then assert the
    final user-facing failure string contains the short-SHA chain
    ``aaaaaaaa->bbbbbbbb, bbbbbbbb->cccccccc`` produced from
    ``refresh_history``.

    This is the integration test the existing ``TestPrHeadAdvanceAuto
    Rerun`` suite is missing: those tests assert ``success is False``
    and the on-disk counter, but never that the returned message
    actually exposes the observed-heads chain to the operator.
    """
    wt = tmp_path / "wt"
    wt.mkdir()

    def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
        output = _STEP7_CLEAN if step_num == 7 else f"step-{step_num}"
        return (True, output, 0.0, "fake-model")

    # Three full inner attempts. Each attempt sees its entry SHA, then a
    # different SHA at Checkpoint A → ``_PRHeadAdvancedRestart`` fires.
    # After two restarts the third one fails the budget guard and we
    # return the exhaustion message.
    metadata_sequence = [
        _pr_metadata("aaaaaaaa11111111"),  # iter 1 entry
        _pr_metadata("bbbbbbbb22222222"),  # iter 1 ckptA -> restart
        _pr_metadata("bbbbbbbb22222222"),  # iter 2 entry
        _pr_metadata("cccccccc33333333"),  # iter 2 ckptA -> restart
        _pr_metadata("cccccccc33333333"),  # iter 3 entry
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
        success, message, _cost, _model = orch.run_agentic_checkup_orchestrator(
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
    # The message must reference the bound and both observed transitions
    # so an operator reading the CLI output can identify exactly which
    # SHAs the budget was spent on.
    assert "max_pr_head_refreshes=" in message
    for fragment in (
        "aaaaaaaa->bbbbbbbb",
        "bbbbbbbb->cccccccc",
    ):
        assert fragment in message, (
            f"Exhaustion message must include observed transition "
            f"{fragment!r}; full message: {message!r}"
        )
