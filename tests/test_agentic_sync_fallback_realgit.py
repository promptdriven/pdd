"""Real-git regression tests for clean-restart fallback-branch architecture augmentation.

Issue #1609: ``_augment_architecture_from_pr_branch`` hardcoded
``origin/change/issue-N`` and missed clean-restart ``change/issue-N-job-*`` fallback
branches, so valid new modules created on a fallback branch were dropped and
``_filter_invalid_basenames`` then rejected them as hallucinations.

Unlike ``tests/test_agentic_sync.py`` (which patches ``subprocess.run`` and therefore
encodes the *author's assumption* of what git returns), these tests build a REAL git
repo with a bare ``origin`` remote and real remote-tracking branches, then exercise the
UNMOCKED function. This is the only layer that actually validates the git plumbing the
bug lived in: the ``git for-each-ref`` glob, ``--sort=-committerdate`` ordering, the
``%(refname:short)`` output format, and ``git show <ref>:<path>``.

Run: ``pytest tests/test_agentic_sync_fallback_realgit.py``
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
from contextlib import ExitStack
from pathlib import Path
from typing import Dict, List
from unittest.mock import patch

import pytest

from pdd.agentic_sync import (
    _augment_architecture_from_pr_branch,
    _filter_invalid_basenames,
    run_agentic_sync,
)

ISSUE = 1609

# Architecture entries use the same {filename, filepath} shape the production code reads.
FOO: Dict[str, str] = {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"}
NEW: Dict[str, str] = {"filename": "new_module_python.prompt", "filepath": "pdd/new_module.py"}


pytestmark = pytest.mark.skipif(
    shutil.which("git") is None, reason="git binary not available"
)


def _git(work: Path, *args: str, date: str | None = None) -> None:
    """Run a git command in ``work`` with a deterministic, hermetic environment."""
    env = dict(os.environ)
    # Hermetic: ignore the developer's global/system git config and identity so the
    # tests behave identically locally and in CI.
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    env["GIT_TERMINAL_PROMPT"] = "0"
    env.setdefault("GIT_AUTHOR_NAME", "Test")
    env.setdefault("GIT_AUTHOR_EMAIL", "test@example.com")
    env.setdefault("GIT_COMMITTER_NAME", "Test")
    env.setdefault("GIT_COMMITTER_EMAIL", "test@example.com")
    if date is not None:
        # Pin both dates so ``--sort=-committerdate`` is deterministic. Git's
        # committerdate has 1-second granularity; same-second commits would make
        # "newest branch wins" nondeterministic and flake in CI.
        env["GIT_AUTHOR_DATE"] = date
        env["GIT_COMMITTER_DATE"] = date
    subprocess.run(
        ["git", *args], cwd=str(work), env=env, check=True,
        capture_output=True, text=True,
    )


def _write_arch(work: Path, arch: List[Dict[str, str]]) -> None:
    (work / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")


def _make_repo(tmp_path: Path) -> Path:
    """Create a work repo wired to a bare ``origin``; ``main`` carries local arch [FOO]."""
    origin = tmp_path / "origin.git"
    work = tmp_path / "work"
    subprocess.run(["git", "init", "--bare", str(origin)], check=True, capture_output=True)
    subprocess.run(["git", "init", str(work)], check=True, capture_output=True)
    _write_arch(work, [FOO])
    _git(work, "add", "architecture.json")
    _git(work, "commit", "-m", "init", date="2026-01-01T00:00:00 +0000")
    # Rename the initial branch to a known name regardless of the git version's
    # default (`git init -b` / init.defaultBranch need git >= 2.28; `branch -M`
    # works everywhere). The function never reads this branch, but the helpers
    # branch from it consistently.
    _git(work, "branch", "-M", "main")
    _git(work, "remote", "add", "origin", str(origin))
    _git(work, "push", "-u", "origin", "main")
    return work


def _add_remote_branch(work: Path, name: str, arch: List[Dict[str, str]], date: str) -> None:
    """Branch ``name`` from main with ``arch``, push it to origin, return to main."""
    _git(work, "checkout", "-b", name, "main")
    _write_arch(work, arch)
    _git(work, "add", "architecture.json")
    _git(work, "commit", "-m", name, date=date)
    _git(work, "push", "origin", name)
    _git(work, "checkout", "main")


def _refresh_remote_tracking(work: Path) -> None:
    """Populate refs/remotes/origin/* exactly as a real pre-merge `pdd sync` checkout has."""
    _git(work, "fetch", "origin")


# --------------------------------------------------------------------------------------
# PRIMARY regression: the pure #1609 repro — canonical branch ABSENT.
# This is RED on origin/main's hardcoded-ref code and GREEN on the fix.
# --------------------------------------------------------------------------------------
def test_new_module_on_fallback_branch_survives_basename_filter(tmp_path):
    """Clean-restart fell back to change/issue-N-job-*; canonical change/issue-N does
    NOT exist. The new module lives only on the fallback branch. Augmentation must
    merge it so ``_filter_invalid_basenames`` does not reject it as a hallucination."""
    work = _make_repo(tmp_path)
    _add_remote_branch(work, f"change/issue-{ISSUE}-job-abc123", [FOO, NEW], "2026-02-01T00:00:00 +0000")
    # Canonical change/issue-1609 is deliberately NOT created (this is the repro).
    _refresh_remote_tracking(work)

    augmented = _augment_architecture_from_pr_branch([dict(FOO)], work, ISSUE)

    names = {e["filename"] for e in augmented}
    assert "new_module_python.prompt" in names, (
        f"new module on the job-* fallback branch was not augmented (got {names}); "
        "main's hardcoded origin/change/issue-N ref misses the fallback branch."
    )
    valid, invalid = _filter_invalid_basenames(["foo", "new_module"], augmented)
    assert "new_module" in valid, f"new module wrongly rejected by basename filter; invalid={invalid}"
    assert invalid == [], f"no basename should be rejected as a hallucination; invalid={invalid}"


# --------------------------------------------------------------------------------------
# Regression-safety: the common path is unchanged when no job-* branches exist.
# GREEN on BOTH origin/main and the fix (it does not discriminate; it proves no regression).
# --------------------------------------------------------------------------------------
def test_common_path_canonical_only_still_augments(tmp_path):
    """No clean-restart: only the canonical change/issue-N branch exists. The new module
    on canonical must still be merged — i.e. the fix did not break the pre-existing path."""
    work = _make_repo(tmp_path)
    _add_remote_branch(work, f"change/issue-{ISSUE}", [FOO, NEW], "2026-02-01T00:00:00 +0000")
    _refresh_remote_tracking(work)

    augmented = _augment_architecture_from_pr_branch([dict(FOO)], work, ISSUE)

    names = {e["filename"] for e in augmented}
    assert "new_module_python.prompt" in names, (
        f"canonical-branch new module must still be augmented in the common path (got {names})"
    )


def test_no_change_branches_returns_original(tmp_path):
    """Neither canonical nor any job-* branch exists: augmentation is a no-op."""
    work = _make_repo(tmp_path)
    _refresh_remote_tracking(work)

    augmented = _augment_architecture_from_pr_branch([dict(FOO)], work, ISSUE)

    assert [e["filename"] for e in augmented] == ["foo_python.prompt"]


# --------------------------------------------------------------------------------------
# Edge: multiple job-* branches — only the newest (by committerdate) is consulted.
# Deterministic via pinned commit dates (1s granularity would otherwise flake).
# --------------------------------------------------------------------------------------
def test_newest_job_branch_wins_and_stale_one_is_not_revived(tmp_path):
    """Two clean-restart attempts leave two job-* branches. Only the newest is read;
    a stale module on the older, abandoned job branch must NOT be revived."""
    work = _make_repo(tmp_path)
    stale = {"filename": "stale_module_python.prompt", "filepath": "pdd/stale_module.py"}
    # Older branch (earlier date) carries the stale module...
    _add_remote_branch(work, f"change/issue-{ISSUE}-job-old", [FOO, stale], "2026-02-01T00:00:00 +0000")
    # ...newer branch (later date) carries the real new module.
    _add_remote_branch(work, f"change/issue-{ISSUE}-job-new", [FOO, NEW], "2026-03-01T00:00:00 +0000")
    _refresh_remote_tracking(work)

    augmented = _augment_architecture_from_pr_branch([dict(FOO)], work, ISSUE)

    names = {e["filename"] for e in augmented}
    assert "new_module_python.prompt" in names, "newest job branch's module should be merged"
    assert "stale_module_python.prompt" not in names, (
        "a module from the older, abandoned job branch must not be revived"
    )


# --------------------------------------------------------------------------------------
# Edge: shared filename — the active fallback's metadata wins the dedup over stale canonical.
# Locks in the round-2 ordering decision (branch_refs = fallback_refs[:1] + [canonical]).
# --------------------------------------------------------------------------------------
def test_active_fallback_metadata_wins_over_stale_canonical(tmp_path):
    """Both canonical and the active fallback define the same filename. Clean-restart
    abandons canonical, so its metadata is stale; the active fallback's entry must win."""
    work = _make_repo(tmp_path)
    canonical_entry = {"filename": "shared_python.prompt", "filepath": "pdd/stale_location.py"}
    active_entry = {"filename": "shared_python.prompt", "filepath": "pdd/active_location.py"}
    _add_remote_branch(work, f"change/issue-{ISSUE}", [FOO, canonical_entry], "2026-02-01T00:00:00 +0000")
    _add_remote_branch(work, f"change/issue-{ISSUE}-job-abc", [FOO, active_entry], "2026-03-01T00:00:00 +0000")
    _refresh_remote_tracking(work)

    augmented = _augment_architecture_from_pr_branch([dict(FOO)], work, ISSUE)

    shared = [e for e in augmented if e["filename"] == "shared_python.prompt"]
    assert len(shared) == 1, f"shared filename must be deduped to a single entry, got {shared}"
    assert shared[0]["filepath"] == "pdd/active_location.py", (
        f"active fallback metadata should win the dedup, got {shared[0]['filepath']}"
    )


# --------------------------------------------------------------------------------------
# WORKFLOW-LEVEL regression: the complete run_agentic_sync(dry_run=True) path.
#
# Hermetic — mocks only the boundaries (GitHub issue fetch, LLM module identification,
# and the dry-run subprocess, which would need real module files on disk). The code
# exercised for real is the part the bug lives in: load architecture from disk, augment
# from the fallback ref, basename-filter, build the dependency graph, and reach the
# dry-run sync plan. RED on origin/main (returns "No valid modules to sync"); GREEN on
# the fix. This proves the reported user workflow is fixed end to end, not just the
# helper in isolation.
# --------------------------------------------------------------------------------------
def test_workflow_fallback_only_module_reaches_sync_plan(tmp_path, monkeypatch):
    """A clean-restart change PR lives on origin/change/issue-N-job-*; `pdd sync
    <issue-url>` runs from the main checkout; the LLM identifies the fallback-only new
    module. It must survive basename filtering and reach the sync plan instead of
    returning "No valid modules to sync"."""
    work = _make_repo(tmp_path)
    _add_remote_branch(work, f"change/issue-{ISSUE}-job-abc", [FOO, NEW], "2026-02-01T00:00:00 +0000")
    # Canonical change/issue-N is deliberately absent — the clean-restart fallback case.
    _refresh_remote_tracking(work)
    monkeypatch.chdir(work)

    issue_json = json.dumps({
        "title": "new module on clean-restart fallback branch",
        "body": "sync should pick up the fallback-only module",
        "comments_url": "",
    })

    def fake_dry_run(modules, project_root, quiet=False, verbose=False, reasoning_time=None):
        # The real dry-run shells out to `pdd` and needs the module's files on disk;
        # new_module exists only as an architecture entry, so stub a passing validation.
        return True, {m: project_root for m in modules}, {m: m for m in modules}, [], 0.0

    with ExitStack() as stack:
        def p(name, **kw):
            return stack.enter_context(patch(f"pdd.agentic_sync.{name}", **kw))

        p("_check_gh_cli", return_value=True)
        p("_run_gh_command", return_value=(True, issue_json))            # GitHub issue fetch
        p("load_prompt_template", return_value="identify-modules")
        p("_detect_modules_from_branch_diff", return_value=[])           # force the LLM path
        p("_branch_diff_is_runtime_llm_only", return_value=False)
        p("run_agentic_task", return_value=(True, "{}", 0.0, "mock-provider"))
        # Module-identification output (suffixed basename, the convention the real
        # strip logic at agentic_sync.py:2098 reduces to "new_module").
        p("_parse_llm_response", return_value=(["new_module_python"], True, []))
        p("_filter_already_synced", side_effect=lambda mods, cwds, **kw: mods)
        dry_run_mock = p("_run_dry_run_validation", side_effect=fake_dry_run)

        success, msg, _cost, _provider = run_agentic_sync(
            f"https://github.com/promptdriven/pdd/issues/{ISSUE}",
            dry_run=True,
            quiet=True,
            use_github_state=False,
        )

    assert success is True, (
        f"fallback-only new module should reach the sync plan, but run_agentic_sync "
        f"returned success={success}, msg={msg!r} (on the unfixed code this is "
        f'"No valid modules to sync")'
    )
    assert "Dry run complete" in msg, f"expected a dry-run plan message, got: {msg!r}"
    assert dry_run_mock.called, "new_module never reached dry-run / runner scheduling"
    called_modules = dry_run_mock.call_args.kwargs["modules"]
    assert "new_module" in called_modules, (
        f"new_module did not reach the dry-run stage; modules={called_modules}"
    )
