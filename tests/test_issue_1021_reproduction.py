"""Reproduction tests for issue #1021.

Bug: ``pdd.ci_drift_heal.commit_and_push`` uses ``git add -A`` which
indiscriminately stages every untracked file in the working tree —
including arbitrary ``.pdd/meta/*.json`` fingerprint artifacts created
by tests, examples, or other temporary workflows that are NOT in the
heal scope. PR #1009 demonstrated this when auto-heal reintroduced
``.pdd/meta/calc_python.json``, ``.pdd/meta/calculator_python.json``,
and ``.pdd/meta/src_module1_python.json`` after they were manually
removed.

Expected behavior (asserted by these tests):
- Auto-heal must NOT commit untracked ``.pdd/meta/*.json`` files for
  modules that were never part of the heal scope.
- It MAY still commit modifications to already-tracked metadata files
  (those are repo source-of-truth) and metadata for the healed module
  itself.

These tests will FAIL on the current buggy implementation (because
``git add -A`` stages everything) and should PASS after the fix.
"""
from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.ci_drift_heal import DriftInfo, commit_and_push


def _run(cmd, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, cwd=cwd, check=True, capture_output=True, text=True
    )


def _init_git_repo(repo: Path) -> None:
    """Initialize an isolated git repo with deterministic identity."""
    _run(["git", "init", "-q", "-b", "main"], cwd=repo)
    _run(["git", "config", "user.email", "issue1021@example.com"], cwd=repo)
    _run(["git", "config", "user.name", "Issue 1021 Test"], cwd=repo)
    _run(["git", "config", "commit.gpgsign", "false"], cwd=repo)


def _commit_committed_files(repo: Path) -> None:
    """Add and commit a single placeholder file so HEAD exists."""
    (repo / "README.md").write_text("seed\n", encoding="utf-8")
    _run(["git", "add", "README.md"], cwd=repo)
    _run(["git", "commit", "-q", "-m", "seed"], cwd=repo)


def _staged_files(repo: Path) -> set[str]:
    """Return the set of files staged in the most recent commit."""
    result = subprocess.run(
        ["git", "show", "--name-only", "--pretty=", "HEAD"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    return {line.strip() for line in result.stdout.splitlines() if line.strip()}


@pytest.fixture
def tmp_repo(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Provide an initialized temp git repo and chdir into it."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _init_git_repo(repo)
    _commit_committed_files(repo)
    monkeypatch.chdir(repo)
    return repo


def _patch_push_to_noop():
    """Block ``git push`` so the test never tries to reach a remote."""
    real_run = subprocess.run

    def fake_run(cmd, *args, **kwargs):
        if isinstance(cmd, (list, tuple)) and list(cmd[:2]) == ["git", "push"]:
            class _R:
                returncode = 0
                stdout = ""
                stderr = ""
            return _R()
        return real_run(cmd, *args, **kwargs)

    return patch("pdd.ci_drift_heal.subprocess.run", side_effect=fake_run)


class TestIssue1021AutoHealMetadataLeak:
    """Verify auto-heal does not stage untracked .pdd/meta/*.json artifacts."""

    def test_untracked_metadata_artifacts_are_not_committed(self, tmp_repo: Path):
        """Untracked .pdd/meta/*.json files for unrelated modules must
        not be staged by auto-heal's commit step.

        Reproduces PR #1009 scenario: heal targets ``auth`` but the
        working tree also contains untracked metadata fingerprint files
        for ``calc``, ``calculator`` and ``src_module1`` (left behind
        by tests/examples). The current ``git add -A`` implementation
        would sweep all three into the commit.
        """
        # Healed module produces a legitimate (in-scope) source change.
        auth_src = tmp_repo / "pdd" / "auth.py"
        auth_src.parent.mkdir(parents=True, exist_ok=True)
        auth_src.write_text("# healed module source\n", encoding="utf-8")

        # Stray untracked metadata artifacts from unrelated modules
        # (e.g. left over from local test runs / examples).
        meta_dir = tmp_repo / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)
        unrelated_artifacts = [
            meta_dir / "calc_python.json",
            meta_dir / "calculator_python.json",
            meta_dir / "src_module1_python.json",
        ]
        for f in unrelated_artifacts:
            # One file mirrors the issue's "null hashes" repro evidence.
            f.write_text('{"prompt_hash": null, "code_hash": null}\n', encoding="utf-8")

        with _patch_push_to_noop():
            ok = commit_and_push(
                [DriftInfo(basename="auth", language="python", operation="update", reason="")],
                skip_ci=False,
                checkpoint=False,
            )

        assert ok is True, "commit_and_push should succeed in this fixture"

        committed = _staged_files(tmp_repo)

        leaked = sorted(
            p for p in committed if p.startswith(".pdd/meta/") and "auth" not in p
        )
        assert not leaked, (
            "Auto-heal committed unrelated .pdd/meta/*.json artifacts: "
            f"{leaked}. These files were untracked artifacts for modules "
            "that were never part of the heal scope and must not be staged."
        )

    def test_tracked_metadata_modifications_are_still_committed(self, tmp_repo: Path):
        """Modifications to already-tracked metadata (repo source-of-truth)
        must STILL be committed — only untracked new metadata artifacts
        for unrelated modules should be filtered out.

        This guards against an over-eager fix that would skip ALL
        ``.pdd/meta/*.json`` files (the issue explicitly preserves
        explicitly-allowlisted metadata like
        ``.pdd/meta/update_main_python.json``).
        """
        # Pre-existing tracked metadata file (committed at HEAD).
        meta_dir = tmp_repo / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)
        tracked_meta = meta_dir / "update_main_python.json"
        tracked_meta.write_text('{"version": 1}\n', encoding="utf-8")
        _run(["git", "add", str(tracked_meta.relative_to(tmp_repo))], cwd=tmp_repo)
        _run(["git", "commit", "-q", "-m", "track update_main metadata"], cwd=tmp_repo)

        # Heal modifies that tracked metadata file (intentional update).
        tracked_meta.write_text('{"version": 2}\n', encoding="utf-8")

        # And a stray untracked artifact appears alongside it.
        stray = meta_dir / "calc_python.json"
        stray.write_text('{"prompt_hash": null}\n', encoding="utf-8")

        with _patch_push_to_noop():
            ok = commit_and_push(
                [DriftInfo(basename="update_main", language="python", operation="update", reason="")],
                skip_ci=False,
                checkpoint=False,
            )

        assert ok is True

        committed = _staged_files(tmp_repo)

        # Tracked-metadata update MUST be in the commit.
        assert ".pdd/meta/update_main_python.json" in committed, (
            "Modifications to tracked metadata should remain committed; "
            f"got: {sorted(committed)}"
        )
        # Untracked stray must NOT be in the commit.
        assert ".pdd/meta/calc_python.json" not in committed, (
            "Untracked .pdd/meta/calc_python.json artifact was leaked "
            "into the auto-heal commit."
        )


class TestIssue1021StageHealFromSubdirectory:
    """Verify ``_stage_heal_changes`` stages new heal-owned files even
    when invoked from a subdirectory of the repository.

    Bug: ``_git_add_pathspecs`` was called without ``cwd=repo_root``,
    so its existence check resolved repo-relative paths against the
    caller's CWD. When auto-heal ran from a subdirectory, legitimate
    new prompt/example/source files would be silently dropped from the
    commit.
    """

    def test_new_heal_files_are_staged_when_run_from_subdirectory(
        self, tmp_repo: Path, monkeypatch: pytest.MonkeyPatch
    ):
        from pdd.ci_drift_heal import DriftInfo

        # New heal-owned files at nested paths (untracked in the repo).
        auth_src = tmp_repo / "pdd" / "auth.py"
        auth_src.parent.mkdir(parents=True, exist_ok=True)
        auth_src.write_text("# new healed module source\n", encoding="utf-8")

        auth_prompt = tmp_repo / "pdd" / "prompts" / "auth_python.prompt"
        auth_prompt.parent.mkdir(parents=True, exist_ok=True)
        auth_prompt.write_text("Healed prompt body\n", encoding="utf-8")

        module = DriftInfo(
            basename="auth",
            language="python",
            operation="sync",
            reason="test",
            code_path=str(auth_src),
            prompt_path=str(auth_prompt),
        )

        # Run from a subdirectory (not the repo root) so a missing
        # cwd= would cause _git_add_pathspecs to skip these new files.
        subdir = tmp_repo / "pdd"
        monkeypatch.chdir(subdir)

        with _patch_push_to_noop():
            ok = commit_and_push([module], skip_ci=False, checkpoint=False)

        assert ok is True, "commit_and_push should succeed in this fixture"

        committed = _staged_files(tmp_repo)
        assert "pdd/auth.py" in committed, (
            "New heal-owned file pdd/auth.py was not committed when "
            f"auto-heal ran from a subdirectory. Committed files: "
            f"{sorted(committed)}"
        )
        assert "pdd/prompts/auth_python.prompt" in committed, (
            "New heal-owned prompt was not committed when auto-heal ran "
            f"from a subdirectory. Committed files: {sorted(committed)}"
        )


class TestIssue1021StageGeneratedExampleAfterUpdateHeal:
    """Verify ``_healed_module_file_relpaths`` resolves missing
    ``example_path`` (and other unset path attributes) via
    ``get_pdd_file_paths`` so files generated by a heal step still get
    staged.

    Bug: when ``--modules`` finds a code file with no prompt, the
    ``DriftInfo`` starts with ``example_path=None``; the update branch
    in ``heal_module()`` runs ``pdd example`` after the prompt is
    regenerated but never writes the new path back onto the dataclass.
    Because the staging logic only added paths from existing attributes,
    the freshly generated example file was silently omitted from the
    auto-heal commit (the prior ``git add -A`` had masked this).
    """

    def test_generated_example_with_unset_attr_is_staged(
        self, tmp_repo: Path, monkeypatch: pytest.MonkeyPatch
    ):
        from pdd.ci_drift_heal import DriftInfo

        # Healed module: source + prompt exist on disk and are tracked
        # via the DriftInfo, but example_path was never resolved (the
        # update-then-example heal flow leaves the attribute as None).
        src = tmp_repo / "pdd" / "auth.py"
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("# healed source\n", encoding="utf-8")

        prompt = tmp_repo / "prompts" / "auth_python.prompt"
        prompt.parent.mkdir(parents=True, exist_ok=True)
        prompt.write_text("Healed prompt body\n", encoding="utf-8")

        # The example file that ``pdd example`` would have produced.
        # ``get_pdd_file_paths('auth', 'python')`` defaults to
        # ``examples/auth_example.py`` when no .pddrc is configured.
        example = tmp_repo / "examples" / "auth_example.py"
        example.parent.mkdir(parents=True, exist_ok=True)
        example.write_text("# generated example\n", encoding="utf-8")

        module = DriftInfo(
            basename="auth",
            language="python",
            operation="update",
            reason="code-without-prompt",
            code_path=str(src),
            prompt_path=str(prompt),
            example_path=None,  # ← the bug: never written back by heal
        )

        with _patch_push_to_noop():
            ok = commit_and_push([module], skip_ci=False, checkpoint=False)
        assert ok is True, "commit_and_push should succeed in this fixture"

        committed = _staged_files(tmp_repo)
        assert "examples/auth_example.py" in committed, (
            "Generated example file was not committed even though the "
            "heal step created it. DriftInfo.example_path was None and "
            "the staging helper failed to fall back to "
            "get_pdd_file_paths(). Committed files: "
            f"{sorted(committed)}"
        )


class TestIssue1021CheckupReviewLoopMetadataLeak:
    """Verify the parallel review-loop commit path also does not leak
    untracked ``.pdd/meta/*.json`` artifacts.

    Step 6's grep verification updated ``FIX_LOCATIONS`` to include
    ``pdd/checkup_review_loop.py`` because
    ``_commit_and_push_if_changed`` uses the same buggy ``git add -A``
    pattern as ``ci_drift_heal.commit_and_push``. A fix that only
    touches the auto-heal path would still leak untracked metadata
    artifacts when the review-loop fixer commits to a PR branch.
    """

    def test_review_loop_commit_does_not_leak_untracked_metadata(
        self, tmp_repo: Path
    ):
        """Untracked ``.pdd/meta/*.json`` files must not be staged by
        the review-loop commit step either.

        The review loop's ``_commit_and_push_if_changed`` operates on a
        worktree and currently runs ``git add -A`` (see
        ``pdd/checkup_review_loop.py:3188``). On the buggy code, stray
        ``.pdd/meta/*.json`` files for unrelated modules in the
        worktree are swept into the fix commit just like in auto-heal.
        """
        from pdd import checkup_review_loop as crl

        # A real in-scope fixer change to commit.
        fix_src = tmp_repo / "pdd" / "review_fix.py"
        fix_src.parent.mkdir(parents=True, exist_ok=True)
        fix_src.write_text("# review-loop fix change\n", encoding="utf-8")

        # Untracked, out-of-scope metadata artifacts in the worktree.
        meta_dir = tmp_repo / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)
        for name in (
            "calc_python.json",
            "calculator_python.json",
            "src_module1_python.json",
        ):
            (meta_dir / name).write_text(
                '{"prompt_hash": null, "code_hash": null}\n',
                encoding="utf-8",
            )

        pr_metadata = {
            "clone_url": "https://example.invalid/x.git",
            "head_ref": "feature/review-loop-fix",
            "head_owner": "promptdriven",
            "head_repo": "pdd",
        }

        # Block the network push but let local git add/commit run.
        with patch.object(
            crl, "push_with_retry", return_value=(True, "")
        ) as mock_push:
            pushed, message, pushed_sha = crl._commit_and_push_if_changed(
                tmp_repo,
                pr_metadata,
                "fix: address reviewer findings",
            )

        # push_with_retry should be invoked once the local commit lands.
        mock_push.assert_called()
        assert pushed is True, f"_commit_and_push_if_changed failed: {message}"
        # `pushed_sha` is the new (#1062) 3rd element: a real commit
        # SHA after a successful push. The exact value depends on the
        # underlying git invocations in this test's `tmp_repo` fixture
        # so we only assert presence here — the SHA itself is the
        # responsibility of `_git_head_sha`, which has its own tests.
        assert pushed_sha is not None and pushed_sha != ""

        committed = _staged_files(tmp_repo)
        leaked = sorted(
            p
            for p in committed
            if p.startswith(".pdd/meta/")
            and not p.endswith("review_fix_python.json")
        )
        assert not leaked, (
            "Review-loop commit leaked untracked .pdd/meta/*.json "
            f"artifacts: {leaked}. These files were never part of the "
            "fixer's scope and must not be staged."
        )


class TestIssue1021StageNewlyCreatedAutoDepsCsv:
    """Verify ``_stage_heal_changes`` stages a freshly created
    ``project_dependencies.csv`` after an ``auto-deps`` heal.

    Bug: when a repo does not yet track ``project_dependencies.csv``,
    ``pdd auto-deps`` writes it as a brand-new file. The scoped staging
    step uses ``git add -u`` plus per-module pathspecs, neither of
    which picks up an untracked CSV at the repo root, so a successful
    auto-deps heal would commit prompt updates while silently dropping
    the generated dependency CSV.
    """

    def test_new_project_dependencies_csv_is_staged_for_auto_deps(
        self, tmp_repo: Path
    ):
        # Heal would have produced a fresh, repo-root project_dependencies.csv.
        csv_path = tmp_repo / "project_dependencies.csv"
        assert not csv_path.exists()
        csv_path.write_text(
            "module,dependency\nauth,utils\n", encoding="utf-8"
        )

        # And a normal source change for the healed module so there is
        # at least one tracked-side change for the commit.
        src = tmp_repo / "pdd" / "auth.py"
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("# auto-deps healed source\n", encoding="utf-8")

        drift = DriftInfo(
            basename="auth",
            language="python",
            operation="auto-deps",
            reason="dependency drift",
            code_path=str(src),
        )

        with _patch_push_to_noop():
            ok = commit_and_push([drift], skip_ci=False, checkpoint=False)

        assert ok is True, "commit_and_push should succeed in this fixture"

        committed = _staged_files(tmp_repo)
        assert "project_dependencies.csv" in committed, (
            "Newly created project_dependencies.csv was not committed "
            "after an auto-deps heal. The staging step must explicitly "
            "include it because `git add -u` ignores untracked files. "
            f"Committed files: {sorted(committed)}"
        )


class TestIssue1021StageSkipsGitignoredRunReports:
    """Verify ``_git_add_pathspecs`` skips gitignored paths.

    Bug: ``_healed_module_metadata_relpaths`` returns both the tracked
    ``.pdd/meta/<base>_<lang>.json`` fingerprint AND the untracked
    ``.pdd/meta/<base>_<lang>_run.json`` per-run report. The repo's
    ``.gitignore`` excludes ``.pdd/meta/*_run.json``, so passing the
    run.json into ``git add`` makes Git exit non-zero with
    "paths are ignored", which aborts the entire heal commit even
    though the source/prompt fixes were valid.
    """

    def test_gitignored_run_report_is_skipped_and_commit_succeeds(
        self, tmp_repo: Path
    ):
        # Repo ignores the per-run report file (real repo's policy).
        (tmp_repo / ".gitignore").write_text(
            ".pdd/meta/*_run.json\n", encoding="utf-8"
        )
        _run(["git", "add", ".gitignore"], cwd=tmp_repo)
        _run(["git", "commit", "-q", "-m", "add gitignore"], cwd=tmp_repo)

        # Tracked source change for the healed module.
        src = tmp_repo / "pdd" / "foo.py"
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("# original\n", encoding="utf-8")
        _run(["git", "add", "pdd/foo.py"], cwd=tmp_repo)
        _run(["git", "commit", "-q", "-m", "seed foo"], cwd=tmp_repo)
        src.write_text("# healed source change\n", encoding="utf-8")

        # The heal step writes both metadata files. The fingerprint is
        # stageable; the run report is gitignored.
        meta_dir = tmp_repo / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)
        (meta_dir / "foo_python.json").write_text(
            '{"prompt_hash": "abc"}\n', encoding="utf-8"
        )
        (meta_dir / "foo_python_run.json").write_text(
            '{"run": "report"}\n', encoding="utf-8"
        )

        drift = DriftInfo(
            basename="foo",
            language="python",
            operation="update",
            reason="prompt drift",
            code_path=str(src),
        )

        head_before = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=tmp_repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

        with _patch_push_to_noop():
            ok = commit_and_push([drift], skip_ci=False, checkpoint=False)

        assert ok is True, (
            "commit_and_push must succeed even when the heal produced a "
            "gitignored run-report file alongside stageable changes."
        )

        head_after = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=tmp_repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        assert head_after != head_before, "Expected a new commit on HEAD."

        committed = _staged_files(tmp_repo)
        assert ".pdd/meta/foo_python_run.json" not in committed, (
            "Gitignored run-report file must NOT appear in the commit. "
            f"Committed files: {sorted(committed)}"
        )
        assert "pdd/foo.py" in committed, (
            "Tracked source change should still be committed. "
            f"Committed files: {sorted(committed)}"
        )


class TestIssue1021StageGeneratedExampleFromSubdirectory:
    """Verify the ``get_pdd_file_paths`` fallback in
    ``_healed_module_file_relpaths`` is anchored at ``repo_root``, not the
    caller's CWD.

    Bug: when ``commit_and_push`` is invoked from a subdirectory and a
    healed ``DriftInfo`` has ``example_path=None`` (the code-without-prompt
    update flow never writes the path back), the fallback call to
    ``get_pdd_file_paths`` resolved ``examples/`` relative to the current
    subdirectory. The path it returned (e.g. ``pdd/examples/auth_example.py``)
    didn't exist, so the real ``examples/auth_example.py`` was silently
    omitted from the scoped staging step.
    """

    def test_generated_example_with_unset_attr_is_staged_from_subdir(
        self, tmp_repo: Path, monkeypatch: pytest.MonkeyPatch
    ):
        from pdd.ci_drift_heal import DriftInfo

        # Healed-module source + prompt at real repo-root-relative paths.
        src = tmp_repo / "pdd" / "auth.py"
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("# healed source\n", encoding="utf-8")

        prompt = tmp_repo / "prompts" / "auth_python.prompt"
        prompt.parent.mkdir(parents=True, exist_ok=True)
        prompt.write_text("Healed prompt body\n", encoding="utf-8")

        # Generated example at the real repo-root-relative path.
        example = tmp_repo / "examples" / "auth_example.py"
        example.parent.mkdir(parents=True, exist_ok=True)
        example.write_text("# generated example\n", encoding="utf-8")

        module = DriftInfo(
            basename="auth",
            language="python",
            operation="update",
            reason="code-without-prompt",
            code_path=str(src),
            prompt_path=str(prompt),
            example_path=None,  # ← forces the fallback path resolution.
        )

        # Run from a subdirectory: ``get_pdd_file_paths`` would otherwise
        # resolve ``examples/`` relative to CWD (=> pdd/examples/...) and
        # the real examples/auth_example.py would not be staged.
        subdir = tmp_repo / "pdd"
        monkeypatch.chdir(subdir)

        with _patch_push_to_noop():
            ok = commit_and_push([module], skip_ci=False, checkpoint=False)
        assert ok is True, "commit_and_push should succeed in this fixture"

        committed = _staged_files(tmp_repo)
        assert "examples/auth_example.py" in committed, (
            "Generated example file was not committed when commit_and_push "
            "ran from a subdirectory. The fallback path lookup must be "
            "anchored at repo_root, not the caller's CWD. "
            f"Committed files: {sorted(committed)}"
        )
