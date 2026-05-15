from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path

import pytest

from pdd.durable_sync_runner import (
    DurableSyncRunner,
    _parse_checkpoint_trailer,
    _pdd_path_index,
    _slugify_basename,
)


def _git(cwd: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=True,
    )


def _init_repo_with_remote(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    remote = tmp_path / "origin.git"
    repo.mkdir()
    _git(tmp_path, "init", "--bare", str(remote))
    _git(tmp_path, "init", "-b", "main", str(repo))
    _git(repo, "config", "user.name", "Test User")
    _git(repo, "config", "user.email", "test@example.invalid")
    (repo / ".gitignore").write_text(".pdd/\n", encoding="utf-8")
    (repo / "README.md").write_text("initial\n", encoding="utf-8")
    _git(repo, "add", ".gitignore", "README.md")
    _git(repo, "commit", "-m", "initial")
    _git(repo, "remote", "add", "origin", str(remote))
    _git(repo, "push", "-u", "origin", "main")
    _git(repo, "symbolic-ref", "refs/remotes/origin/HEAD", "refs/remotes/origin/main")
    return repo


class EmptyDurableRunner(DurableSyncRunner):
    def _run_child_sync(self, basename: str):
        return True, 0.0, ""


class MetadataDurableRunner(DurableSyncRunner):
    def _run_child_sync(self, basename: str):
        cwd = self.module_cwds[basename]
        (cwd / "README.md").write_text("updated\n", encoding="utf-8")
        meta_dir = cwd / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)
        (meta_dir / "foo_python.json").write_text(
            json.dumps({"module": basename}),
            encoding="utf-8",
        )
        return True, 0.0, ""


class PushFailingMetadataRunner(MetadataDurableRunner):
    def _push_durable_head(self):
        return False, "simulated push outage"


class MultiModuleDurableRunner(DurableSyncRunner):
    def _run_child_sync(self, basename: str):
        cwd = self.module_cwds[basename]
        (cwd / f"{basename}.txt").write_text(f"synced {basename}\n", encoding="utf-8")
        return True, 0.0, ""


class FailCDurableRunner(MultiModuleDurableRunner):
    def _run_child_sync(self, basename: str):
        if basename == "c":
            return False, 0.0, "simulated c failure"
        return super()._run_child_sync(basename)


def _runner(repo: Path, runner_cls=EmptyDurableRunner, **kwargs) -> DurableSyncRunner:
    sync_options = kwargs.pop("sync_options", {})
    basenames = kwargs.pop("basenames", ["foo"])
    dep_graph = kwargs.pop(
        "dep_graph",
        {basename: [] for basename in basenames},
    )
    issue_number = kwargs.pop("issue_number", 1328)
    return runner_cls(
        basenames=basenames,
        dep_graph=dep_graph,
        sync_options=sync_options,
        github_info=None,
        issue_number=issue_number,
        project_root=repo,
        quiet=True,
        issue_url=f"https://github.com/org/repo/issues/{issue_number}",
        **kwargs,
    )


def test_parse_checkpoint_trailer_requires_supported_version_and_fields():
    assert _parse_checkpoint_trailer(
        "PDD-Sync-Checkpoint-V1: issue=1328 module=src/foo"
    ) == (1328, "src/foo")
    assert _parse_checkpoint_trailer(
        "PDD-Sync-Checkpoint-V2: issue=1328 module=src/foo"
    ) is None
    assert _parse_checkpoint_trailer("PDD-Sync-Checkpoint-V1: module=src/foo") is None


def test_slugify_basename_adds_digest_to_avoid_worktree_name_collisions():
    assert _slugify_basename("foo/bar") != _slugify_basename("foo-bar")
    assert _slugify_basename("foo/bar").startswith("foo-bar-")


def test_pdd_path_index_finds_root_and_nested_pdd_dirs():
    assert _pdd_path_index(".pdd/meta/foo_python.json") == 0
    assert _pdd_path_index("packages/app/.pdd/meta/foo_python.json") == len("packages/app/")
    assert _pdd_path_index("packages/app/pdd/meta/foo_python.json") is None


def test_durable_runner_refuses_main_branch(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)

    success, message, _ = _runner(repo, durable_branch="main").run()

    assert success is False
    assert "protected branch" in message


def test_durable_runner_refuses_branch_checked_out_elsewhere(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    _git(repo, "checkout", "-b", "feature")

    success, message, _ = _runner(repo, durable_branch="feature").run()

    assert success is False
    assert "already checked out" in message


def test_durable_runner_requires_origin_remote(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(tmp_path, "init", "-b", "main", str(repo))
    _git(repo, "config", "user.name", "Test User")
    _git(repo, "config", "user.email", "test@example.invalid")
    (repo / "README.md").write_text("initial\n", encoding="utf-8")
    _git(repo, "add", "README.md")
    _git(repo, "commit", "-m", "initial")

    success, message, _ = _runner(repo).run()

    assert success is False
    assert "origin remote" in message


def test_durable_runner_fails_early_when_initial_fetch_fails(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    _git(repo, "remote", "set-url", "origin", str(tmp_path / "missing.git"))

    success, message, _ = _runner(repo).run()

    assert success is False
    assert "Failed to fetch durable branch" in message


def test_empty_success_creates_empty_checkpoint_and_marker(tmp_path: Path, capsys):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo)

    success, message, _ = runner.run()

    assert success is True
    assert "All 1 modules synced successfully" in message
    log = _git(repo, "log", "sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=foo" in log
    output = capsys.readouterr().out
    assert "PDD_CHECKPOINT: issue=1328 module=foo" in output
    assert "empty=true" in output


def test_resume_skips_modules_with_matching_issue_trailer(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    first = _runner(repo)
    success, message, _ = first.run()
    assert success is True, message
    before = _git(repo, "rev-list", "--count", "sync/issue-1328").stdout.strip()

    second = _runner(repo)
    success, message, _ = second.run()

    assert success is True, message
    assert second._resumed_modules == ["foo"]
    after = _git(repo, "rev-list", "--count", "sync/issue-1328").stdout.strip()
    assert after == before


def test_no_resume_ignores_existing_trailer_and_appends_checkpoint(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    first = _runner(repo)
    success, message, _ = first.run()
    assert success is True, message
    before = int(_git(repo, "rev-list", "--count", "sync/issue-1328").stdout.strip())

    second = _runner(repo, no_resume=True)
    success, message, _ = second.run()

    assert success is True, message
    after = int(_git(repo, "rev-list", "--count", "sync/issue-1328").stdout.strip())
    assert after == before + 1


def test_trailers_from_other_issues_do_not_resume_current_issue(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    other_issue = _runner(repo, issue_number=999, durable_branch="sync/shared")
    success, message, _ = other_issue.run()
    assert success is True, message
    _git(repo, "worktree", "remove", "--force", str(other_issue.durable_worktree_path))

    current_issue = _runner(repo, durable_branch="sync/shared")
    success, message, _ = current_issue.run()

    assert success is True, message
    assert current_issue._resumed_modules == []
    log = _git(repo, "log", "sync/shared", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V1: issue=999 module=foo" in log
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=foo" in log


def test_module_metadata_is_force_added_even_when_pdd_dir_is_ignored(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, runner_cls=MetadataDurableRunner)

    success, message, _ = runner.run()

    assert success is True, message
    metadata = _git(repo, "show", "sync/issue-1328:.pdd/meta/foo_python.json").stdout
    assert json.loads(metadata) == {"module": "foo"}
    readme = _git(repo, "show", "sync/issue-1328:README.md").stdout
    assert readme == "updated\n"


def test_nested_module_metadata_is_force_added_for_module_cwd(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    module_dir = repo / "packages" / "app"
    module_dir.mkdir(parents=True)
    (module_dir / "README.md").write_text("initial\n", encoding="utf-8")
    _git(repo, "add", "packages/app/README.md")
    _git(repo, "commit", "-m", "add nested module")
    _git(repo, "push", "origin", "main")

    runner = _runner(
        repo,
        runner_cls=MetadataDurableRunner,
        module_cwds={"foo": module_dir},
    )

    success, message, _ = runner.run()

    assert success is True, message
    metadata = _git(
        repo,
        "show",
        "sync/issue-1328:packages/app/.pdd/meta/foo_python.json",
    ).stdout
    assert json.loads(metadata) == {"module": "foo"}
    readme = _git(repo, "show", "sync/issue-1328:packages/app/README.md").stdout
    assert readme == "updated\n"


def test_metadata_allowlist_rejects_nested_pdd_state_and_wrong_meta_scope(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    module_dir = repo / "packages" / "app"
    runner = _runner(repo, module_cwds={"foo": module_dir})

    assert runner._unsafe_staged_paths(
        "foo",
        [
            ".pdd/meta/foo_python.json",
            "packages/app/.pdd/meta/foo_typescript.json",
        ],
    ) == []
    assert runner._unsafe_staged_paths(
        "foo",
        [
            "packages/app/.pdd/agentic_sync_state.json",
            "packages/other/.pdd/meta/foo_python.json",
            "packages/app/.pdd/meta/bar_python.json",
        ],
    ) == [
        "packages/app/.pdd/agentic_sync_state.json",
        "packages/app/.pdd/meta/bar_python.json",
        "packages/other/.pdd/meta/foo_python.json",
    ]


def test_unsafe_staged_paths_rejects_sensitive_artifacts(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo)

    unsafe_paths = [
        ".env",
        ".env.local",
        "cost.csv",
        "logs/crash.log",
        "logs/fix_errors.log",
        "certs/client.pem",
        "certs/client.key",
        "config/token.txt",
        "config/secrets/api.txt",
        ".pdd/worktrees/sync-issue-1328-foo",
        ".pdd/agentic_sync_state.json",
        ".pdd/cache/unrelated.json",
    ]
    safe_paths = [
        "src/app.py",
        ".pdd/meta/foo_python.json",
    ]

    result = runner._unsafe_staged_paths("foo", [*unsafe_paths, *safe_paths])

    assert result == sorted(unsafe_paths)


def test_allowed_write_set_rejects_out_of_scope_checkpoint_paths(tmp_path: Path):
    """
    Issue #1013 (F5, F13, F14): kwarg is now ``allowed_write_set`` (the
    ``allowed_write_paths`` alias was removed) and ``.pdd/meta/*.json`` is
    auto-allowed via ``DEFAULT_SYNC_COMPANION_ALLOWLIST`` — only paths
    outside both the contract AND the companion allowlist are rejected.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, allowed_write_set=["src/app.py"])

    assert runner._out_of_scope_staged_paths(
        ["src/app.py", "architecture.json", ".pdd/meta/foo_python.json"],
        "foo",
        repo,
    ) == ["architecture.json"]


def test_allowed_write_set_none_means_permissive_for_durable_runner(tmp_path: Path):
    """
    Issue #1013 (F9): when no contract is parsed (``allowed_write_set=None``),
    durable sync runs in permissive mode — out-of-scope rejection is a no-op.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, allowed_write_set=None)

    assert runner._out_of_scope_staged_paths(
        ["src/app.py", "architecture.json", "anything/else.txt"],
        "foo",
        repo,
    ) == []


def test_allowed_write_set_empty_rejects_everything_for_durable_runner(tmp_path: Path):
    """
    Issue #1013 (F9): explicit empty contract means "reject every primary
    write" — though companion artifacts still pass via the default allowlist.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, allowed_write_set=[])

    result = runner._out_of_scope_staged_paths(
        ["src/app.py", ".pdd/meta/foo_python.json"],
        "foo",
        repo,
    )
    assert result == ["src/app.py"]


def test_wildcard_only_companion_pattern_is_ignored_by_durable_runner(
    tmp_path: Path,
):
    """Iter-10 M-1: even if a wildcard-only pattern (``**/*``) bypasses the
    parser and lands in ``self.companion_allowlist``, the durable runner's
    defense-in-depth filter MUST refuse to treat it as auto-allowing
    repo-wide writes."""
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=["**/*"],
    )

    # ``**/*`` is wildcard-only, so it must NOT auto-allow ``unrelated/file.py``.
    assert runner._out_of_scope_staged_paths(
        ["unrelated/file.py"],
        "foo",
        repo,
    ) == ["unrelated/file.py"]


def test_durable_nested_meta_path_is_not_in_companion_allowlist(
    tmp_path: Path,
):
    """Iter-14 M-2: durable checkpoint scope checking previously used
    ``PurePosixPath.match`` (suffix-based), which falsely matched
    ``subdir/.pdd/meta/foo.json`` against the default top-level
    ``.pdd/meta/*.json`` companion pattern. The anchored matcher MUST
    refuse to auto-allow nested fingerprint-shaped paths, so staged
    nested ``.pdd/meta/*.json`` files surface as out-of-scope and the
    checkpoint is rejected.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    # The nested path is shaped like a fingerprint-meta artifact but
    # sits under ``subdir/`` — the iter-14 M-2 bug shape.
    result = runner._out_of_scope_staged_paths(
        ["subdir/.pdd/meta/bar.json"],
        "foo",
        repo,
    )
    assert result == ["subdir/.pdd/meta/bar.json"], (
        "nested .pdd/meta path must NOT be auto-allowed by the "
        "default top-level companion pattern (iter-14 M-2)"
    )


def test_multi_module_durable_companion_matched_module_relative(
    tmp_path: Path,
):
    """Iter-16 M-1: in a multi-module repo where ``module_cwd`` is a
    SUBDIRECTORY of the worktree (``worktree/pkg``), staged paths
    surface relative to the worktree git root (``pkg/.pdd/meta/foo.json``).
    The companion pattern ``.pdd/meta/*.json`` is module-relative, so the
    durable scope check MUST strip the module_cwd prefix before matching;
    otherwise legitimate fingerprint metadata is rejected and the
    checkpoint commit fails. Mirrors the async-side iter-14 M-1 part-2
    fix.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        basenames=["pkg_mod"],
        module_cwds={"pkg_mod": repo / "pkg"},
        allowed_write_set=["pkg/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    # Staged path is repo-relative (``pkg/.pdd/meta/foo.json``) but the
    # companion pattern describes module-relative metadata. With the
    # iter-16 fix the prefix is stripped and the anchored matcher sees
    # ``.pdd/meta/foo.json`` — a clean match.
    result = runner._out_of_scope_staged_paths(
        ["pkg/.pdd/meta/foo.json"],
        "pkg_mod",
        repo,
    )
    assert result == [], (
        "multi-module durable runner must strip module_cwd prefix before "
        "companion-pattern matching (iter-16 M-1)"
    )


def test_durable_sibling_module_metadata_rejected(tmp_path: Path):
    """Iter-16 M-1 (sibling-module regression for F1 iter-3): when
    ``module_cwd = worktree/pkg``, a sibling module's metadata path like
    ``pkg_other/.pdd/meta/foo.json`` sits OUTSIDE the active module's
    cwd. The companion allowlist must NOT auto-allow it; only files
    UNDER the module's own cwd qualify as companion artifacts.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        basenames=["pkg_mod"],
        module_cwds={"pkg_mod": repo / "pkg"},
        allowed_write_set=["pkg/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    result = runner._out_of_scope_staged_paths(
        ["pkg_other/.pdd/meta/foo.json"],
        "pkg_mod",
        repo,
    )
    assert result == ["pkg_other/.pdd/meta/foo.json"], (
        "sibling-module metadata must NOT be auto-allowed by the "
        "companion allowlist (F1 iter-3 sibling rule, iter-16 M-1)"
    )


def test_single_module_durable_companion_still_matches(tmp_path: Path):
    """Iter-16 M-1 (single-module regression): when ``module_cwd ==
    module_worktree`` (no submodule prefix), top-level
    ``.pdd/meta/foo.json`` must still match the default companion
    pattern. The iter-16 prefix-stripping must be a no-op in this case.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        allowed_write_set=["src/app.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    result = runner._out_of_scope_staged_paths(
        [".pdd/meta/foo.json"],
        "foo",
        repo,
    )
    assert result == [], (
        "single-module durable runner must still auto-allow top-level "
        ".pdd/meta artifacts (iter-16 M-1 single-module regression)"
    )


def test_single_module_durable_nested_meta_not_allowed(tmp_path: Path):
    """Iter-14 M-2 (regression): single-module durable runner with
    ``module_cwd == module_worktree`` must still reject a NESTED
    ``subdir/.pdd/meta/foo.json`` — the anchored matcher refuses
    suffix-style matches, and iter-16's prefix-stripping must not
    weaken that.
    """
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        allowed_write_set=["src/app.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    result = runner._out_of_scope_staged_paths(
        ["subdir/.pdd/meta/foo.json"],
        "foo",
        repo,
    )
    assert result == ["subdir/.pdd/meta/foo.json"], (
        "nested .pdd/meta path must remain out-of-scope under single-"
        "module mode (iter-14 M-2 regression preserved by iter-16)"
    )


def test_staged_rename_source_side_is_scope_checked(tmp_path: Path):
    """Iter-6 B3 (rename detection bug): ``git diff --cached --name-only``
    for a staged ``git mv old new`` emits ONLY ``new``. A contract that
    allows ``new`` but not ``old`` would pass validation while the rename
    silently DELETES the out-of-scope ``old``.

    After the fix the durable runner uses ``--name-status -M`` so both
    sides of the rename surface and the out-of-scope deletion is rejected.
    """
    repo = _init_repo_with_remote(tmp_path)
    (repo / "src").mkdir(exist_ok=True)
    (repo / "src" / "old.py").write_text("contents\n", encoding="utf-8")
    _git(repo, "add", "src/old.py")
    _git(repo, "commit", "-m", "add src/old.py")
    _git(repo, "mv", "src/old.py", "src/new.py")

    runner = _runner(repo, allowed_write_set=["src/new.py"])
    success, message, _empty = runner._stage_module_changes("foo", repo)

    assert not success, (
        "Durable sync must reject a checkpoint that deletes src/old.py "
        "even when the contract permits src/new.py."
    )
    assert "src/old.py" in message, (
        f"Diagnostic must call out the out-of-scope source path; got: {message!r}"
    )


def test_push_failure_preserves_local_checkpoint_and_next_run_pushes_it(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    first = _runner(repo, runner_cls=PushFailingMetadataRunner)

    success, message, _ = first.run()

    assert success is False
    assert "simulated push outage" in message
    local_log = _git(
        first.durable_worktree_path,
        "log",
        "--format=%B",
    ).stdout
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=foo" in local_log

    second = _runner(repo)
    success, message, _ = second.run()

    assert success is True, message
    assert second._resumed_modules == ["foo"]
    _git(repo, "fetch", "origin", "sync/issue-1328")
    remote_log = _git(repo, "log", "origin/sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=foo" in remote_log


def test_non_fast_forward_push_rejection_halts_run(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, runner_cls=MetadataDurableRunner)
    ok, message = runner._prepare_durable_branch()
    assert ok, message
    first_worktree = runner._create_module_worktree("foo")
    success, error = runner._checkpoint_module("foo", first_worktree)
    assert success is True, error
    runner._remove_worktree(first_worktree)

    intruder = tmp_path / "intruder"
    _git(tmp_path, "clone", str(tmp_path / "origin.git"), str(intruder))
    _git(intruder, "config", "user.name", "Other User")
    _git(intruder, "config", "user.email", "other@example.invalid")
    _git(intruder, "checkout", "sync/issue-1328")
    (intruder / "other.txt").write_text("remote change\n", encoding="utf-8")
    _git(intruder, "add", "other.txt")
    _git(intruder, "commit", "-m", "remote change")
    _git(intruder, "push", "origin", "sync/issue-1328")

    second_worktree = runner._create_module_worktree("foo")
    (second_worktree / "second.txt").write_text("second local change\n", encoding="utf-8")
    success, error = runner._checkpoint_module("foo", second_worktree)

    assert success is False
    assert "Checkpoint push rejected" in error
    assert runner._checkpoint_halted.is_set()


def test_fresh_clone_resumes_checkpointed_modules_after_partial_failure(
    tmp_path: Path,
    durable_max_parallel: int | None,
):
    repo = _init_repo_with_remote(tmp_path)
    basenames = ["a", "b", "c"]
    max_parallel = durable_max_parallel or 3
    first = _runner(
        repo,
        runner_cls=FailCDurableRunner,
        basenames=basenames,
        durable_max_parallel=max_parallel,
    )

    success, message, _ = first.run()

    assert success is False
    assert "simulated c failure" in message
    _git(repo, "fetch", "origin", "sync/issue-1328")
    first_remote_log = _git(repo, "log", "origin/sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=a" in first_remote_log
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=b" in first_remote_log
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=c" not in first_remote_log

    fresh = tmp_path / "fresh-worker"
    _git(tmp_path, "clone", str(tmp_path / "origin.git"), str(fresh))
    _git(fresh, "config", "user.name", "Fresh Worker")
    _git(fresh, "config", "user.email", "fresh@example.invalid")
    _git(fresh, "symbolic-ref", "refs/remotes/origin/HEAD", "refs/remotes/origin/main")

    second = _runner(
        fresh,
        runner_cls=MultiModuleDurableRunner,
        basenames=basenames,
        durable_max_parallel=max_parallel,
    )
    success, message, _ = second.run()

    assert success is True, message
    assert sorted(second._resumed_modules) == ["a", "b"]
    _git(fresh, "fetch", "origin", "sync/issue-1328")
    final_log = _git(fresh, "log", "origin/sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=c" in final_log
    assert _git(fresh, "show", "origin/sync/issue-1328:c.txt").stdout == "synced c\n"


def test_halted_checkpoint_prevents_later_in_flight_module_checkpoint(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, runner_cls=MetadataDurableRunner)
    ok, message = runner._prepare_durable_branch()
    assert ok, message
    runner._checkpoint_halted.set()

    success, _, error = runner._sync_one_module("foo")

    assert success is False
    assert "Checkpointing halted" in error
    log = _git(runner.durable_worktree_path, "log", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V1: issue=1328 module=foo" not in log


def test_durable_runner_end_to_end_uses_child_subprocess_and_resumes(
    tmp_path: Path,
    monkeypatch,
    capsys,
):
    repo = _init_repo_with_remote(tmp_path)
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    fake_pdd = bin_dir / "pdd"
    fake_pdd.write_text(
        """#!/usr/bin/env python3
import os
import sys
from pathlib import Path

basename = sys.argv[sys.argv.index("sync") + 1]
Path(f"{basename}.txt").write_text(f"synced {basename}\\n", encoding="utf-8")
meta_dir = Path(".pdd") / "meta"
meta_dir.mkdir(parents=True, exist_ok=True)
(meta_dir / f"{basename}_python.json").write_text('{"ok": true}\\n', encoding="utf-8")
cost_path = os.environ.get("PDD_OUTPUT_COST_PATH")
if cost_path:
    Path(cost_path).write_text("cost\\n0.12\\n", encoding="utf-8")
print("PDD_PHASE: fake")
print("Overall status: Success")
""",
        encoding="utf-8",
    )
    fake_pdd.chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}")

    first = _runner(repo, runner_cls=DurableSyncRunner)
    success, message, cost = first.run()

    assert success is True, message
    assert cost == pytest.approx(0.12)
    assert _git(repo, "show", "sync/issue-1328:foo.txt").stdout == "synced foo\n"
    metadata = _git(repo, "show", "sync/issue-1328:.pdd/meta/foo_python.json").stdout
    assert json.loads(metadata) == {"ok": True}
    assert "PDD_CHECKPOINT: issue=1328 module=foo" in capsys.readouterr().out

    fake_pdd.write_text(
        """#!/usr/bin/env python3
import sys
sys.exit(7)
""",
        encoding="utf-8",
    )
    second = _runner(repo, runner_cls=DurableSyncRunner)
    success, message, cost = second.run()

    assert success is True, message
    assert cost == pytest.approx(0.0)
    assert second._resumed_modules == ["foo"]


def test_total_budget_keeps_durable_runner_single_worker(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(
        repo,
        sync_options={"total_budget": 5.0},
        durable_max_parallel=8,
    )

    assert runner.max_workers == 1


def test_durable_baseline_paths_use_git_root_not_caller_cwd(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    """Issue #1013 iter-18 M-1 + iter-22 M-1: ``DurableSyncRunner`` MUST NOT
    inherit baseline-changed-paths from the caller's cwd. Iter-18 first
    pinned the snapshot to the durable ``git_root`` (so caller-cwd dirty
    files would not leak); iter-22 then made the durable baseline EMPTY by
    construction (per-module worktrees are freshly-created and have no
    pre-existing user WIP), so this assertion is now vacuously true but is
    kept as an explicit guard against regressions.
    """
    caller_cwd = tmp_path / "caller_cwd"
    caller_cwd.mkdir()
    # Dirty file under the caller's cwd; must NOT leak into baseline.
    (caller_cwd / "out.py").write_text("dirty file in caller's cwd")

    durable_root = _init_repo_with_remote(tmp_path)
    monkeypatch.chdir(caller_cwd)

    runner = _runner(
        durable_root,
        runner_cls=EmptyDurableRunner,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    assert runner.project_root == durable_root.resolve()
    # Iter-22 M-1 invariant: durable baseline is always empty.
    # Iter-24 M-1: empty dict (was empty set before the type swap).
    assert "out.py" not in runner._baseline_changed_paths
    assert runner._baseline_changed_paths == {}


def test_durable_baseline_is_empty_even_when_git_root_has_dirty_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    """Issue #1013 iter-22 M-1 (durable baseline-leakage bug): in production
    ``git_root`` IS the user's main checkout where dirty WIP lives, but the
    per-module sync runs in a SEPARATE ``.pdd/worktrees/sync-issue-N-mod/``
    worktree. If the durable runner inherits the main-checkout baseline,
    ``_enforce_scope_guard`` resolves each baseline ``rel_posix`` against the
    per-module worktree root and silently auto-allows any same-named file
    written there by sync, bypassing the split contract.

    Iter-18 fixed the iter-17 regression where the snapshot was taken from
    ``Path.cwd()`` BEFORE the durable runner reassigned ``project_root``;
    iter-22 closes the residual leak by making the durable baseline empty
    by construction. Per-module worktrees are freshly created via
    ``git worktree add`` and have no pre-existing user WIP — so the
    iter-6 B1 "preserve pre-existing untracked files" carve-out (which
    exists for the in-place async case) has no analog here.
    """
    durable_root = _init_repo_with_remote(tmp_path)

    # Dirty (untracked) file inside the durable repo root. In production this
    # stands in for the user's WIP in their main checkout.
    (durable_root / "dirty.py").write_text("user work-in-progress")
    # Also stage a tracked modification so both flavours of "dirty" are
    # represented in what ``git status`` would otherwise report.
    (durable_root / "README.md").write_text("locally modified\n")

    monkeypatch.chdir(durable_root)
    runner = _runner(
        durable_root,
        runner_cls=EmptyDurableRunner,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    # Iter-22 M-1: durable baseline is empty regardless of the git_root's
    # state. The dirty paths from the main checkout must NOT bleed into the
    # per-module worktree's allow set.
    # Iter-24 M-1: empty dict (was empty set before the type swap).
    assert runner.project_root == durable_root.resolve()
    assert runner._baseline_changed_paths == {}
    assert runner._baseline_ignored_paths == {}


def test_durable_baseline_remains_empty_dict_after_init(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    """Issue #1013 iter-24 M-1: baseline snapshots changed from ``Set[str]``
    to ``Dict[str, Optional[str]]`` (path → SHA-1) for content-aware
    preservation. The durable runner's iter-22 "clear baseline" invariant
    still holds — but the cleared value is now an empty dict, not an empty
    set. Iterating a dict with no entries yields nothing, so all the
    ``.items()`` loops in ``_enforce_scope_guard`` and
    ``_remaining_out_of_scope_paths`` remain safe no-ops in durable mode.
    """
    durable_root = _init_repo_with_remote(tmp_path)
    # Dirty paths in the git_root that would have populated the baseline
    # under the inherited AsyncSyncRunner init path.
    (durable_root / "dirty.py").write_text("user wip")
    (durable_root / "build.log").write_text("ignored junk")

    monkeypatch.chdir(durable_root)
    runner = _runner(
        durable_root,
        runner_cls=EmptyDurableRunner,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    assert runner._baseline_changed_paths == {}
    assert runner._baseline_ignored_paths == {}
    # Iter-24 invariant: the cleared baseline is a Mapping (so .items() is
    # safe). Iteration yields no entries — confirms downstream loops are
    # no-ops.
    assert list(runner._baseline_changed_paths.items()) == []
    assert list(runner._baseline_ignored_paths.items()) == []


def test_durable_scope_guard_does_not_whitelist_main_checkout_dirty_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    """Iter-22 M-1 reviewer repro: a dirty ``out.py`` in the main checkout
    must NOT silently whitelist an ``out.py`` written by sync in a separate
    per-module worktree. Before iter-22, the durable runner snapshotted the
    main checkout's ``out.py`` into ``_baseline_changed_paths``; the scope
    guard then resolved that path against the per-module worktree root and
    added it to ``allowed_files``, so the contract-violating worktree
    ``out.py`` slid through.
    """
    from pdd import agentic_sync_runner as mod

    # Main checkout (becomes the durable runner's ``git_root``) with a dirty
    # ``out.py`` standing in for the user's WIP.
    main_checkout = _init_repo_with_remote(tmp_path)
    (main_checkout / "out.py").write_text("user WIP in main checkout")

    # Separate worktree directory, where sync actually runs. Initialize it
    # as its own git repo so ``_resolve_repo_root`` and ``git status``
    # operate locally there.
    worktree_path = tmp_path / "sync-worktree"
    worktree_path.mkdir()
    _git(worktree_path, "init", "-b", "main", ".")
    _git(worktree_path, "config", "user.name", "Test User")
    _git(worktree_path, "config", "user.email", "test@example.invalid")
    (worktree_path / ".gitignore").write_text(".pdd/\n", encoding="utf-8")
    _git(worktree_path, "add", ".gitignore")
    _git(worktree_path, "commit", "-m", "initial")

    # Sync wrote ``out.py`` inside the worktree — this is the contract
    # violation that must be detected.
    (worktree_path / "out.py").write_text("written by sync, NOT in contract")

    monkeypatch.chdir(main_checkout)
    runner = _runner(
        main_checkout,
        runner_cls=EmptyDurableRunner,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    # Mock the revert helpers to return [] so the diagnostic depends purely
    # on the re-scan + baseline interaction, not the helpers' behaviour.
    monkeypatch.setattr(
        mod, "_revert_out_of_scope_changes", lambda _root, _allowed: []
    )
    monkeypatch.setattr(
        mod,
        "revert_out_of_scope_changes_with_dirs",
        lambda _root, allowed_dirs, allowed_files: [],
    )

    # Pretend ``module_cwd`` resolves to the separate worktree.
    monkeypatch.setattr(
        runner, "_resolve_repo_root", lambda _cwd: worktree_path.resolve()
    )

    diagnostic = runner._enforce_scope_guard("mod", worktree_path)

    # Without the iter-22 fix the diagnostic would be ``None`` because
    # ``out.py`` from the (leaked) baseline resolves to
    # ``<worktree_path>/out.py`` and lands in ``allowed_files``. With the
    # fix the baseline is empty, so ``out.py`` is correctly out of scope.
    assert diagnostic is not None
    assert "out.py" in diagnostic


def test_durable_runner_aborts_before_worktree_setup_when_baseline_failed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    """Iter-40 M-2 (durable init ordering): when the inherited
    ``AsyncSyncRunner.__init__`` records ``_baseline_acquisition_failed=True``
    (the iter-38 fail-closed signal), the durable runner's
    :meth:`~DurableSyncRunner.run` MUST abort BEFORE
    :meth:`_prepare_durable_branch` runs. The iter-38 fix was added in
    ``AsyncSyncRunner.run()``, but ``DurableSyncRunner.run()`` calls
    ``_prepare_durable_branch()`` first — without this iter-40 hoist a
    transient git scan failure would leave durable side effects
    (worktree creation, branch checkout, remote pushes) in place before
    the inherited fail-closed check ran."""
    from pdd import agentic_sync_runner as mod

    durable_root = _init_repo_with_remote(tmp_path)

    # Patch the baseline scan to fail. ``DurableSyncRunner.__init__``
    # forwards to ``AsyncSyncRunner.__init__`` which reads the scan and
    # records ``_baseline_acquisition_failed`` on ``None``.
    monkeypatch.setattr(mod, "_git_changed_paths", lambda _root: None)
    monkeypatch.setattr(mod, "_git_ignored_paths", lambda _root: set())

    monkeypatch.chdir(durable_root)

    runner = _runner(
        durable_root,
        runner_cls=EmptyDurableRunner,
        allowed_write_set=["pdd/foo.py"],
        companion_allowlist=[".pdd/meta/*.json"],
    )

    # The inherited init must have flagged the baseline acquisition as
    # failed. (Iter-22 clears the baseline *paths* to {} but does NOT
    # clear this flag — exactly so the iter-40 hoist can see it.)
    assert runner._baseline_acquisition_failed is True, (
        "iter-40: inherited fail-closed flag must reach the durable runner"
    )

    prepare_calls: list[bool] = []

    def fake_prepare() -> tuple[bool, str]:
        prepare_calls.append(True)
        return True, ""

    monkeypatch.setattr(runner, "_prepare_durable_branch", fake_prepare)

    success, message, cost = runner.run()

    assert success is False, (
        "iter-40: durable runner must fail-closed when baseline scan failed"
    )
    assert prepare_calls == [], (
        "iter-40: _prepare_durable_branch MUST NOT run when baseline "
        "acquisition failed — otherwise worktree creation and branch "
        f"checkout happen before the abort. Calls: {prepare_calls}"
    )
    assert "fail-closed" in message, (
        f"iter-40: abort message must mention fail-closed; got: {message!r}"
    )
    assert "baseline" in message, (
        f"iter-40: abort message must mention baseline; got: {message!r}"
    )
    # The abort path returns ``self.initial_cost`` (0.0 for the default
    # runner) — mirrors the inherited AsyncSyncRunner.run abort.
    assert cost == 0.0
