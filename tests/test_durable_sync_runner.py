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
