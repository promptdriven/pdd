from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_sync_runner import AsyncSyncRunner
from pdd.durable_sync_runner import (
    DurableSyncRunner,
    _parse_checkpoint_trailer,
    _pdd_path_index,
    _slugify_basename,
)
from pdd.resolved_sync_unit import resolve_sync_unit
from pdd.sync_plan import (
    PlanProvenance,
    SyncPlanCandidate,
    SyncPlanDetails,
    build_sync_plan,
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
        target = self._module_target(basename).rsplit("/", 1)[-1]
        (cwd / f"{target}.py").write_text("updated\n", encoding="utf-8")
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


class OutOfScopeDurableRunner(DurableSyncRunner):
    def _run_child_sync(self, basename: str):
        (self.module_cwds[basename] / "outside-contract.txt").write_text(
            "must not checkpoint\n", encoding="utf-8"
        )
        return True, 0.0, ""


class MultiModuleDurableRunner(DurableSyncRunner):
    def _run_child_sync(self, basename: str):
        cwd = self.module_cwds[basename]
        target = self._module_target(basename).rsplit("/", 1)[-1]
        (cwd / f"{target}.py").write_text(f"synced {basename}\n", encoding="utf-8")
        return True, 0.0, ""


class FailCDurableRunner(MultiModuleDurableRunner):
    def _run_child_sync(self, basename: str):
        if basename == "c":
            return False, 0.0, "simulated c failure"
        return super()._run_child_sync(basename)


def _runner(repo: Path, runner_cls=EmptyDurableRunner, **kwargs) -> DurableSyncRunner:
    sync_options = kwargs.pop("sync_options", {})
    basenames = kwargs.pop("basenames", ["foo"])
    execution_order = kwargs.pop("execution_order", None)
    dep_graph = kwargs.pop(
        "dep_graph",
        {basename: [] for basename in basenames},
    )
    issue_number = kwargs.pop("issue_number", 1328)
    checkout_identity = kwargs.pop(
        "checkout_identity", _git(repo, "rev-parse", "HEAD").stdout.strip()
    )
    supplied_cwds = kwargs.get("module_cwds", {})
    if not sync_options:
        candidates = []
        for basename in basenames:
            target = basename.rsplit("/", 1)[-1]
            cwd = Path(supplied_cwds.get(
                basename, repo / Path(*basename.split("/")[:-1])
            ))
            cwd.mkdir(parents=True, exist_ok=True)
            candidates.append(
                SyncPlanCandidate(
                    module_id=basename,
                    unit=resolve_sync_unit(basename, target, cwd),
                    output_paths=(cwd / f"{target}.py",),
                    details=SyncPlanDetails(
                        changed_reason="durable test scope",
                        expected_operation="generate",
                        confidence="high",
                        provenance=(PlanProvenance("test", basename),),
                    ),
                    dependencies=tuple(dep_graph.get(basename, [])),
                )
            )
        plan = build_sync_plan(
            repo, candidates, basenames, execution_order=execution_order
        )
        sync_options = {
            "sync_plan": plan.to_dict(),
            "sync_plan_digest": plan.sync_plan_digest,
            "selection_digest": plan.selection_digest,
            "execution_selected_module_ids": list(plan.selected_module_ids),
            "execution_dependency_order": list(plan.execution_order),
        }
    return runner_cls(
        basenames=basenames,
        dep_graph=dep_graph,
        sync_options=sync_options,
        github_info=None,
        issue_number=issue_number,
        project_root=repo,
        quiet=True,
        issue_url=f"https://github.com/org/repo/issues/{issue_number}",
        checkout_identity=checkout_identity,
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
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=foo" in log
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


def test_durable_runner_and_resume_binding_use_frozen_execution_order(tmp_path: Path):
    """Durable scheduling must not replace an authoritative b,a prefix."""
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, basenames=["a", "b"], execution_order=["b", "a"])

    assert runner.basenames == ["b", "a"]
    assert runner._resume_binding["ordered_module_ids"] == ["b", "a"]


def test_durable_runner_rejects_checkout_change_after_plan_freeze(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo)
    supplied_identity = runner._resume_binding["checkout_identity"]
    (repo / "README.md").write_text("changed\n", encoding="utf-8")
    _git(repo, "add", "README.md")
    _git(repo, "commit", "-m", "advance checkout")

    success, message, _ = runner.run()

    assert success is False
    assert "checkout identity changed" in message
    assert runner._resume_binding["checkout_identity"] == supplied_identity
    assert runner._durable_resume_binding is None


def test_durable_runner_rejects_unavailable_checkout_identity(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)

    success, message, _ = _runner(repo, checkout_identity=None).run()

    assert success is False
    assert "requires an exact supplied checkout identity" in message


def test_durable_runner_does_not_resume_a_changed_v1_selection(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    first = _runner(repo, basenames=["foo"])
    success, message, _ = first.run()
    assert success is True, message

    changed = _runner(repo, basenames=["foo", "bar"])
    success, message, _ = changed.run()

    assert success is True, message
    assert changed._resumed_modules == []


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
    assert "PDD-Sync-Checkpoint-V2: issue=999 module=foo" in log
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=foo" in log


def test_module_metadata_is_force_added_even_when_pdd_dir_is_ignored(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, runner_cls=MetadataDurableRunner)

    success, message, _ = runner.run()

    assert success is True, message
    metadata = _git(repo, "show", "sync/issue-1328:.pdd/meta/foo_python.json").stdout
    assert json.loads(metadata) == {"module": "foo"}
    output = _git(repo, "show", "sync/issue-1328:foo.py").stdout
    assert output == "updated\n"


def test_durable_runner_rejects_child_output_outside_frozen_plan(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    runner = _runner(repo, runner_cls=OutOfScopeDurableRunner)

    success, message, _ = runner.run()

    assert success is False
    assert "out-of-scope path(s): outside-contract.txt" in message
    log = _git(repo, "log", "sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=foo" not in log


def test_nested_module_metadata_is_force_added_for_module_cwd(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    module_dir = repo / "packages" / "app"
    module_dir.mkdir(parents=True)
    (module_dir / "foo.py").write_text("initial\n", encoding="utf-8")
    _git(repo, "add", "packages/app/foo.py")
    _git(repo, "commit", "-m", "add nested module")
    _git(repo, "push", "origin", "main")

    runner = _runner(
        repo,
        runner_cls=MetadataDurableRunner,
        basenames=["packages/app/foo"],
        module_cwds={"packages/app/foo": module_dir},
    )

    success, message, _ = runner.run()

    assert success is True, message
    metadata = _git(
        repo,
        "show",
        "sync/issue-1328:packages/app/.pdd/meta/foo_python.json",
    ).stdout
    assert json.loads(metadata) == {"module": "packages/app/foo"}
    output = _git(repo, "show", "sync/issue-1328:packages/app/foo.py").stdout
    assert output == "updated\n"


def test_metadata_allowlist_rejects_nested_pdd_state_and_wrong_meta_scope(tmp_path: Path):
    repo = _init_repo_with_remote(tmp_path)
    module_dir = repo / "packages" / "app"
    basename = "packages/app/foo"
    runner = _runner(
        repo,
        basenames=[basename],
        module_cwds={basename: module_dir},
    )

    assert runner._unsafe_staged_paths(
        basename,
        [
            ".pdd/meta/foo_python.json",
            "packages/app/.pdd/meta/foo_typescript.json",
        ],
    ) == []
    assert runner._unsafe_staged_paths(
        basename,
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
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=foo" in local_log

    second = _runner(repo)
    success, message, _ = second.run()

    assert success is True, message
    assert second._resumed_modules == ["foo"]
    _git(repo, "fetch", "origin", "sync/issue-1328")
    remote_log = _git(repo, "log", "origin/sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=foo" in remote_log


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
    (second_worktree / "foo.py").write_text("second local change\n", encoding="utf-8")
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
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=a" in first_remote_log
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=b" in first_remote_log
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=c" not in first_remote_log

    fresh = tmp_path / "fresh-worker"
    _git(tmp_path, "clone", str(tmp_path / "origin.git"), str(fresh))
    _git(fresh, "config", "user.name", "Fresh Worker")
    _git(fresh, "config", "user.email", "fresh@example.invalid")
    _git(fresh, "symbolic-ref", "refs/remotes/origin/HEAD", "refs/remotes/origin/main")
    _git(fresh, "checkout", "main")

    second = _runner(
        fresh,
        runner_cls=MultiModuleDurableRunner,
        basenames=basenames,
        durable_max_parallel=max_parallel,
    )
    success, message, _ = second.run()

    assert success is True, message
    # The fresh worker has the same immutable V1 plan, selection, schedule,
    # and checkout identity, so only the completed modules resume.
    assert second._resumed_modules == ["a", "b"]
    _git(fresh, "fetch", "origin", "sync/issue-1328")
    final_log = _git(fresh, "log", "origin/sync/issue-1328", "--format=%B").stdout
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=c" in final_log
    assert _git(fresh, "show", "origin/sync/issue-1328:c.py").stdout == "synced c\n"


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
    assert "PDD-Sync-Checkpoint-V2: issue=1328 module=foo" not in log


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
Path(f"{basename}.py").write_text(f"synced {basename}\\n", encoding="utf-8")
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
    assert _git(repo, "show", "sync/issue-1328:foo.py").stdout == "synced foo\n"
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


# ---------------------------------------------------------------------------
# Issue #1565 — DurableSyncRunner sibling: PDD_SYNC_MAX_WORKERS env var
# ---------------------------------------------------------------------------

# Scope addition: covers expansion item "pdd/durable_sync_runner.py:82 —
# DurableSyncRunner.__init__ else-branch also falls back to MAX_WORKERS without
# checking PDD_SYNC_MAX_WORKERS" identified by Step 6 but absent from Step 8's
# primary test plan.
def test_durable_runner_fallback_max_workers_reads_pdd_sync_max_workers_env_var():
    """PDD_SYNC_MAX_WORKERS must also limit DurableSyncRunner.max_workers when
    durable_max_parallel is not set (the else-branch at durable_sync_runner.py:82).

    Fails on buggy code: agentic_sync_runner.MAX_WORKERS is always 4, so the
    imported durable_sync_runner.MAX_WORKERS is also always 4 regardless of the
    env var.
    """
    _project_root = str(Path(__file__).resolve().parent.parent)
    _pythonpath = f"{_project_root}:{os.environ.get('PYTHONPATH', '')}"
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import os; os.environ['PDD_SYNC_MAX_WORKERS'] = '2'; "
                "from pdd.durable_sync_runner import MAX_WORKERS; "
                "print(MAX_WORKERS)"
            ),
        ],
        capture_output=True,
        text=True,
        env={**os.environ, "PYTHONPATH": _pythonpath},
    )
    assert result.returncode == 0, (
        f"Import subprocess failed: stderr={result.stderr!r}"
    )
    assert result.stdout.strip() == "2", (
        f"DurableSyncRunner's MAX_WORKERS should be 2 when "
        f"PDD_SYNC_MAX_WORKERS=2; got {result.stdout.strip()!r}. "
        "Bug: durable_sync_runner imports MAX_WORKERS from agentic_sync_runner "
        "which is hardcoded to 4; the env var never reaches the durable runner."
    )


def test_durable_runner_reads_pdd_sync_max_workers_when_constructed(
    tmp_path: Path, monkeypatch
):
    """DurableSyncRunner must see env changes made after module import."""
    repo = _init_repo_with_remote(tmp_path)
    monkeypatch.setenv("PDD_SYNC_MAX_WORKERS", "2")

    runner = _runner(repo)

    assert runner.max_workers == 2


# ---------------------------------------------------------------------------
# Issue #1565 — Real-subprocess (not mocked Popen) worker-cap validation for
# durable mode (Greg review item 4).
#
# DurableSyncRunner._run_child_sync delegates to super()._sync_one_module ->
# AsyncSyncRunner._run_attempt, i.e. the SAME real subprocess.Popen reader the
# agentic runner uses; durable only adds the worktree/checkpoint scheduling on
# top. So the bounded-output and sticky-failure-marker behaviors are inherited
# verbatim and are covered by the real-subprocess tests in
# tests/test_agentic_sync_runner.py. The durable-specific risk is the worker
# cap, validated here with real child processes. The assertion is two-sided
# (peak <= 2 AND peak >= 2) so it cannot pass vacuously on a run that happened
# to serialize.
# ---------------------------------------------------------------------------

# Concurrency-only fake child: drop a presence token, sample peak co-running
# siblings for `hold_s`, record the peak, make no file changes (so the durable
# checkpoint is empty), and exit 0.
_DURABLE_FAKE_CHILD_SOURCE = r'''
import os
import sys
import time
import uuid

presence_dir, result_path = sys.argv[1], sys.argv[2]
hold_s, sample_s = float(sys.argv[3]), float(sys.argv[4])
os.makedirs(presence_dir, exist_ok=True)
token = os.path.join(presence_dir, "%d-%s" % (os.getpid(), uuid.uuid4().hex))
open(token, "w").close()
peak = 0
deadline = time.time() + hold_s
try:
    while time.time() < deadline:
        try:
            peak = max(peak, len(os.listdir(presence_dir)))
        except OSError:
            pass
        time.sleep(sample_s)
finally:
    try:
        os.remove(token)
    except OSError:
        pass
with open(result_path, "w") as handle:
    handle.write(str(peak))
sys.exit(0)
'''


def test_real_subprocess_durable_max_workers_limits_concurrency(
    tmp_path: Path, monkeypatch
):
    """PDD_SYNC_MAX_WORKERS=2 caps concurrent module syncs in DURABLE mode,
    proven with real subprocesses driven through the durable scheduler.

    Four independent modules sync through real ``subprocess.Popen`` children
    (each producing an empty checkpoint); the observed peak concurrency must
    not exceed the cap.
    """
    repo = _init_repo_with_remote(tmp_path)
    child = tmp_path / "durable_fake_child.py"
    child.write_text(_DURABLE_FAKE_CHILD_SOURCE, encoding="utf-8")
    presence = tmp_path / "presence"
    results = tmp_path / "results"
    presence.mkdir()
    results.mkdir()

    monkeypatch.setenv("PDD_SYNC_MAX_WORKERS", "2")
    basenames = ["a", "b", "c", "d"]

    def _fake_build_command(self, basename, in_flight_cost=0.0):
        return [
            sys.executable,
            str(child),
            str(presence),
            str(results / basename),
            "0.6",
            "0.01",
        ]

    runner = _runner(
        repo,
        runner_cls=DurableSyncRunner,
        basenames=basenames,
        dep_graph={b: [] for b in basenames},
        issue_number=1565,
    )
    assert runner.max_workers == 2

    with patch.object(AsyncSyncRunner, "_build_command", _fake_build_command):
        success, message, _cost = runner.run()

    assert success, f"durable real-subprocess run failed: {message!r}"
    peaks = [
        int((results / b).read_text())
        for b in basenames
        if (results / b).exists()
    ]
    assert peaks, "no durable child reported a peak — children never ran"
    observed = max(peaks)
    # Upper bound: the cap holds. Lower bound: the children genuinely run
    # concurrently, so the cap assertion is not vacuously satisfied by a run
    # that happened to serialize. With 4 always-ready modules and 2 workers the
    # durable scheduler must drive the peak to exactly 2 (worktree-create and
    # checkpoint serialize under _checkpoint_lock, but the child sync — where
    # the peak is measured — runs outside it).
    assert observed <= 2, (
        f"PDD_SYNC_MAX_WORKERS=2 did not cap durable concurrency: real children "
        f"observed a peak of {observed} simultaneous syncs (expected <= 2)"
    )
    assert observed >= 2, (
        f"durable children never ran 2-wide (peak {observed}); the <= 2 cap "
        f"assertion would be vacuous — with 4 ready modules and 2 workers the "
        f"peak must reach 2"
    )


def test_durable_runner_builds_remapped_context_and_target(tmp_path):
    """Durable carries target + context identity into `_build_command` (#1675).

    Target and context are cwd-independent, so even though durable repopulates
    module_cwds with a per-module worktree at runtime, the child must still run
    `pdd --context <ctx> sync <target>` — using the resolved target (not the
    scheduler key) and the cwd's own context (not the invalid global one).
    """
    worktree = tmp_path / "wt" / "backend"
    worktree.mkdir(parents=True)
    (worktree / ".pddrc").write_text(
        'version: "1.0"\ncontexts:\n  report_ctx:\n    paths: ["report*"]\n'
        '    defaults:\n      prompts_dir: "prompts"\n',
        encoding="utf-8",
    )
    runner = DurableSyncRunner(
        basenames=["backend/report"],
        dep_graph={"backend/report": []},
        sync_options={"context": "root_ctx"},  # not defined in the nested .pddrc
        github_info=None,
        issue_number=1675,
        project_root=tmp_path,
        quiet=True,
        module_cwds={"backend/report": tmp_path / "backend"},
        module_targets={"backend/report": "report"},
        module_contexts={"backend/report": "report_ctx"},
    )
    # Simulate the per-module worktree cwd that _sync_one_module sets at runtime.
    runner.module_cwds["backend/report"] = worktree

    cmd = runner._build_command("backend/report")
    assert cmd[-1] == "report"  # resolved target, not the "backend/report" key
    assert "--context" in cmd and cmd[cmd.index("--context") + 1] == "report_ctx"
    assert "root_ctx" not in cmd


def test_durable_remaps_unit_into_worktree_for_build_command(tmp_path):
    """Durable carries a ResolvedSyncUnit and rebases it onto the worktree cwd
    so the child runs `pdd --context <ctx> sync <target>` there (#1675)."""
    from pdd.resolved_sync_unit import ResolvedSyncUnit

    parent_cwd = tmp_path / "backend"
    parent_cwd.mkdir()
    unit = ResolvedSyncUnit(
        key="backend/report",
        target_basename="report",
        cwd=parent_cwd,
        pddrc_path=parent_cwd / ".pddrc",
        context="report_ctx",
        prompts_dir=parent_cwd / "prompts",
    )
    runner = DurableSyncRunner(
        basenames=["backend/report"],
        dep_graph={"backend/report": []},
        sync_options={"context": "root_ctx"},
        github_info=None,
        issue_number=1675,
        project_root=tmp_path,
        quiet=True,
        module_units={"backend/report": unit},
    )
    assert runner.parent_module_units["backend/report"].context == "report_ctx"

    # Simulate the per-module worktree remap that _sync_one_module performs
    # (relocate from the repo root onto the worktree root).
    worktree_root = tmp_path / "wt"
    runner.module_units["backend/report"] = runner.parent_module_units[
        "backend/report"
    ].relocate(tmp_path, worktree_root)

    cmd = runner._build_command("backend/report")
    assert cmd[-1] == "report"
    assert "--context" in cmd and cmd[cmd.index("--context") + 1] == "report_ctx"
    assert runner._module_cwd_path("backend/report") == worktree_root / "backend"


def test_durable_allows_ancestor_pddrc_metadata(tmp_path):
    """#1675 (review): operation_log anchors a module's metadata at the nearest
    .pddrc PARENT, which can be an ANCESTOR of the module cwd. A module run from
    backend/functions governed by backend/.pddrc writes backend/.pdd/meta — durable
    mode must treat that as allowed, not reject the correctly-staged file as unsafe."""
    from pdd.resolved_sync_unit import ResolvedSyncUnit

    cwd = tmp_path / "backend" / "functions"
    cwd.mkdir(parents=True)
    governing = tmp_path / "backend"
    unit = ResolvedSyncUnit(
        key="backend/functions/report",
        target_basename="report",
        cwd=cwd,
        pddrc_path=governing / ".pddrc",  # ancestor of cwd
        context=None,
        prompts_dir=cwd / "prompts",
    )
    runner = DurableSyncRunner(
        basenames=["backend/functions/report"],
        dep_graph={"backend/functions/report": []},
        sync_options={},
        github_info=None,
        issue_number=1675,
        project_root=tmp_path,
        quiet=True,
        module_cwds={"backend/functions/report": cwd},
        module_targets={"backend/functions/report": "report"},
        module_units={"backend/functions/report": unit},
    )
    prefixes = {p.as_posix() for p in runner._allowed_metadata_prefixes("backend/functions/report")}
    assert "backend/.pdd/meta" in prefixes, prefixes  # the governing .pddrc parent
    # the correctly-anchored ancestor metadata file is NOT flagged unsafe
    assert runner._unsafe_staged_paths(
        "backend/functions/report", ["backend/.pdd/meta/report_python.json"]
    ) == []
    # but a wrong-name file under that same dir is still rejected
    assert runner._unsafe_staged_paths(
        "backend/functions/report", ["backend/.pdd/meta/other_python.json"]
    ) == ["backend/.pdd/meta/other_python.json"]
