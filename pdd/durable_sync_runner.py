"""Durable issue-sync runner.

This runner keeps the existing issue-sync scheduling model, but isolates each
module in its own git worktree and checkpoints successful module output to a
durable branch before marking the module complete.
"""
# pylint: disable=duplicate-code,too-many-arguments,too-many-instance-attributes
# pylint: disable=too-few-public-methods
from __future__ import annotations

import base64
import binascii
import os
import re
import shutil
# Durable sync shells out to git with shell=False.
import subprocess  # nosec B404
import threading
import time
import uuid
from hashlib import sha1
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from .agentic_sync_runner import AsyncSyncRunner, _read_sync_max_workers
from .resolved_sync_unit import ResolvedSyncUnit

MAX_WORKERS = _read_sync_max_workers()

CHECKPOINT_TRAILER = "PDD-Sync-Checkpoint-V1"
CHECKPOINT_AUTHOR_NAME = "PDD Durable Sync"
CHECKPOINT_AUTHOR_EMAIL = "pdd-durable-sync@example.invalid"
# Shared (non-module-prefixed) greenfield-ownership manifest under .pdd/meta
# (issue #1903 §B.4 round 10). Kept in lockstep with
# content_selector._PDD_CREATED_TESTS_MANIFEST.
_OWNERSHIP_MANIFEST_NAME = "pdd_created_tests.json"


class DurableSyncRunner(AsyncSyncRunner):
    """Dependency-aware durable sync runner for GitHub issue sync jobs."""

    def __init__(
        self,
        *,
        basenames: List[str],
        dep_graph: Dict[str, List[str]],
        sync_options: Dict[str, object],
        github_info: Optional[Dict[str, object]],
        issue_number: int,
        project_root: Path,
        durable_branch: Optional[str] = None,
        no_resume: bool = False,
        durable_max_parallel: Optional[int] = None,
        quiet: bool = False,
        verbose: bool = False,
        issue_url: Optional[str] = None,
        module_cwds: Optional[Dict[str, Path]] = None,
        module_targets: Optional[Dict[str, str]] = None,
        module_contexts: Optional[Dict[str, Optional[str]]] = None,
        module_units: Optional[Dict[str, ResolvedSyncUnit]] = None,
        initial_cost: float = 0.0,
    ) -> None:
        self.issue_number = issue_number
        self.git_root = project_root.resolve()
        self.selected_branch = durable_branch or f"sync/issue-{issue_number}"
        self.no_resume = no_resume
        self.durable_max_parallel = durable_max_parallel
        self.parent_module_cwds = dict(module_cwds or {})
        # Parent-checkout units; remapped onto each per-module worktree cwd at
        # runtime in _sync_one_module so the child keeps the same target/context
        # identity inside the worktree (#1675).
        self.parent_module_units = dict(module_units or {})
        self.durable_worktree_path = (
            self.git_root / ".pdd" / "worktrees" / f"durable-issue-{issue_number}"
        )
        self._checkpoint_lock = threading.Lock()
        self._checkpoint_halted = threading.Event()
        self._run_id = uuid.uuid4().hex[:8]
        self._prepared = False
        self._protected_base_sha: Optional[str] = None

        super().__init__(
            basenames=basenames,
            dep_graph=dep_graph,
            sync_options=sync_options,
            github_info=github_info,
            quiet=quiet,
            verbose=verbose,
            issue_url=issue_url,
            module_cwds={},
            # Carry target + context identity through to the base runner so a
            # child still runs `pdd --context <ctx> sync <target>` after its cwd
            # is remapped into a per-module worktree at runtime. Both are
            # cwd-independent (the worktree checks out the same .pddrc), so they
            # pass through unchanged even though module_cwds is repopulated per
            # module during the run (#1675).
            module_targets=dict(module_targets or {}),
            module_contexts=dict(module_contexts or {}),
            module_units={},
            initial_cost=initial_cost,
        )
        self.project_root = self.git_root
        if self.total_budget is not None:
            self.max_workers = 1
        elif durable_max_parallel is not None:
            self.max_workers = max(1, int(durable_max_parallel))
        else:
            self.max_workers = _read_sync_max_workers()

    def _load_state(self) -> None:
        """Durable mode resumes from git trailers, not local JSON state."""

    def _save_state(self) -> None:
        """Durable mode must not persist or read local runner state."""

    def _delete_state(self) -> None:
        """Durable mode leaves local runner state untouched."""

    def run(self) -> Tuple[bool, str, float]:
        ok, message = self._prepare_durable_branch()
        if not ok:
            return False, message, self.initial_cost
        return super().run()

    def _prepare_durable_branch(self) -> Tuple[bool, str]:
        if self._prepared:
            return True, ""

        valid_ok, valid_msg = self._validate_repository_for_durable_sync()
        if not valid_ok:
            return False, valid_msg

        cleanup_ok, cleanup_msg = self._cleanup_orphan_module_worktrees()
        if not cleanup_ok:
            return False, cleanup_msg

        setup_ok, setup_msg = self._setup_durable_worktree()
        if not setup_ok:
            return False, setup_msg

        protected_ok, protected_msg = self._resolve_protected_base()
        if not protected_ok:
            return False, protected_msg

        push_ok, push_msg = self._push_unpushed_local_checkpoints()
        if not push_ok:
            return False, push_msg

        if not self.no_resume:
            completed = self._read_checkpointed_modules()
            for basename in self.basenames:
                if basename in completed:
                    self.module_states[basename].status = "success"
                    # Restore the adopted-test "needs review" note (round 8) so a
                    # resumed run still surfaces it in the PR comment and summary.
                    review = completed[basename]
                    if review:
                        self.module_states[basename].needs_review = review
                    self._resumed_modules.append(basename)

        self._prepared = True
        return True, ""

    def _resolve_protected_base(self) -> Tuple[bool, str]:
        """Pin immutable ownership evidence before any module child runs."""
        remote_head = self._git(
            ["symbolic-ref", "--quiet", "refs/remotes/origin/HEAD"],
            cwd=self.git_root,
        )
        protected_ref = remote_head.stdout.strip() if remote_head.returncode == 0 else "origin/main"
        exists = self._git(["rev-parse", "--verify", protected_ref], cwd=self.git_root)
        if exists.returncode != 0:
            return False, "Durable sync cannot resolve the protected origin default branch"
        base = self._git(
            ["merge-base", "HEAD", protected_ref],
            cwd=self.durable_worktree_path,
        )
        if base.returncode != 0 or not base.stdout.strip():
            return False, "Durable sync cannot establish a protected ownership base"
        self._protected_base_sha = base.stdout.strip()
        return True, ""

    def _build_env(
        self, cost_file_path: str, repair_directive: Optional[str] = None
    ) -> Dict[str, str]:
        """Propagate the pinned base used for monotonic test ownership."""
        env = super()._build_env(cost_file_path, repair_directive)
        if not self._protected_base_sha:
            raise RuntimeError("durable sync protected ownership base is unavailable")
        env["PDD_PROTECTED_BASE_REF"] = self._protected_base_sha
        return env

    def _validate_repository_for_durable_sync(self) -> Tuple[bool, str]:
        root = self._git(["rev-parse", "--show-toplevel"], cwd=self.git_root)
        if root.returncode != 0:
            return False, "Durable sync requires a git repository"
        self.git_root = Path(root.stdout.strip()).resolve()
        self.project_root = self.git_root

        if self._git(["remote", "get-url", "origin"], cwd=self.git_root).returncode != 0:
            return False, "Durable sync requires an origin remote for checkpoint pushes"

        if self._is_forbidden_branch(self.selected_branch):
            return (
                False,
                f"Durable sync refuses to operate on protected branch "
                f"{self.selected_branch!r}",
            )

        return True, ""

    def _sync_one_module(self, basename: str) -> Tuple[bool, float, str]:
        worktree_path: Optional[Path] = None
        try:
            worktree_path = self._create_module_worktree(basename)
            module_cwd = self._module_cwd_for_worktree(basename, worktree_path)
            self.module_cwds[basename] = module_cwd
            # Rebase the canonical unit onto the worktree cwd so the child keeps
            # the same target/context identity inside the worktree (#1675).
            parent_unit = self.parent_module_units.get(basename)
            if parent_unit is not None:
                # Relocate relative to the repo root (the worktree mirrors it) so
                # paths that are ancestors of cwd — e.g. a .pddrc one level up —
                # rebase into the worktree too (#1675).
                self.module_units[basename] = parent_unit.relocate(
                    self.git_root, worktree_path
                )

            success, cost, error = self._run_child_sync(basename)
            if not success:
                return False, cost, error

            if self._checkpoint_halted.is_set():
                return False, cost, "Checkpointing halted after an earlier checkpoint failure"

            ok, checkpoint_msg = self._checkpoint_module(basename, worktree_path)
            if not ok:
                return False, cost, checkpoint_msg

            self._remove_worktree(worktree_path)
            return True, cost, ""
        except (RuntimeError, subprocess.SubprocessError, OSError) as exc:
            return False, 0.0, str(exc)
        finally:
            if basename in self.module_cwds:
                del self.module_cwds[basename]
            if basename in self.module_units:
                del self.module_units[basename]

    def _run_child_sync(self, basename: str) -> Tuple[bool, float, str]:
        return super()._sync_one_module(basename)

    def _checkpoint_module(self, basename: str, module_worktree: Path) -> Tuple[bool, str]:
        with self._checkpoint_lock:
            if self._checkpoint_halted.is_set():
                return False, "Checkpointing halted after an earlier checkpoint failure"

            ok, msg, empty = self._create_checkpoint_commit(basename, module_worktree)
            if not ok:
                self._checkpoint_halted.set()
                return False, msg

            pushed, push_msg, commit_sha = self._push_checkpoint()
            if not pushed:
                self._checkpoint_halted.set()
                return False, push_msg

            print(
                f"PDD_CHECKPOINT: issue={self.issue_number} module={basename} "
                f"commit={commit_sha} empty={str(empty).lower()}",
                flush=True,
            )
            return True, ""

    def _create_checkpoint_commit(
        self, basename: str, module_worktree: Path
    ) -> Tuple[bool, str, bool]:
        clean_ok, clean_msg = self._ensure_clean_durable_worktree()
        if not clean_ok:
            return False, clean_msg, False

        stage_ok, stage_msg, empty = self._stage_module_changes(basename, module_worktree)
        if not stage_ok:
            return False, stage_msg, empty

        if empty:
            ok, msg = self._commit_empty_checkpoint(basename)
        else:
            ok, msg = self._apply_module_patch_to_durable_branch(basename, module_worktree)
        return ok, msg, empty

    def _create_module_worktree(self, basename: str) -> Path:
        slug = _slugify_basename(basename)
        worktree_path = (
            self.git_root
            / ".pdd"
            / "worktrees"
            / f"sync-issue-{self.issue_number}-{slug}-{self._run_id}"
        )
        self._remove_orphan_dir(worktree_path)

        with self._checkpoint_lock:
            head = self._git(["rev-parse", "HEAD"], cwd=self.durable_worktree_path)
            if head.returncode != 0:
                raise RuntimeError(
                    f"Could not resolve durable branch HEAD: {head.stderr.strip()}"
                )
            base_sha = head.stdout.strip()
            result = self._git(
                ["worktree", "add", "--detach", str(worktree_path), base_sha],
                cwd=self.git_root,
                timeout=120,
            )
            if result.returncode != 0:
                raise RuntimeError(
                    f"Failed to create module worktree for {basename}: "
                    f"{_combined_output(result)}"
                )

        return worktree_path

    def _module_cwd_for_worktree(self, basename: str, module_worktree: Path) -> Path:
        parent_cwd = self.parent_module_cwds.get(basename, self.git_root)
        try:
            rel = parent_cwd.resolve().relative_to(self.git_root)
        except ValueError:
            rel = Path(".")
        return module_worktree / rel

    def _setup_durable_worktree(self) -> Tuple[bool, str]:
        available_ok, available_msg = self._check_durable_worktree_available()
        if not available_ok:
            return False, available_msg

        branch_paths = self._worktree_paths_for_branch(self.selected_branch)
        durable_resolved = self.durable_worktree_path.resolve()
        if branch_paths and branch_paths[0].resolve() == durable_resolved:
            return self._fast_forward_durable_worktree()

        return self._add_durable_worktree()

    def _check_durable_worktree_available(self) -> Tuple[bool, str]:
        branch_paths = self._worktree_paths_for_branch(self.selected_branch)
        durable_resolved = self.durable_worktree_path.resolve()
        for path in branch_paths:
            if path.resolve() != durable_resolved:
                return (
                    False,
                    f"Durable branch {self.selected_branch!r} is already checked "
                    f"out at {path}",
                )

        if branch_paths and branch_paths[0].resolve() == durable_resolved:
            return True, ""

        if durable_resolved in {path.resolve() for path in self._registered_worktree_paths()}:
            return (
                False,
                f"Durable worktree path {self.durable_worktree_path} is already "
                "registered for another branch or detached HEAD",
            )
        return True, ""

    def _add_durable_worktree(self) -> Tuple[bool, str]:
        self.durable_worktree_path.parent.mkdir(parents=True, exist_ok=True)
        self._remove_orphan_dir(self.durable_worktree_path)

        fetch_ok, remote_branch_found, fetch_msg = self._fetch_remote_branch(
            self.selected_branch
        )
        if not fetch_ok:
            return False, fetch_msg
        local_exists = self._local_branch_exists(self.selected_branch)
        remote_ref = f"refs/remotes/origin/{self.selected_branch}"
        remote_exists = remote_branch_found and self._ref_exists(remote_ref)

        if not local_exists and remote_exists:
            create = self._git(
                ["branch", self.selected_branch, f"origin/{self.selected_branch}"],
                cwd=self.git_root,
            )
            if create.returncode != 0:
                return False, f"Failed to create local durable branch: {_combined_output(create)}"
            local_exists = True

        if local_exists:
            cmd = ["worktree", "add", str(self.durable_worktree_path), self.selected_branch]
        else:
            cmd = [
                "worktree",
                "add",
                "-b",
                self.selected_branch,
                str(self.durable_worktree_path),
                "HEAD",
            ]

        result = self._git(cmd, cwd=self.git_root, timeout=120)
        if result.returncode != 0:
            return False, f"Failed to create durable branch worktree: {_combined_output(result)}"

        return self._fast_forward_durable_worktree()

    def _fast_forward_durable_worktree(self) -> Tuple[bool, str]:
        fetch_ok, remote_branch_found, fetch_msg = self._fetch_remote_branch(
            self.selected_branch
        )
        if not fetch_ok:
            return False, fetch_msg
        if remote_branch_found and self._ref_exists(f"refs/remotes/origin/{self.selected_branch}"):
            merge = self._git(
                ["merge", "--ff-only", f"origin/{self.selected_branch}"],
                cwd=self.durable_worktree_path,
            )
            if merge.returncode != 0:
                return False, f"Failed to fast-forward durable branch: {_combined_output(merge)}"
        return True, ""

    def _stage_module_changes(
        self, basename: str, module_worktree: Path
    ) -> Tuple[bool, str, bool]:
        reset = self._git(["reset"], cwd=module_worktree)
        if reset.returncode != 0:
            return False, f"Failed to reset module index: {_combined_output(reset)}", False

        add = self._git(["add", "-A"], cwd=module_worktree)
        if add.returncode != 0:
            return False, f"Failed to stage module changes: {_combined_output(add)}", False

        self._force_add_module_metadata(basename, module_worktree)

        names = self._git(
            ["diff", "--cached", "--name-only", "--diff-filter=ACMRTD"],
            cwd=module_worktree,
        )
        if names.returncode != 0:
            return False, f"Failed to inspect staged changes: {_combined_output(names)}", False

        changed_paths = [line.strip() for line in names.stdout.splitlines() if line.strip()]
        unsafe = self._unsafe_staged_paths(basename, changed_paths)
        if unsafe:
            return (
                False,
                "Durable sync refuses to checkpoint unsafe path(s): "
                + ", ".join(unsafe),
                False,
            )

        empty = not changed_paths
        return True, "", empty

    def _metadata_basename(self, basename: str) -> str:
        """Filesystem-safe stem for this module's ``.pdd/meta`` files.

        The child writes metadata named after the *target* basename it synced
        (e.g. ``pdd sync report`` -> ``report_*.json``), which can differ from
        the scheduler key (e.g. ``backend/report``). Use the resolved target so
        checkpoint staging/validation matches the files the child actually wrote
        (#1675).
        """
        return self._module_target(basename).replace("/", "_")

    def _force_add_module_metadata(self, basename: str, module_worktree: Path) -> None:
        safe = self._metadata_basename(basename)
        meta_dirs = [
            module_worktree / prefix
            for prefix in self._allowed_metadata_prefixes(basename)
        ]

        paths = []
        for meta_dir in meta_dirs:
            if meta_dir.exists():
                paths.extend(sorted(meta_dir.glob(f"{safe}_*.json")))
                # Issue #1903 §B.4 (round 10): the SHARED greenfield-ownership
                # manifest lives in .pdd/meta and is tracked, but it is NOT
                # module-prefixed — force-add it too so a PDD-created co-located
                # test's ownership travels on the durable branch and survives a
                # fresh-worktree resume (else it is misread as human-adopted).
                manifest = meta_dir / _OWNERSHIP_MANIFEST_NAME
                if manifest.is_file():
                    paths.append(manifest)
        if not paths:
            return
        rel_paths = [str(path.relative_to(module_worktree)) for path in paths]
        self._git(["add", "-f", "--", *rel_paths], cwd=module_worktree)

    def _unsafe_staged_paths(self, basename: str, paths: List[str]) -> List[str]:
        safe = self._metadata_basename(basename)
        allowed_meta_prefixes = {
            prefix.as_posix().rstrip("/") + "/"
            for prefix in self._allowed_metadata_prefixes(basename)
        }
        unsafe: List[str] = []
        for path in paths:
            normalized = path.replace(os.sep, "/")
            lower = normalized.lower()
            pdd_index = _pdd_path_index(normalized)
            if pdd_index is not None:
                matching_meta_prefix = next(
                    (
                        prefix
                        for prefix in allowed_meta_prefixes
                        if normalized.startswith(prefix)
                    ),
                    None,
                )
                if matching_meta_prefix:
                    meta_name = Path(normalized).name
                    # The shared ownership manifest is a legitimate tracked
                    # non-module-prefixed .pdd/meta file (round 10) — allow it.
                    if meta_name == _OWNERSHIP_MANIFEST_NAME:
                        pass
                    elif not meta_name.startswith(f"{safe}_") or not meta_name.endswith(".json"):
                        unsafe.append(path)
                else:
                    unsafe.append(path)
            if lower.endswith("crash.log") or lower.endswith("fix_errors.log"):
                unsafe.append(path)
            if lower.endswith(".pem") or lower.endswith(".key"):
                unsafe.append(path)
            if Path(lower).name in {".env", ".env.local", "cost.csv"}:
                unsafe.append(path)
            if "token" in lower or "secret" in lower:
                unsafe.append(path)
        return sorted(set(unsafe))

    def _allowed_metadata_prefixes(self, basename: str) -> List[Path]:
        prefixes = [Path(".pdd") / "meta"]

        def _add(root: Optional[Path]) -> None:
            if root is None:
                return
            try:
                rel = root.resolve().relative_to(self.git_root)
            except ValueError:
                return
            if rel != Path("."):
                prefixes.append(rel / ".pdd" / "meta")

        # The module cwd's own .pdd/meta.
        _add(self.parent_module_cwds.get(basename))
        # #1675: operation_log anchors a module's metadata at the nearest .pddrc
        # PARENT, which may be an ANCESTOR of the module cwd (e.g. cwd
        # backend/functions governed by backend/.pddrc writes backend/.pdd/meta).
        # Allow that governing project root too, or correctly-staged ancestor
        # metadata is wrongly rejected as unsafe / never force-added.
        unit = self.parent_module_units.get(basename)
        if unit is not None and unit.pddrc_path is not None:
            _add(unit.pddrc_path.parent)

        deduped: List[Path] = []
        for prefix in prefixes:
            if prefix not in deduped:
                deduped.append(prefix)
        return deduped

    def _apply_module_patch_to_durable_branch(
        self, basename: str, module_worktree: Path
    ) -> Tuple[bool, str]:
        commit = self._git(
            [
                "-c",
                f"user.name={CHECKPOINT_AUTHOR_NAME}",
                "-c",
                f"user.email={CHECKPOINT_AUTHOR_EMAIL}",
                "commit",
                "-m",
                f"pdd durable module diff for {basename}",
            ],
            cwd=module_worktree,
        )
        if commit.returncode != 0:
            return False, f"Failed to create module patch commit: {_combined_output(commit)}"

        patch = self._git(
            ["format-patch", "-1", "--stdout", "--binary", "HEAD"],
            cwd=module_worktree,
        )
        if patch.returncode != 0:
            return False, f"Failed to export module patch: {_combined_output(patch)}"

        apply = self._git(
            ["am", "--3way"],
            cwd=self.durable_worktree_path,
            input_text=patch.stdout,
            timeout=120,
        )
        if apply.returncode != 0:
            self._git(["am", "--abort"], cwd=self.durable_worktree_path)
            return False, f"Failed to apply module patch for {basename}: {_combined_output(apply)}"

        amend = self._git(
            [
                "-c",
                f"user.name={CHECKPOINT_AUTHOR_NAME}",
                "-c",
                f"user.email={CHECKPOINT_AUTHOR_EMAIL}",
                "commit",
                "--amend",
                "-m",
                f"chore: checkpoint pdd sync for {basename}",
                "-m",
                self._checkpoint_trailer(basename),
            ],
            cwd=self.durable_worktree_path,
        )
        if amend.returncode != 0:
            return False, f"Failed to add checkpoint trailer: {_combined_output(amend)}"
        return True, ""

    def _commit_empty_checkpoint(self, basename: str) -> Tuple[bool, str]:
        commit = self._git(
            [
                "-c",
                f"user.name={CHECKPOINT_AUTHOR_NAME}",
                "-c",
                f"user.email={CHECKPOINT_AUTHOR_EMAIL}",
                "commit",
                "--allow-empty",
                "-m",
                f"chore: checkpoint pdd sync for {basename}",
                "-m",
                self._checkpoint_trailer(basename),
            ],
            cwd=self.durable_worktree_path,
        )
        if commit.returncode != 0:
            return False, f"Failed to create empty checkpoint commit: {_combined_output(commit)}"
        return True, ""

    def _push_checkpoint(self) -> Tuple[bool, str, str]:
        sha_result = self._git(["rev-parse", "HEAD"], cwd=self.durable_worktree_path)
        if sha_result.returncode != 0:
            return False, f"Failed to resolve checkpoint commit: {_combined_output(sha_result)}", ""
        sha = sha_result.stdout.strip()

        pushed, message = self._push_durable_head()
        return pushed, message, sha

    def _push_durable_head(self) -> Tuple[bool, str]:
        last_output = ""
        for attempt in range(1, 4):
            push = self._git(
                ["push", "origin", f"HEAD:refs/heads/{self.selected_branch}"],
                cwd=self.durable_worktree_path,
                timeout=120,
            )
            if push.returncode == 0:
                return True, ""
            last_output = _combined_output(push)
            lowered = last_output.lower()
            if (
                "non-fast-forward" in lowered
                or "fetch first" in lowered
                or "stale info" in lowered
                or "cannot lock ref" in lowered
            ):
                return False, f"Checkpoint push rejected: {last_output}"
            if attempt < 3:
                time.sleep(0.5 * attempt)

        return False, f"Checkpoint push failed after 3 attempts: {last_output}"

    def _push_unpushed_local_checkpoints(self) -> Tuple[bool, str]:
        range_args = ["log", "--format=%B"]
        remote_ref = f"refs/remotes/origin/{self.selected_branch}"
        if self._ref_exists(remote_ref):
            range_args.insert(1, f"origin/{self.selected_branch}..HEAD")

        log = self._git(range_args, cwd=self.durable_worktree_path)
        if log.returncode != 0:
            return False, f"Failed to inspect local checkpoint commits: {_combined_output(log)}"

        has_current_issue_checkpoint = False
        for line in log.stdout.splitlines():
            parsed = _parse_checkpoint_trailer(line)
            if parsed and parsed[0] == self.issue_number:
                has_current_issue_checkpoint = True
                break

        if not has_current_issue_checkpoint:
            return True, ""

        pushed, message = self._push_durable_head()
        if not pushed:
            return False, message
        return True, ""

    def _read_checkpointed_modules(self) -> Dict[str, Optional[str]]:
        """Map each checkpointed module (for this issue) to its ``needs_review``
        note (or ``None``). The newest trailer per module wins so a re-checkpoint
        that cleared/added the flag is honored on resume (round 8)."""
        log = self._git(["log", "--format=%B"], cwd=self.durable_worktree_path)
        if log.returncode != 0:
            return {}

        completed: Dict[str, Optional[str]] = {}
        for line in log.stdout.splitlines():  # git log is newest-first
            parsed = _parse_checkpoint_trailer(line)
            if not parsed:
                continue
            issue, module, review = parsed
            if issue == self.issue_number and module not in completed:
                completed[module] = review
        return completed

    def _checkpoint_trailer(self, basename: str) -> str:
        trailer = f"{CHECKPOINT_TRAILER}: issue={self.issue_number} module={basename}"
        # Carry an issue #1903 §B.4 "needs review" note into the durable
        # checkpoint (round 8): durable resume rebuilds module state from these
        # trailers only, so without this a resumed module loses its adopted-test
        # review warning and coverage loss would be silently swallowed. The note
        # is prose with spaces; trailer values are whitespace-free, so base64url
        # encode it (no padding — restored on parse).
        state = self.module_states.get(basename)
        review = getattr(state, "needs_review", None) if state is not None else None
        if review:
            enc = base64.urlsafe_b64encode(review.encode("utf-8")).decode("ascii").rstrip("=")
            trailer += f" review={enc}"
        return trailer

    def _ensure_clean_durable_worktree(self) -> Tuple[bool, str]:
        status = self._git(["status", "--porcelain"], cwd=self.durable_worktree_path)
        if status.returncode != 0:
            return False, f"Failed to inspect durable worktree: {_combined_output(status)}"
        if status.stdout.strip():
            return False, "Dedicated durable branch worktree is not clean"
        return True, ""

    def _cleanup_orphan_module_worktrees(self) -> Tuple[bool, str]:
        prune = self._git(["worktree", "prune"], cwd=self.git_root)
        if prune.returncode != 0:
            return False, f"Failed to prune git worktrees: {_combined_output(prune)}"

        registered = {path.resolve() for path in self._registered_worktree_paths()}
        prefix = f"sync-issue-{self.issue_number}-"
        worktrees_dir = self.git_root / ".pdd" / "worktrees"
        if not worktrees_dir.exists():
            return True, ""
        for child in worktrees_dir.iterdir():
            if not child.name.startswith(prefix):
                continue
            if child.resolve() in registered:
                continue
            self._remove_orphan_dir(child)
        return True, ""

    def _remove_worktree(self, worktree_path: Path) -> None:
        result = self._git(
            ["worktree", "remove", "--force", str(worktree_path)],
            cwd=self.git_root,
        )
        if result.returncode == 0:
            return
        self._git(["worktree", "prune"], cwd=self.git_root)
        registered = {path.resolve() for path in self._registered_worktree_paths()}
        if worktree_path.resolve() not in registered:
            self._remove_orphan_dir(worktree_path)

    def _remove_orphan_dir(self, path: Path) -> None:
        if path.exists():
            shutil.rmtree(path)

    def _is_forbidden_branch(self, branch: str) -> bool:
        if branch in {"main", "master"}:
            return True
        default_branch = self._default_branch_name()
        return bool(default_branch and branch == default_branch)

    def _default_branch_name(self) -> Optional[str]:
        ref = self._git(
            ["symbolic-ref", "--quiet", "--short", "refs/remotes/origin/HEAD"],
            cwd=self.git_root,
        )
        if ref.returncode != 0:
            return None
        name = ref.stdout.strip()
        if name.startswith("origin/"):
            return name[len("origin/"):]
        return name or None

    def _worktree_paths_for_branch(self, branch: str) -> List[Path]:
        paths: List[Path] = []
        current_path: Optional[Path] = None
        current_branch: Optional[str] = None
        listing = self._git(["worktree", "list", "--porcelain"], cwd=self.git_root)
        if listing.returncode != 0:
            return paths

        def flush() -> None:
            if current_path is not None and current_branch == f"refs/heads/{branch}":
                paths.append(current_path)

        for line in listing.stdout.splitlines():
            if line.startswith("worktree "):
                flush()
                current_path = Path(line[len("worktree "):]).resolve()
                current_branch = None
            elif line.startswith("branch "):
                current_branch = line[len("branch "):].strip()
            elif not line.strip():
                flush()
                current_path = None
                current_branch = None
        flush()
        return paths

    def _registered_worktree_paths(self) -> List[Path]:
        paths: List[Path] = []
        listing = self._git(["worktree", "list", "--porcelain"], cwd=self.git_root)
        if listing.returncode != 0:
            return paths
        for line in listing.stdout.splitlines():
            if line.startswith("worktree "):
                paths.append(Path(line[len("worktree "):]).resolve())
        return paths

    def _fetch_remote_branch(self, branch: str) -> Tuple[bool, bool, str]:
        if self._git(["remote", "get-url", "origin"], cwd=self.git_root).returncode != 0:
            return True, False, ""
        result = self._git(
            ["fetch", "origin", f"+refs/heads/{branch}:refs/remotes/origin/{branch}"],
            cwd=self.git_root,
            timeout=120,
        )
        if result.returncode == 0:
            return True, True, ""
        output = _combined_output(result)
        lowered = output.lower()
        if "couldn't find remote ref" in lowered or "could not find remote ref" in lowered:
            return True, False, ""
        return False, False, f"Failed to fetch durable branch {branch!r}: {output}"

    def _local_branch_exists(self, branch: str) -> bool:
        return self._ref_exists(f"refs/heads/{branch}")

    def _ref_exists(self, ref: str) -> bool:
        result = self._git(["show-ref", "--verify", "--quiet", ref], cwd=self.git_root)
        return result.returncode == 0

    def _git(
        self,
        args: List[str],
        *,
        cwd: Path,
        input_text: Optional[str] = None,
        timeout: int = 60,
    ) -> subprocess.CompletedProcess[str]:
        git_executable = shutil.which("git") or "git"
        # Arguments are passed directly to git without a shell.
        return subprocess.run(  # nosec B603
            [git_executable, *args],
            cwd=str(cwd),
            input=input_text,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )


def _parse_checkpoint_trailer(line: str) -> Optional[Tuple[int, str, Optional[str]]]:
    prefix = f"{CHECKPOINT_TRAILER}:"
    stripped = line.strip()
    if not stripped.startswith(prefix):
        return None
    body = stripped[len(prefix):].strip()
    fields = dict(re.findall(r"(\w+)=([^\s]+)", body))
    try:
        issue = int(fields["issue"])
    except (KeyError, ValueError):
        return None
    module = fields.get("module")
    if not module:
        return None
    review: Optional[str] = None
    enc = fields.get("review")
    if enc:
        try:
            pad = "=" * (-len(enc) % 4)
            review = base64.urlsafe_b64decode(enc + pad).decode("utf-8")
        except (binascii.Error, ValueError, UnicodeDecodeError):
            review = None
    return issue, module, review


def _slugify_basename(basename: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_.-]+", "-", basename).strip("-")
    digest = sha1(basename.encode("utf-8"), usedforsecurity=False).hexdigest()[:8]
    return f"{slug or 'module'}-{digest}"


def _pdd_path_index(path: str) -> Optional[int]:
    if path.startswith(".pdd/"):
        return 0
    marker = "/.pdd/"
    index = path.find(marker)
    if index == -1:
        return None
    return index + 1


def _combined_output(result: subprocess.CompletedProcess[str]) -> str:
    return (result.stderr or result.stdout or "").strip()
