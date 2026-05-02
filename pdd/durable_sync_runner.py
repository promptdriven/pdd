"""Durable issue-sync runner.

This runner keeps the existing issue-sync scheduling model, but isolates each
module in its own git worktree and checkpoints successful module output to a
durable branch before marking the module complete.
"""
# pylint: disable=duplicate-code,too-many-arguments,too-many-instance-attributes
# pylint: disable=too-few-public-methods
from __future__ import annotations

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

from .agentic_sync_runner import AsyncSyncRunner, MAX_WORKERS

CHECKPOINT_TRAILER = "PDD-Sync-Checkpoint-V1"
CHECKPOINT_AUTHOR_NAME = "PDD Durable Sync"
CHECKPOINT_AUTHOR_EMAIL = "pdd-durable-sync@example.invalid"


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
        initial_cost: float = 0.0,
    ) -> None:
        self.issue_number = issue_number
        self.git_root = project_root.resolve()
        self.selected_branch = durable_branch or f"sync/issue-{issue_number}"
        self.no_resume = no_resume
        self.durable_max_parallel = durable_max_parallel
        self.parent_module_cwds = dict(module_cwds or {})
        self.durable_worktree_path = (
            self.git_root / ".pdd" / "worktrees" / f"durable-issue-{issue_number}"
        )
        self._checkpoint_lock = threading.Lock()
        self._checkpoint_halted = threading.Event()
        self._run_id = uuid.uuid4().hex[:8]
        self._prepared = False

        super().__init__(
            basenames=basenames,
            dep_graph=dep_graph,
            sync_options=sync_options,
            github_info=github_info,
            quiet=quiet,
            verbose=verbose,
            issue_url=issue_url,
            module_cwds={},
            initial_cost=initial_cost,
        )
        self.project_root = self.git_root
        if self.total_budget is not None:
            self.max_workers = 1
        elif durable_max_parallel is not None:
            self.max_workers = max(1, int(durable_max_parallel))
        else:
            self.max_workers = MAX_WORKERS

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

        push_ok, push_msg = self._push_unpushed_local_checkpoints()
        if not push_ok:
            return False, push_msg

        if not self.no_resume:
            completed = self._read_checkpointed_modules()
            for basename in self.basenames:
                if basename in completed:
                    self.module_states[basename].status = "success"
                    self._resumed_modules.append(basename)

        self._prepared = True
        return True, ""

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

    def _force_add_module_metadata(self, basename: str, module_worktree: Path) -> None:
        safe = basename.replace("/", "_")
        meta_dirs = [
            module_worktree / prefix
            for prefix in self._allowed_metadata_prefixes(basename)
        ]

        paths = []
        for meta_dir in meta_dirs:
            if meta_dir.exists():
                paths.extend(sorted(meta_dir.glob(f"{safe}_*.json")))
        if not paths:
            return
        rel_paths = [str(path.relative_to(module_worktree)) for path in paths]
        self._git(["add", "-f", "--", *rel_paths], cwd=module_worktree)

    def _unsafe_staged_paths(self, basename: str, paths: List[str]) -> List[str]:
        safe = basename.replace("/", "_")
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
                    if not meta_name.startswith(f"{safe}_") or not meta_name.endswith(".json"):
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
        parent_cwd = self.parent_module_cwds.get(basename)
        if parent_cwd is not None:
            try:
                rel = parent_cwd.resolve().relative_to(self.git_root)
            except ValueError:
                rel = None
            if rel and rel != Path("."):
                prefixes.append(rel / ".pdd" / "meta")
        return prefixes

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

    def _read_checkpointed_modules(self) -> Set[str]:
        log = self._git(["log", "--format=%B"], cwd=self.durable_worktree_path)
        if log.returncode != 0:
            return set()

        completed: Set[str] = set()
        for line in log.stdout.splitlines():
            parsed = _parse_checkpoint_trailer(line)
            if not parsed:
                continue
            issue, module = parsed
            if issue == self.issue_number:
                completed.add(module)
        return completed

    def _checkpoint_trailer(self, basename: str) -> str:
        return f"{CHECKPOINT_TRAILER}: issue={self.issue_number} module={basename}"

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


def _parse_checkpoint_trailer(line: str) -> Optional[Tuple[int, str]]:
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
    return issue, module


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
