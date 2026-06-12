from __future__ import annotations

import functools
import hashlib
import logging
import os
import signal
import sys
import json
import shutil
import subprocess
import tempfile
import time
import uuid
import re
import random
from datetime import datetime, timedelta, timezone, tzinfo
from pathlib import Path
from zoneinfo import ZoneInfo
from typing import Any, Dict, List, Optional, Set, Tuple, Union
from dataclasses import dataclass

from rich.console import Console

_steer_logger = logging.getLogger(__name__ + ".steer")

AgenticUsage = Optional[Dict[str, List[Dict[str, Any]]]]
ClaudePolicy = Dict[str, Any]
_FILESYSTEM_POLICY_KEYS: Tuple[str, str] = ("writableRoots", "readOnlyRoots")


class AgenticUnsupportedSemanticsError(ValueError):
    """Raised when a requested agentic policy cannot be enforced by PDD."""


def get_agentic_capabilities() -> Dict[str, Any]:
    """Return machine-checkable agentic capability contracts for callers."""
    return {
        "claude_policy": {
            "schema_version": 2,
            "fields": {
                "allowedTools": ["string", "null"],
                "addDirs": "list[string]",
                "writableRoots": "list[string]",
                "readOnlyRoots": "list[string]",
                "noSessionPersistence": {
                    "standard": "boolean",
                    "interactive": False,
                },
                "outputFormat": ["json"],
            },
            "modes": {
                "standard": {"noSessionPersistence": True},
                "interactive": {
                    "noSessionPersistence": False,
                    "usageSource": "persisted_session_transcript",
                },
            },
            "filesystemPolicy": {
                "schemaVersion": 1,
                "writableRoots": True,
                "readOnlyRoots": True,
                "enforcement": "post_run_audit_fail_closed",
                "auditsGitMetadata": True,
                "auditsLinkedGitMetadata": True,
                "pddOwnedLogChanges": "chained_exact_signature_verified_only",
                "providerLogDirWritesAudited": True,
                "auditsDirectoryMetadata": True,
                "escapedSymlinkTargets": "fail_closed",
                "unrestrictedBashWithFilesystemRoots": "rejected",
                "symlinkTargetAllowRoots": [
                    "cwd",
                    "addDirs",
                    "writableRoots",
                    "readOnlyRoots",
                ],
                "nonFollowingPolicyRootIdentity": True,
            },
            "result": {
                "schemaVersion": 1,
                "changedFiles": {
                    "pythonAttribute": "changed_files",
                    "dictKey": "changed_files",
                },
            },
        }
    }


def _allowed_tools_include_unrestricted_bash(allowed_tools: Optional[str]) -> bool:
    """Return True when allowedTools grants unrestricted Bash execution."""
    if allowed_tools is None:
        return False
    for token in allowed_tools.split(","):
        normalized = re.sub(r"\s+", "", token).lower()
        if normalized in {"bash", "bash(*)"}:
            return True
    return False


def validate_claude_policy(policy: Any, *, interactive: bool = False) -> ClaudePolicy:
    """Validate and normalize the Claude CLI policy contract PDD enforces."""
    if not isinstance(policy, dict):
        raise AgenticUnsupportedSemanticsError("claude_policy must be an object")

    allowed_keys = {
        "allowedTools",
        "addDirs",
        "writableRoots",
        "readOnlyRoots",
        "noSessionPersistence",
        "outputFormat",
    }
    unknown = sorted(set(policy) - allowed_keys)
    if unknown:
        raise AgenticUnsupportedSemanticsError(
            f"claude_policy contains unsupported keys: {', '.join(unknown)}"
        )

    allowed_tools = policy.get("allowedTools")
    if allowed_tools is not None and not isinstance(allowed_tools, str):
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.allowedTools must be a string or null"
        )
    if isinstance(allowed_tools, str) and not allowed_tools.strip():
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.allowedTools must not be an empty string; use null for no tools"
        )

    add_dirs = policy.get("addDirs", [])
    if not isinstance(add_dirs, list) or not all(isinstance(p, str) for p in add_dirs):
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.addDirs must be a list of strings"
        )

    normalized_roots: Dict[str, List[str]] = {}
    for key in _FILESYSTEM_POLICY_KEYS:
        if key not in policy:
            continue
        roots = policy.get(key)
        if not isinstance(roots, list) or not all(isinstance(p, str) for p in roots):
            raise AgenticUnsupportedSemanticsError(
                f"claude_policy.{key} must be a list of strings"
            )
        if any(not p.strip() for p in roots):
            raise AgenticUnsupportedSemanticsError(
                f"claude_policy.{key} must not contain empty paths"
            )
        normalized_roots[key] = list(roots)
    if normalized_roots and _allowed_tools_include_unrestricted_bash(allowed_tools):
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.allowedTools must not include unrestricted Bash when "
            "writableRoots or readOnlyRoots are declared because PDD cannot "
            "audit shell writes outside the filesystem policy roots"
        )

    no_session = policy.get("noSessionPersistence", False)
    if not isinstance(no_session, bool):
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.noSessionPersistence must be a boolean"
        )
    if interactive and no_session:
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.noSessionPersistence is unsupported in interactive "
            "Claude mode because Claude Code marks the flag as print-mode-only "
            "and PDD interactive billing uses the persisted session transcript"
        )

    output_format = policy.get("outputFormat", "json")
    if output_format != "json":
        raise AgenticUnsupportedSemanticsError(
            "claude_policy.outputFormat must be json"
        )

    normalized = {
        "allowedTools": allowed_tools,
        "addDirs": list(add_dirs),
        "noSessionPersistence": no_session,
        "outputFormat": "json",
    }
    normalized.update(normalized_roots)
    return normalized


def _append_claude_policy_args(cmd: List[str], claude_policy: ClaudePolicy) -> None:
    """Append Claude CLI args that enforce the validated policy."""
    allowed_tools = claude_policy["allowedTools"]
    if allowed_tools is None:
        cmd.extend(["--tools", ""])
    else:
        cmd.extend(["--allowedTools", allowed_tools])
    add_dirs: List[str] = []
    for key in ("addDirs", "writableRoots", "readOnlyRoots"):
        for path in claude_policy.get(key, []):
            if path not in add_dirs:
                add_dirs.append(path)
    for add_dir in add_dirs:
        cmd.extend(["--add-dir", add_dir])
    if claude_policy["noSessionPersistence"]:
        cmd.append("--no-session-persistence")


@dataclass
class _FilesystemPolicySnapshot:
    files: Dict[Path, str]
    errors: List[str]
    escaped_symlink_targets: Dict[Path, Path]


def _claude_policy_has_filesystem_roots(policy: Optional[ClaudePolicy]) -> bool:
    """Return True when caller requested the filesystem audit policy."""
    return bool(
        policy is not None and any(key in policy for key in _FILESYSTEM_POLICY_KEYS)
    )


def _path_is_within(path: Path, root: Path) -> bool:
    """Return True when *path* is equal to or contained by *root*."""
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def _record_resolution_error(
    errors: Optional[List[str]],
    path: Path,
    context: str,
    exc: Exception,
) -> None:
    """Record or re-raise path resolution failures."""
    if errors is None:
        raise exc
    if isinstance(exc, RuntimeError):
        errors.append(f"{path}: symlink loop while resolving {context}: {exc}")
    else:
        errors.append(f"{path}: {exc}")


def _resolve_audit_path(
    path: Path,
    errors: Optional[List[str]],
    context: str,
) -> Optional[Path]:
    """Resolve a path and route audit failures into *errors*."""
    try:
        return path.resolve(strict=False)
    except (RuntimeError, OSError) as exc:
        _record_resolution_error(errors, path, context, exc)
        return None


def _resolve_policy_path(
    cwd: Path,
    raw_path: str,
    errors: Optional[List[str]] = None,
) -> Optional[Path]:
    """Resolve a policy path without following its final symlink component."""
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = cwd / path
    try:
        if path.name in ("", os.pardir):
            return path.resolve(strict=False)
        return path.parent.resolve(strict=False) / path.name
    except (RuntimeError, OSError) as exc:
        _record_resolution_error(errors, path, f"policy root {raw_path}", exc)
        return None


def _resolve_policy_roots(
    cwd: Path,
    policy: ClaudePolicy,
    key: str,
    errors: Optional[List[str]] = None,
) -> List[Path]:
    """Resolve and deduplicate root paths from a normalized policy key."""
    roots: List[Path] = []
    for raw_path in policy.get(key, []):
        resolved = _resolve_policy_path(cwd, raw_path, errors)
        if resolved is None:
            continue
        if resolved not in roots:
            roots.append(resolved)
    return roots


def _resolve_git_metadata_path(base_dir: Path, raw_path: str) -> Path:
    """Resolve a git metadata path from a gitdir/commondir pointer file."""
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = base_dir / path
    return path.resolve(strict=False)


def _linked_git_metadata_roots(cwd: Path) -> List[Path]:
    """Return linked-worktree git metadata roots referenced by cwd/.git."""
    git_pointer = cwd / ".git"
    try:
        if not git_pointer.is_file():
            return []
        line = git_pointer.read_text(encoding="utf-8", errors="replace").splitlines()[0]
    except (IndexError, OSError, UnicodeError):
        return []

    if not line.lower().startswith("gitdir:"):
        return []

    raw_gitdir = line.split(":", 1)[1].strip()
    if not raw_gitdir:
        return []

    roots: List[Path] = []
    git_dir = _resolve_git_metadata_path(git_pointer.parent, raw_gitdir)
    roots.append(git_dir)

    common_dir_file = git_dir / "commondir"
    try:
        raw_common_dir = common_dir_file.read_text(
            encoding="utf-8",
            errors="replace",
        ).splitlines()[0].strip()
    except (IndexError, OSError, UnicodeError):
        raw_common_dir = ""

    if raw_common_dir:
        common_dir = _resolve_git_metadata_path(git_dir, raw_common_dir)
        if common_dir not in roots:
            roots.append(common_dir)
    return roots


def _collapse_audit_roots(roots: List[Path]) -> List[Path]:
    """Remove duplicate/nested audit roots so recursive snapshots stay bounded."""
    collapsed: List[Path] = []
    for root in sorted(set(roots), key=lambda p: (len(p.parts), str(p))):
        if any(_path_is_within(root, existing) for existing in collapsed):
            continue
        collapsed.append(root)
    return collapsed


def _audit_entry_path(path: Path) -> Path:
    """Return a stable absolute audit key without following the symlink leaf."""
    if path.is_symlink():
        return path.parent.resolve(strict=False) / path.name
    return path.resolve(strict=False)


def _resolve_symlink_target_path(
    link_path: Path,
    raw_target: str,
    errors: List[str],
) -> Optional[Path]:
    """Resolve a symlink target path relative to its link parent."""
    target_path = Path(raw_target)
    if not target_path.is_absolute():
        target_path = link_path.parent / target_path
    try:
        return target_path.resolve(strict=False)
    except RuntimeError as exc:
        errors.append(f"{link_path}: symlink loop while resolving {raw_target}: {exc}")
        return None
    except OSError as exc:
        errors.append(f"{link_path}: {exc}")
        return None


def _filesystem_signature(path: Path, errors: List[str]) -> str:
    """Return a content-aware signature for an audited filesystem path."""
    try:
        stat_result = path.lstat()
    except FileNotFoundError:
        return "missing"
    except OSError as exc:
        errors.append(f"{path}: {exc}")
        return "error"

    if path.is_symlink():
        try:
            target = os.readlink(path)
        except OSError as exc:
            errors.append(f"{path}: {exc}")
            target = "<unreadable>"
        return f"symlink:{stat_result.st_mode}:{target}"

    if path.is_file():
        digest = hashlib.sha256()
        try:
            with open(path, "rb") as handle:
                while True:
                    chunk = handle.read(1024 * 1024)
                    if not chunk:
                        break
                    digest.update(chunk)
        except OSError as exc:
            errors.append(f"{path}: {exc}")
            return f"file-error:{stat_result.st_mode}:{stat_result.st_size}"
        return f"file:{stat_result.st_mode}:{stat_result.st_size}:{digest.hexdigest()}"

    if path.is_dir():
        return (
            f"dir:{stat_result.st_mode}:{stat_result.st_size}:"
            f"{stat_result.st_mtime_ns}"
        )

    return (
        f"other:{stat_result.st_mode}:{stat_result.st_size}:"
        f"{stat_result.st_mtime_ns}"
    )


def _record_escaped_symlink_target(
    link_path: Path,
    target_path: Path,
    symlink_target_roots: List[Path],
    escaped_symlink_targets: Dict[Path, Path],
) -> None:
    """Record symlinks whose targets leave the caller-allowed target roots."""
    if any(_path_is_within(target_path, root) for root in symlink_target_roots):
        return
    escaped_symlink_targets[_audit_entry_path(link_path)] = target_path


def _snapshot_audit_path(
    path: Path,
    files: Dict[Path, str],
    errors: List[str],
    symlink_target_roots: List[Path],
    escaped_symlink_targets: Dict[Path, Path],
) -> None:
    """Add one filesystem path to the snapshot and track symlink escapes."""
    entry_path = _audit_entry_path(path)
    files[entry_path] = _filesystem_signature(path, errors)
    if not path.is_symlink():
        return
    try:
        raw_target = os.readlink(path)
    except OSError as exc:
        errors.append(f"{path}: {exc}")
        return
    target_path = _resolve_symlink_target_path(path, raw_target, errors)
    if target_path is None:
        return
    _record_escaped_symlink_target(
        path,
        target_path,
        symlink_target_roots,
        escaped_symlink_targets,
    )


def _snapshot_audit_root(
    root: Path,
    files: Dict[Path, str],
    errors: List[str],
    symlink_target_roots: List[Path],
    escaped_symlink_targets: Dict[Path, Path],
) -> None:
    """Add all auditable files under *root* to *files*."""
    if root.is_symlink():
        _snapshot_audit_path(
            root,
            files,
            errors,
            symlink_target_roots,
            escaped_symlink_targets,
        )
        return
    if not root.exists():
        return
    if root.is_file():
        _snapshot_audit_path(
            root,
            files,
            errors,
            symlink_target_roots,
            escaped_symlink_targets,
        )
        return
    if not root.is_dir():
        _snapshot_audit_path(
            root,
            files,
            errors,
            symlink_target_roots,
            escaped_symlink_targets,
        )
        return
    _snapshot_audit_path(
        root,
        files,
        errors,
        symlink_target_roots,
        escaped_symlink_targets,
    )

    def on_walk_error(exc: OSError) -> None:
        errors.append(f"{root}: {exc}")

    for current, dirnames, filenames in os.walk(
        root,
        topdown=True,
        onerror=on_walk_error,
    ):
        current_path = Path(current)
        for dirname in list(dirnames):
            dir_path = current_path / dirname
            if dir_path.is_symlink():
                _snapshot_audit_path(
                    dir_path,
                    files,
                    errors,
                    symlink_target_roots,
                    escaped_symlink_targets,
                )
            else:
                _snapshot_audit_path(
                    dir_path,
                    files,
                    errors,
                    symlink_target_roots,
                    escaped_symlink_targets,
                )
        for filename in filenames:
            file_path = current_path / filename
            _snapshot_audit_path(
                file_path,
                files,
                errors,
                symlink_target_roots,
                escaped_symlink_targets,
            )


def _take_filesystem_policy_snapshot(
    cwd: Path,
    policy: ClaudePolicy,
) -> _FilesystemPolicySnapshot:
    """Snapshot files under cwd, addDirs, writable roots, and read-only roots."""
    files: Dict[Path, str] = {}
    errors: List[str] = []
    escaped_symlink_targets: Dict[Path, Path] = {}

    resolved_cwd = _resolve_audit_path(cwd, errors, "cwd")
    if resolved_cwd is None:
        return _FilesystemPolicySnapshot(
            files=files,
            errors=errors,
            escaped_symlink_targets=escaped_symlink_targets,
        )

    symlink_target_roots = [resolved_cwd]
    for key in ("addDirs", "writableRoots", "readOnlyRoots"):
        symlink_target_roots.extend(
            _resolve_policy_roots(resolved_cwd, policy, key, errors)
        )
    snapshot_roots = list(symlink_target_roots)
    snapshot_roots.extend(_linked_git_metadata_roots(resolved_cwd))

    audit_roots = _collapse_audit_roots(snapshot_roots)
    collapsed_symlink_target_roots = _collapse_audit_roots(symlink_target_roots)
    for root in audit_roots:
        _snapshot_audit_root(
            root,
            files,
            errors,
            collapsed_symlink_target_roots,
            escaped_symlink_targets,
        )
    return _FilesystemPolicySnapshot(
        files=files,
        errors=errors,
        escaped_symlink_targets=escaped_symlink_targets,
    )


def _display_audit_path(cwd: Path, path: Path) -> str:
    """Render cwd-contained paths as POSIX relative paths, else absolute paths."""
    resolved_cwd = cwd.resolve(strict=False)
    try:
        return path.relative_to(resolved_cwd).as_posix()
    except ValueError:
        return str(path)


def _format_audit_paths(paths: List[str], *, limit: int = 12) -> str:
    """Format changed paths for concise policy messages."""
    shown = paths[:limit]
    suffix = f" (+{len(paths) - limit} more)" if len(paths) > limit else ""
    return ", ".join(shown) + suffix


@dataclass
class _PddOwnedLogWrite:
    path: Path
    before_signature: str
    after_signature: str


def _record_pdd_owned_log_signature(
    log_write: Optional[_PddOwnedLogWrite],
    signatures: Dict[Path, str],
    baseline: Optional[_FilesystemPolicySnapshot],
) -> None:
    """Record the exact post-write signature of a PDD-owned log file."""
    if log_write is None:
        return
    entry_path = _audit_entry_path(log_write.path)
    baseline_signature = (
        signatures.get(entry_path)
        if entry_path in signatures
        else (
            baseline.files.get(entry_path, "missing")
            if baseline is not None
            else log_write.before_signature
        )
    )
    if log_write.before_signature != baseline_signature:
        return
    signatures[entry_path] = log_write.after_signature


def _is_trusted_pdd_owned_log_change(
    path: Path,
    after_signature: Optional[str],
    signatures: Dict[Path, str],
) -> bool:
    """Return True only for exact PDD-owned log writes with matching signatures."""
    if after_signature is None:
        return False
    return signatures.get(path) == after_signature


def _is_directory_signature(signature: Optional[str]) -> bool:
    """Return True when a snapshot signature describes a directory."""
    return bool(signature and signature.startswith("dir:"))


def _is_directory_change(
    path: Path,
    before: _FilesystemPolicySnapshot,
    after: _FilesystemPolicySnapshot,
) -> bool:
    """Return True when a changed path is a directory in either snapshot."""
    return (
        _is_directory_signature(before.files.get(path))
        or _is_directory_signature(after.files.get(path))
    )


def _filter_redundant_directory_changes(
    paths: List[Path],
    before: _FilesystemPolicySnapshot,
    after: _FilesystemPolicySnapshot,
    explained_paths: Optional[Set[Path]] = None,
) -> List[Path]:
    """Drop directory mtime changes when a changed descendant is also reported."""
    all_explained_paths = list(paths) + list(explained_paths or set())
    filtered: List[Path] = []
    for path in paths:
        if _is_directory_change(path, before, after) and any(
            other != path and _path_is_within(other, path)
            for other in all_explained_paths
        ):
            continue
        filtered.append(path)
    return filtered


def _escaped_symlink_target_for_path(
    path: Path,
    before: _FilesystemPolicySnapshot,
    after: _FilesystemPolicySnapshot,
) -> Path:
    """Return the known escaped symlink target without assuming snapshot side."""
    if path in after.escaped_symlink_targets:
        return after.escaped_symlink_targets[path]
    return before.escaped_symlink_targets[path]


def _audit_filesystem_policy(
    cwd: Path,
    policy: Optional[ClaudePolicy],
    before: Optional[_FilesystemPolicySnapshot],
    pdd_owned_log_signatures: Optional[Dict[Path, str]] = None,
) -> Tuple[List[str], Optional[str]]:
    """Compare filesystem snapshots and return changed files plus violation text."""
    if policy is None or before is None:
        return [], None

    after = _take_filesystem_policy_snapshot(cwd, policy)
    if before.errors or after.errors:
        errors = before.errors + after.errors
        detail = _format_audit_paths(errors)
        return [], f"Filesystem policy audit failed; refusing result: {detail}"

    pdd_owned_log_signatures = pdd_owned_log_signatures or {}
    comparison_paths = (
        set(before.files) | set(after.files) | set(pdd_owned_log_signatures)
    )
    trusted_pdd_log_paths = {
        path for path, signature in pdd_owned_log_signatures.items()
        if after.files.get(path) == signature
    }
    changed_paths = sorted(
        _filter_redundant_directory_changes(
            [
                path for path in comparison_paths
                if (
                    before.files.get(path) != after.files.get(path)
                    or (
                        path in pdd_owned_log_signatures
                        and after.files.get(path) != pdd_owned_log_signatures[path]
                    )
                )
                and not _is_trusted_pdd_owned_log_change(
                    path,
                    after.files.get(path),
                    pdd_owned_log_signatures,
                )
            ],
            before,
            after,
            trusted_pdd_log_paths,
        ),
        key=str,
    )
    escaped_symlink_paths = sorted(
        set(before.escaped_symlink_targets) | set(after.escaped_symlink_targets),
        key=str,
    )
    reported_paths = sorted(set(changed_paths) | set(escaped_symlink_paths), key=str)
    escaped_symlink_files = [
        (
            _display_audit_path(cwd, path),
            str(_escaped_symlink_target_for_path(path, before, after)),
        )
        for path in escaped_symlink_paths
    ]
    changed_files = [_display_audit_path(cwd, path) for path in reported_paths]
    if not reported_paths:
        return changed_files, None

    resolved_cwd = cwd.resolve(strict=False)
    writable_roots = _resolve_policy_roots(resolved_cwd, policy, "writableRoots")
    read_only_roots = _resolve_policy_roots(resolved_cwd, policy, "readOnlyRoots")

    outside_writable = [
        path for path in changed_paths
        if not any(_path_is_within(path, root) for root in writable_roots)
    ]
    inside_read_only = [
        path for path in changed_paths
        if any(_path_is_within(path, root) for root in read_only_roots)
    ]
    if not outside_writable and not inside_read_only and not escaped_symlink_files:
        return changed_files, None

    lines = [
        "Filesystem policy violation: changed files must stay inside "
        "caller-declared writable roots and outside declared read-only roots.",
    ]
    if outside_writable:
        lines.append(
            "Changed files outside writable roots: "
            + _format_audit_paths(
                [_display_audit_path(cwd, path) for path in outside_writable]
            )
        )
    if inside_read_only:
        lines.append(
            "Changed files inside read-only roots: "
            + _format_audit_paths(
                [_display_audit_path(cwd, path) for path in inside_read_only]
            )
        )
    if escaped_symlink_files:
        symlink_details = [
            f"{display_path} -> {target_path}"
            for display_path, target_path in escaped_symlink_files
        ]
        lines.append(
            "symlink targets outside audited roots: "
            + _format_audit_paths(symlink_details)
        )
    lines.append("Changed files: " + _format_audit_paths(changed_files))
    return changed_files, "\n".join(lines)


def _interactive_allowed_tools(allowed_tools: Optional[str]) -> Optional[str]:
    """Add PDD's reply MCP tool while preserving caller tool restrictions."""
    reply_tool = "mcp__pdd__pdd_reply"
    if allowed_tools is None:
        return reply_tool
    tools = [tool.strip() for tool in allowed_tools.split(",") if tool.strip()]
    if reply_tool not in tools:
        tools.append(reply_tool)
    return ",".join(tools)


def _load_model_data(*args, **kwargs):
    """Lazily load model data from ``pdd.llm_invoke``.

    The real loader lives in ``pdd.llm_invoke``, but a top-level import here
    creates a circular import: ``pdd/__init__.py`` imports this module, which
    would import ``pdd.llm_invoke``, which (transitively, via the FastAPI
    routes) imports back into ``pdd.agentic_common`` while it is still
    initializing. Importing inside the helpers defers the resolution until
    after package import completes. Returns ``None`` when the loader is
    genuinely unavailable.
    """
    try:
        from pdd.llm_invoke import _load_model_data as _real_loader
    except ImportError:
        return None
    return _real_loader(*args, **kwargs)

# Constants
_DEFAULT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai", "opencode"]

# Default number of tail lines to scan for semantic regex patterns.
# Semantic matching is restricted to the tail to prevent false positives
# when LLMs quote/discuss a status without declaring it (Issue #865).
_SEMANTIC_TAIL_LINES = 30

# Semantic fallback patterns for when LLMs paraphrase instead of emitting exact tokens.
# Each token maps to a list of regex patterns that capture common paraphrases.
# Patterns are checked only after exact and case-insensitive matching fail,
# and only in the tail of the output.
SEMANTIC_PATTERNS: Dict[str, List[str]] = {
    "ALL_TESTS_PASS": [
        r"\ball\b.*\btests?\b.*\bpass",         # "all tests pass", "all 18 tests pass"
        r"\d+/\d+\s+pass",                     # "18/18 passing"
        r"both\s+passed",                       # "both passed"
        r"all\s+tests?\s+(are\s+)?green",       # "all tests are green"
        r"all\s+tests?\s+passed\s+successfully", # "all tests passed successfully"
        r"tests?\s+suite\s+passed",             # "test suite passed"
        r"100%\s+pass",                         # "100% passing"
        r"\b\d+\s+passed\b(?!.*\b\d+\s+failed\b)", # "788 passed" (no failures mentioned)
        r"\bfix\b.*\bcomplete\b",               # "fix is complete"
        r"\bverif(?:ied|ication)\b.*\bcleanly\b", # "verification completed cleanly"
    ],
    "NOT_A_BUG": [
        r"\bnot\s+(?:actually\s+)?(?:a\s+)?(?:real\s+)?bug\b", # "not a bug", "not a real bug", "not actually a bug"
        r"(it\s+is\s+|already\s+)fixed",        # "it is already fixed", "already fixed"
        r"expected\s+behavio[u]?r",             # "expected behavior"
        r"working\s+(as\s+)?(designed|intended|correctly|expected)", # "working correctly"
        r"not\s+(actually\s+)?a\s+(code\s+)?issue", # "not actually an issue"
    ],
    "CONTINUE_CYCLE": [
        r"tests?\s+still\s+fail",              # "tests still failing"
        r"more\s+work\s+needed",                # "more work needed"
        r"not\s+yet\s+(fixed|resolved|passing)", # "not yet fixed"
        r"continue\s+(to\s+)?(next\s+)?cycle",  # "continue to next cycle"
    ],
    "MAX_CYCLES_REACHED": [
        r"max(imum)?\s+cycles?\s+(reached|exceeded|limit)", # "max cycles reached"
        r"cycle\s+limit\s+(reached|exceeded)",  # "cycle limit reached"
    ],
    "STOP_CONDITION": [
        r"awaiting\s+(architectural\s+)?decisions", # "awaiting decisions"
        r"clarification\s+(is\s+)?needed",      # "clarification is needed"
        r"need[s]?\s+clarification\s+(from|before)", # "needs clarification from/before"
        r"need[s]?\s+more\s+info(rmation)?\s+(from|before)", # "needs more info from"
    ],
}


@dataclass
class TokenMatch:
    """Result of control token detection with tier and pattern info."""
    tier: str  # "exact", "case_insensitive", "semantic", "llm_classification"
    token: Optional[str] = None  # The classified token (e.g., "NOT_A_BUG", "ALL_TESTS_PASS")
    pattern: Optional[str] = None
    cost: Optional[float] = None

    def __bool__(self) -> bool:
        return True


class AgenticTaskResult(tuple):
    """Public result for ``run_agentic_task`` with legacy four-item unpacking.

    The underlying tuple has five fields so downstream bridges can detect
    structured usage with ``isinstance(result, tuple)``, ``len(result) >= 5``,
    and ``result[4]``. Iteration intentionally yields the historical four
    fields to preserve existing ``success, output, cost, provider = ...``
    callers. Changed-file metadata is stored as an attribute so the indexed
    usage slot remains stable.
    """

    def __new__(
        cls,
        success: bool,
        output_text: str,
        cost_usd: float,
        provider: str,
        usage: AgenticUsage = None,
        *,
        changed_files: Optional[List[str]] = None,
    ) -> "AgenticTaskResult":
        result = tuple.__new__(
            cls,
            (success, output_text, cost_usd, provider, usage),
        )
        result._changed_files = list(changed_files or [])
        return result

    def __iter__(self):
        return (tuple.__getitem__(self, i) for i in range(4))

    @property
    def success(self) -> bool:
        return bool(tuple.__getitem__(self, 0))

    @property
    def output_text(self) -> str:
        return str(tuple.__getitem__(self, 1))

    @property
    def cost_usd(self) -> float:
        return float(tuple.__getitem__(self, 2))

    @property
    def provider(self) -> str:
        return str(tuple.__getitem__(self, 3))

    @property
    def usage(self) -> AgenticUsage:
        return tuple.__getitem__(self, 4)

    @property
    def changed_files(self) -> List[str]:
        return list(getattr(self, "_changed_files", []))

    def to_dict(self) -> Dict[str, Any]:
        """Return a JSON-serializable mapping shape for structured consumers."""
        return {
            "success": self.success,
            "output_text": self.output_text,
            "cost_usd": self.cost_usd,
            "provider": self.provider,
            "usage": self.usage,
            "changed_files": self.changed_files,
        }


class _ProviderRunResult(tuple):
    """Internal provider result carrying optional structured usage."""

    def __new__(
        cls,
        success: bool,
        output_text: str,
        cost_usd: float,
        model: Optional[str],
        usage: AgenticUsage = None,
    ) -> "_ProviderRunResult":
        return tuple.__new__(cls, (success, output_text, cost_usd, model, usage))

    def __iter__(self):
        return (tuple.__getitem__(self, i) for i in range(4))

    @property
    def usage(self) -> AgenticUsage:
        return tuple.__getitem__(self, 4)


@dataclass
class SteerEntry:
    """Mid-run user steering entry (typically from GitHub issue comments)."""

    comment_id: str
    author: str
    body: str


def _steer_body_for_llm(body: str) -> str:
    """Remove human-only ``<pdd>...</pdd>`` blocks before LLM-facing steer text."""
    from pdd.preprocess import process_pdd_tags

    return process_pdd_tags(body).strip()


STEER_STATE_KEYS = (
    "last_steered_comment_id",
    "last_steer_at",
    "steer_generation",
    "steer_cursor_seeded",
)


def merge_steer_state(from_state: Dict[str, Any], into_state: Dict[str, Any]) -> None:
    """Copy steer cursor fields from *from_state* into *into_state*."""
    for key in STEER_STATE_KEYS:
        if key in from_state:
            into_state[key] = from_state[key]


def _step_output_awaiting_clarification(output: str) -> bool:
    """True when a cached step output indicates a clarification hard-stop."""
    if not isinstance(output, str) or not output:
        return False
    if re.search(r"STOP_CONDITION:\s*.+", output, re.IGNORECASE):
        return True
    # Bug orchestrator step 3 uses substring matching (no STOP_CONDITION tag).
    if re.search(r"Needs\s+More\s+Info", output, re.IGNORECASE):
        return True
    return False


def workflow_awaiting_clarification(
    state: Dict[str, Any],
    clarification_step_numbers: Set[int],
) -> bool:
    """True when cached outputs show the workflow paused for user clarification."""
    outputs = state.get("step_outputs") or {}
    for step in clarification_step_numbers:
        out = outputs.get(str(step), "")
        if _step_output_awaiting_clarification(out):
            return True
    return False


def merge_steers_into_issue_content(
    issue_content: str,
    steers: List[SteerEntry],
) -> str:
    """Append drained mid-run steers so clarification steps see new user input."""
    if not steers:
        return issue_content
    block_lines = [
        "",
        "## Mid-run user comments (since workflow pause)",
        "The following issue comments arrived while the workflow was paused. "
        "Address them in this step:",
    ]
    for steer in steers:
        block_lines.append(
            f"- @{steer.author} ({steer.comment_id}): {_steer_body_for_llm(steer.body)}"
        )
    return issue_content.rstrip() + "\n" + "\n".join(block_lines) + "\n"


def issue_update_should_clear_workflow_state(
    state: Dict[str, Any],
    stored_updated_at: str,
    current_updated_at: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    *,
    cwd: Path,
    clarification_step_numbers: Optional[Set[int]] = None,
) -> bool:
    """Return True when ``issue_updated_at`` drift should wipe cached workflow state.

    Preserves state when pending human steers exist (comment-only activity) or when
    the workflow is paused awaiting clarification responses.
    """
    if not stored_updated_at or not current_updated_at:
        return False
    if stored_updated_at == current_updated_at:
        return False

    scratch = _steer_state_slice(state)
    pending = drain_issue_steers(
        repo_owner, repo_name, issue_number, scratch, cwd=cwd
    )
    if pending:
        merge_steer_state(scratch, state)
        return False

    if clarification_step_numbers and workflow_awaiting_clarification(
        state, clarification_step_numbers
    ):
        return False

    return True


def apply_clarification_steers_on_resume(
    issue_content: str,
    state: Dict[str, Any],
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    clarification_step_numbers: Set[int],
    *,
    cwd: Path,
    quiet: bool = False,
) -> str:
    """Merge newly drained steers into *issue_content* when resuming clarification."""
    if not workflow_awaiting_clarification(state, clarification_step_numbers):
        return issue_content
    steers = drain_issue_steers(
        repo_owner, repo_name, issue_number, state, cwd=cwd
    )
    if not steers:
        return issue_content
    if not quiet:
        preview = ", ".join(f"@{s.author}" for s in steers[:3])
        suffix = f" (+{len(steers) - 3} more)" if len(steers) > 3 else ""
        console.print(
            f"[cyan]Resuming clarification with new feedback from {preview}{suffix}[/cyan]"
        )
    return merge_steers_into_issue_content(issue_content, steers)


def _steer_state_slice(state: Dict[str, Any]) -> Dict[str, Any]:
    return {key: state[key] for key in STEER_STATE_KEYS if key in state}


def append_agentic_progress_steer_note(count: int, preview: str) -> None:
    """Attach pending-steer metadata to the current interrupt/progress context."""
    global _agentic_interrupt_context
    if _agentic_interrupt_context is None:
        _agentic_interrupt_context = {}
    _agentic_interrupt_context["pending_steers"] = count
    _agentic_interrupt_context["steer_preview"] = preview


def peek_agentic_progress_steer_metadata() -> Dict[str, Any]:
    """Return pending-steer fields from interrupt context without clearing it."""
    global _agentic_interrupt_context
    if not _agentic_interrupt_context:
        return {}
    meta: Dict[str, Any] = {}
    if "pending_steers" in _agentic_interrupt_context:
        meta["pending_steers"] = _agentic_interrupt_context["pending_steers"]
    if "steer_preview" in _agentic_interrupt_context:
        meta["steer_preview"] = _agentic_interrupt_context["steer_preview"]
    return meta


def detect_control_token(
    output: Optional[str],
    token: str,
    tail_lines: int = _SEMANTIC_TAIL_LINES,
) -> Optional[TokenMatch]:
    """Detect a control token in LLM output with three-tier fallback.

    Tier 1: Exact substring match (fastest, most reliable) — full output.
    Tier 2: Case-insensitive substring match — full output.
    Tier 3: Semantic regex patterns for common LLM paraphrases — tail only.

    Restricting tier 3 to the tail prevents false positives when LLMs
    quote or discuss a status in the middle of analysis without declaring it.

    Args:
        output: The raw LLM step output text.
        token: The control token to detect (e.g., 'ALL_TESTS_PASS').
        tail_lines: Number of lines from the end to scan for semantic patterns.

    Returns:
        TokenMatch if detected (truthy), None if not (falsy).
    """
    if not output:
        return None

    # Tier 1: exact match (full output)
    if token in output:
        return TokenMatch(tier="exact", token=token)

    # Tier 2: case-insensitive (full output)
    output_upper = output.upper()
    if token.upper() in output_upper:
        return TokenMatch(tier="case_insensitive", token=token)

    # Tier 3: semantic regex fallback (tail only for long outputs)
    patterns = SEMANTIC_PATTERNS.get(token, [])
    if patterns:
        lines = output.splitlines()
        if len(lines) > tail_lines:
            tail_text = '\n'.join(lines[-tail_lines:])
        else:
            tail_text = output
        for pattern in patterns:
            if re.search(pattern, tail_text, re.IGNORECASE):
                return TokenMatch(tier="semantic", token=token, pattern=pattern)

    return None


def classify_step_output(
    output: str,
    expected_tokens: List[str],
    model: str = "gemini/gemini-3-flash",
) -> Optional[TokenMatch]:
    """Classify step output via LLM when regex-based detection fails.

    Makes a single cheap API call with structured output to classify
    the step output into one of the expected control tokens.
    Only call this as a tier-4 fallback after detect_control_token returns None.

    Args:
        output: The raw step output text.
        expected_tokens: List of valid tokens (e.g., ["ALL_TESTS_PASS", "CONTINUE_CYCLE"]).
        model: LiteLLM model identifier for classification.

    Returns:
        TokenMatch when classified to a known token.
        None when the classifier confidently returns NONE.
        TokenMatch(token="CLASSIFICATION_ERROR") when classification fails
        (timeout/rate-limit/provider error/parse failure), allowing callers to
        distinguish "no token" from "classifier unavailable".
    """
    try:
        from pdd.llm_invoke import llm_invoke
    except ImportError:
        return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")

    token_list = ", ".join(expected_tokens)
    prompt = (
        "Classify the following step output into exactly one of these statuses: "
        "{token_list}, or NONE if none apply.\n\n"
        "Step output (last 3000 chars):\n{step_output}\n\n"
        "Return a JSON object with status, confidence (0-1 float), and reasoning (brief string)."
    )

    schema = {
        "type": "object",
        "properties": {
            "status": {"type": "string", "enum": expected_tokens + ["NONE"]},
            "confidence": {"type": "number"},
            "reasoning": {"type": "string"},
        },
        "required": ["status", "confidence", "reasoning"],
    }

    try:
        result = llm_invoke(
            prompt=prompt,
            input_json={"token_list": token_list, "step_output": output[-3000:]},
            output_schema=schema,
            strength=0.0,
            temperature=0.0,
        )
        # llm_invoke returns content in "result" key, not "output"
        raw = result.get("result") or result.get("output", "")
        parsed = json.loads(raw) if isinstance(raw, str) else raw
        if not parsed:
            return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")
        status = parsed.get("status", "NONE")
        if status == "NONE" or status not in expected_tokens:
            return None
        cost = result.get("cost")
        return TokenMatch(tier="llm_classification", token=status, cost=cost)
    except Exception:
        return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")


def substitute_template_variables(
    template: Any,
    context: Dict[str, Any],
    *,
    strict_unresolved: bool = False,
) -> str:
    """Safely substitute known {placeholders} without raising on unknown keys.

    This intentionally uses iterative ``str.replace`` instead of ``str.format``
    so unknown placeholders remain intact and context values containing braces
    (e.g. JSON) are preserved verbatim.
    """
    # Compatibility path for tests/mocks that provide template objects with a
    # .format(**context) method rather than a raw string prompt.
    if not isinstance(template, str) and hasattr(template, "format") and callable(template.format):
        return str(template.format(**context))

    if strict_unresolved:
        for match in re.finditer(r"(?<![{])[{]([A-Za-z_][A-Za-z0-9_]*)[}](?![}])", template):
            key = match.group(1)
            if key not in context:
                raise KeyError(key)

    rendered = template
    for key, value in context.items():
        rendered = rendered.replace("{" + str(key) + "}", str(value))

    return rendered


def get_agent_provider_preference() -> List[str]:
    """Return provider preference order, overridable via PDD_AGENTIC_PROVIDER env var.

    Examples:
        PDD_AGENTIC_PROVIDER=google,anthropic,openai  ->  ["google", "anthropic", "openai"]
        PDD_AGENTIC_PROVIDER=google                    ->  ["google"]
        (unset)                                        ->  ["anthropic", "google", "openai"]
    """
    env_val = os.environ.get("PDD_AGENTIC_PROVIDER", "")
    if env_val:
        prefs = [p.strip() for p in env_val.split(",") if p.strip()]
        normalized = []
        for p in prefs:
            if p == "antigravity":
                normalized.append("google")
                # `PDD_AGENTIC_PROVIDER=antigravity` is an explicit pin to `agy`.
                # Overwrite any prior `PDD_GOOGLE_CLI` (including a stale
                # `gemini` rollback value) so the more-specific selector wins.
                os.environ["PDD_GOOGLE_CLI"] = "agy"
            else:
                normalized.append(p)
        # Deduplicate while preserving order
        result = []
        for p in normalized:
            if p not in result:
                result.append(p)
        return result
    return list(_DEFAULT_PROVIDER_PREFERENCE)

# CLI command mapping for each provider
CLI_COMMANDS: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
    "opencode": "opencode",
}

# Common installation paths for CLI tools (platform-specific)
# Used as fallback when shutil.which() fails to find the binary
_COMMON_CLI_PATHS: Dict[str, List[Path]] = {
    "claude": [
        Path.home() / ".npm-global" / "bin" / "claude",
        Path.home() / ".local" / "bin" / "claude",
        Path.home() / "bin" / "claude",
        Path("/usr/local/bin/claude"),
        Path("/opt/homebrew/bin/claude"),
        Path("/home/linuxbrew/.linuxbrew/bin/claude"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "codex": [
        Path.home() / ".npm-global" / "bin" / "codex",
        Path.home() / ".local" / "bin" / "codex",
        Path.home() / "bin" / "codex",
        Path("/usr/local/bin/codex"),
        Path("/opt/homebrew/bin/codex"),
        Path("/home/linuxbrew/.linuxbrew/bin/codex"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "gemini": [
        Path.home() / ".npm-global" / "bin" / "gemini",
        Path.home() / ".local" / "bin" / "gemini",
        Path.home() / "bin" / "gemini",
        Path("/usr/local/bin/gemini"),
        Path("/opt/homebrew/bin/gemini"),
        Path("/home/linuxbrew/.linuxbrew/bin/gemini"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "agy": [
        Path.home() / ".npm-global" / "bin" / "agy",
        Path.home() / ".local" / "bin" / "agy",
        Path.home() / "bin" / "agy",
        Path("/usr/local/bin/agy"),
        Path("/opt/homebrew/bin/agy"),
        Path("/home/linuxbrew/.linuxbrew/bin/agy"),
        Path.home() / ".antigravity" / "bin" / "agy",
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "opencode": [
        Path.home() / ".npm-global" / "bin" / "opencode",
        Path.home() / ".local" / "bin" / "opencode",
        Path.home() / "bin" / "opencode",
        Path("/usr/local/bin/opencode"),
        Path("/opt/homebrew/bin/opencode"),
        Path("/home/linuxbrew/.linuxbrew/bin/opencode"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
}

# Maximum depth to search for .pddrc file
MAX_PDDRC_SEARCH_DEPTH: int = 10

DEFAULT_TIMEOUT_SECONDS: float = 600.0  # Increased from 240s; Claude needs time for complex verify tasks
MIN_VALID_OUTPUT_LENGTH: int = 50
DEFAULT_MAX_RETRIES: int = 3
DEFAULT_RETRY_DELAY: float = 5.0
MAX_RETRY_DELAY: float = 120.0
MAX_PATH_DISPLAY_LENGTH: int = 200  # Truncation length for PATH in diagnostic messages
MAX_ERROR_SNIPPET_LENGTH: int = 2000  # Truncation length for provider error messages (Issue #492)
CLAUDE_CODE_MODE_ENV: str = "PDD_CLAUDE_CODE_MODE"
CLAUDE_CODE_INTERACTIVE_MODE: str = "interactive"
# Issue #1365: interactive Claude post-launch auth fast-fail. A revoked or
# logged-out interactive session surfaces a *synthetic* authentication-failure
# turn in its --session-id transcript within ~1-4s, then leaves the TUI parked
# at the prompt forever — burning the full step timeout per dead credential in
# the cloud OAuth waterfall. The grace window lets a healthy session start a
# real turn before the first transcript check (a healthy turn never writes a
# synthetic auth row); the interval throttles those checks inside the PTY loop.
INTERACTIVE_AUTH_FASTFAIL_GRACE_SECONDS: float = 2.0
INTERACTIVE_AUTH_FASTFAIL_INTERVAL_SECONDS: float = 1.0
# The model name Claude Code stamps on a turn it generated locally for a failed
# API call (auth failure, usage cap, transient error) rather than from a model.
CLAUDE_SYNTHETIC_MODEL: str = "<synthetic>"
# Issue #1232: max newlines allowed in a leading-"Error:" provider error response.
# Genuine terse provider errors have 0-2 newlines (single status line, or
# "Error: ...\nDetails: ..."). Multi-paragraph findings docs have many more
# newlines — this gate prevents demoting substantive docs that happen to start
# with "Error:" while preserving the long-single-line error case from #902.
MAX_ERROR_RESPONSE_NEWLINES: int = 3


def _is_rate_limited(error_message: str) -> bool:
    """Detect transient rate-limit errors that need extended backoff.

    Provider 429s clear in seconds-to-minutes; the default exponential
    backoff (1s → 2s → 4s) burns the retry budget before the rate limit
    window opens. When this returns True, the caller should pick a
    longer floor (e.g. 60s) for the next sleep.

    Background: in the May 5 agentic split run on solving_orchestrator.py,
    3 of 12 child extractions ended in ``api_error_status: 429`` after
    DEFAULT_MAX_RETRIES (3) attempts under standard backoff — children
    that would have succeeded with one or two longer waits were marked
    as terminal failures and never retried.
    """
    msg = error_message.lower()
    rate_limit_patterns = [
        r'"api_error_status"\s*:\s*429',
        r"\b429\b",
        r"rate[\s_-]?limit",
        r"too\s+many\s+requests",
        r"requests\s+per\s+minute",
        r"rate\s+exceeded",
    ]
    return any(re.search(p, msg) for p in rate_limit_patterns)


# Floor for the next sleep when the previous attempt hit a 429. Long enough
# that token-window-based limits (per-minute) have a chance to clear, short
# enough that a deadline-bounded run still attempts another shot.
RATE_LIMIT_BACKOFF_FLOOR: float = 60.0


_PERMANENT_ERROR_CLASSES: Tuple[Tuple[str, Tuple[str, ...]], ...] = (
    # (classification, regex patterns) — order matters; first match wins.
    (
        "auth",
        (
            r"authentication[_\s]error",
            r"authentication\s+failed",
            r"failed\s+to\s+authenticate",
            r"invalid\s+bearer",
            r"invalid\s+api\s+key",
            r"invalid\s+key",
            r"\b401\b",
            r"access\s+denied",
            r"permission\s+denied",
        ),
    ),
    (
        "invalid-parameter",
        (
            r"invalid\s+parameter",
            r"invalid.*temperature|temperature.*(?:not supported|out of range)",
            r"not\s+supported\s+for\s+this\s+model",
            # Negative lookahead so OpenCode "model not found in provider"
            # misconfigurations classify as `provider-config` (their dedicated
            # class lower in this table), not as a bare invalid-parameter.
            r"model\s+not\s+found(?!\s+in\s+provider)",
        ),
    ),
    (
        # Claude Code subscription-tier caps. Covers the weekly/overall limit
        # ("You've hit your limit · resets [TIME]") AND the 5-hour session limit
        # and the usage limit ("You've hit your session/usage limit · resets
        # [TIME]") — all are hours-to-days resets where retrying the same token
        # is futile. Distinct from API-tier 429 because the reset window is
        # hours-to-days, not seconds-to-minutes — retrying on the 60s rate-limit
        # floor wastes minutes. Stable token `credential-limit` lets pdd_cloud's
        # OAuth-token waterfall detect this and rotate to a different credential
        # instead of retrying the dead one.
        "credential-limit",
        (
            # Proximity + time-token guard. Requires "hit your [session/usage/
            # weekly/monthly] limit" and "resets" within 40 chars (typical
            # envelope is "... limit · resets May 18, 11pm (UTC) ...") AND
            # requires a time-token OR delimiter immediately after "resets" so
            # distant prose like "if you hit your limit, nothing resets
            # automatically" does NOT classify as credential-limit. Without the
            # time token, any sentence stringing both phrases together would
            # short-circuit the rate-limit retry path on benign text.
            r"hit\s+your\s+(?:session\s+|usage\s+|weekly\s+|monthly\s+)?limit[^\n]{0,40}?\bresets?\b\s*(?:[·:|\-]|in\s|at\s|on\s|\d|jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)",
        ),
    ),
    (
        # Issue #1072: quota exhaustion (permanent even when 429 is present)
        "quota",
        (
            r"quota\s+(exhausted|exceeded)",
            r"daily\s+quota",
            r"terminal\s*quota\s*error",
        ),
    ),
    (
        # Issue #814: Anthropic billing / credit-exhaustion 400 bodies
        "billing/credit-exhaustion",
        (
            r"credit\s+balance\s+is\s+too\s+low",
            r"insufficient\s+(credit|balance|funds)",
        ),
    ),
    (
        # Issue #1232: Anthropic CLI OAuth/login failures on cloud workers
        "oauth/login",
        (
            r"not\s+logged\s+in",
            r"please\s+run\s+/login",
        ),
    ),
    (
        # OpenCode-specific misconfigurations that cannot heal without user action
        "provider-config",
        (
            r"provider\s+not\s+configured",
            r"no\s+provider\s+configured",
            r"model\s+not\s+found\s+in\s+provider",
            r"run\s+`?opencode\s+auth\s+login`?",
            r"opencode\s+auth\s+login",
            r"configure\s+(a\s+|the\s+)?provider",
        ),
    ),
)

# Issue #814 weak billing-page hint. Runs only after the strong classes above
# AND the rate-limit short-circuit so a transient 429 mentioning
# "Plans & Billing" stays transient.
_PERMANENT_ERROR_WEAK_BILLING_PATTERN: str = r"plans\s*&\s*billing"


def _classify_permanent_error(error_message: str) -> Optional[str]:
    """Return a stable classification token for a permanent error, or None.

    Classification runs in three tiers so a body that incidentally carries
    rate-limit phrasing cannot mask a genuinely permanent failure:

    1. Strong-permanent classes (auth / invalid-parameter / quota /
       billing/credit-exhaustion / oauth/login / provider-config) win
       first. A "401 … see rate-limit docs" body still classifies as
       permanent so the orchestrator falls through to the next provider
       instead of sleeping on the 60s rate-limit floor (Issue #1072,
       Issue #814).
    2. Rate-limit short-circuit: if step 1 did not match and
       `_is_rate_limited` is True, the error is transient (returns
       ``None``) so a generic HTTP 429 that just points the user at
       "Plans & Billing" keeps its standard retry/backoff treatment.
    3. Weak-permanent hint: a bare "Plans & Billing" mention without any
       of the stronger patterns above is still classified as
       billing/credit-exhaustion so Anthropic billing pages without an
       accompanying 429 status are not retried (Issue #814).
    """
    msg = error_message.lower()
    for classification, patterns in _PERMANENT_ERROR_CLASSES:
        if any(re.search(pattern, msg) for pattern in patterns):
            return classification
    if _is_rate_limited(error_message):
        return None
    if re.search(_PERMANENT_ERROR_WEAK_BILLING_PATTERN, msg):
        return "billing/credit-exhaustion"
    return None


def _is_permanent_error(error_message: str) -> bool:
    """Backward-compatible wrapper around `_classify_permanent_error`."""
    return _classify_permanent_error(error_message) is not None


# ---------------------------------------------------------------------------
# Issue #1541: secret-safe provider-limit marker for PDD Cloud retry scheduling
# ---------------------------------------------------------------------------
# PDD Cloud needs to queue an agentic executor run when the active credential
# hits a rate/usage/credential limit, then resume after the provider reset
# window. It cannot reliably extract a reset time by scraping raw provider
# stderr (brittle, provider-specific, and risks leaking secrets the provider
# echoes back in an error body). Instead the CLI emits exactly one stable,
# machine-parseable line per provider-limit event:
#
#   PDD_PROVIDER_LIMIT provider=<anthropic|openai|google|antigravity|opencode>
#       status=<429|credential_limit>
#       reason=<rate_limit|usage_limit|session_limit|credential_limit>
#       reset_at=<UTC ISO-8601 'YYYY-MM-DDTHH:MM:SSZ' or empty>
#       reset_source=<provider|parsed_text|estimated|none>
#
# The marker is ADDITIVE — it piggybacks on the already-vetted
# `_classify_permanent_error` ("credential-limit") and `_is_rate_limited`
# classifications, so it inherits their false-positive guards and never changes
# retry/backoff semantics. It only ever emits fixed enum fields plus a
# normalized UTC timestamp, never a slice of the (untrusted) provider text.

PDD_PROVIDER_LIMIT_MARKER: str = "PDD_PROVIDER_LIMIT"
_provider_limit_logger = logging.getLogger(__name__ + ".provider_limit")

# Allowed enum values. Anything outside these is coerced to a conservative
# default by the formatter so a classifier bug can never widen the marker into
# untrusted territory.
_MARKER_PROVIDERS: frozenset = frozenset(
    {"anthropic", "openai", "google", "antigravity", "opencode"}
)
_MARKER_STATUSES: frozenset = frozenset({"429", "credential_limit"})
_MARKER_REASONS: frozenset = frozenset(
    {"rate_limit", "usage_limit", "session_limit", "credential_limit"}
)
_MARKER_SOURCES: frozenset = frozenset(
    {"provider", "parsed_text", "estimated", "none"}
)

_MONTHS: Dict[str, int] = {
    name.lower(): num
    for num, name in enumerate(
        ["Jan", "Feb", "Mar", "Apr", "May", "Jun",
         "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"],
        start=1,
    )
}

# Normalized UTC reset timestamp shape used both to format and to validate.
_RESET_AT_RE = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")

# Reset-clause matchers. Each is anchored on the `resets` keyword and reads ONLY
# structured groups (never the surrounding free text). A short bounded gap
# (`[^\n]{0,12}?`) absorbs the typical "· " / "at " / "on " delimiter between
# the anchor and the time token. Tried most-specific first.
_RESET_ISO_RE = re.compile(
    r"resets?\b[^\n]{0,12}?"
    r"(?P<iso>\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}(?::\d{2})?(?:\.\d+)?"
    r"(?:Z|[+-]\d{2}:?\d{2})?)",
    re.IGNORECASE,
)
# Optional trailing timezone, tried after the time. `tz` is a parenthesized
# token ("(UTC)", "(America/Los_Angeles)"); `tzbare` is an *unparenthesized*
# zone, captured in two structurally-anchored shapes so it catches real zone
# tokens without swallowing ordinary trailing prose:
#   * an IANA "Area/Location" name ("America/Los_Angeles") anchored on the closed
#     set of IANA area prefixes — the required area + "/" can't match prose like
#     "and/or"; tried first so "US/Pacific" is not truncated to the "US" abbrev;
#   * an UPPERCASE abbreviation or numeric offset ("PST", "UTC-08:00"), matched
#     case-sensitively so a lowercase word like "today" is left alone.
# Every token (parenthesized OR bare) is routed through `_resolve_reset_tz`, so
# an unrecognized zone degrades to unparseable instead of being silently read as
# UTC. The uppercase-only bound on the abbreviation branch is deliberate: it
# treats an all-caps non-zone word as a possible unknown zone (-> unparseable)
# rather than emit a confidently-wrong UTC timestamp.
_TZ_TAIL = (
    r"(?:\s*\((?P<tz>[^)\n]{1,40})\)"
    r"|\s+(?P<tzbare>"
    r"(?:Africa|America|Antarctica|Arctic|Asia|Atlantic|Australia|Brazil|Canada"
    r"|Chile|Europe|Indian|Mexico|Pacific|US|Etc)/[\w+/-]+"
    r"|(?-i:[A-Z]{2,5}(?:[+-]\d{1,2}(?::?\d{2})?)?|[+-]\d{2}:?\d{2})"
    r"))?"
)
# `ampm` accepts plain and dotted forms (am, pm, a.m., p.m.). The date matcher
# also accepts an explicit 4-digit `year` and an optional "at" connector between
# the day and the time, so "June 11, 2026, 3:30pm" is not misread as hour=20 and
# "June 11 at 3:30pm" is not dropped as unparseable.
_RESET_DATE_RE = re.compile(
    r"resets?\b[^\n]{0,12}?"
    r"(?P<month>jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?\s+"
    r"(?P<day>\d{1,2})(?:,)?\s+"
    r"(?:(?P<year>\d{4})(?:,)?\s+)?"
    r"(?:at\s+)?"
    r"(?P<hour>\d{1,2})(?::(?P<minute>\d{2}))?\s*(?P<ampm>[ap]\.?m\.?)?"
    + _TZ_TAIL,
    re.IGNORECASE,
)
_RESET_TIME_RE = re.compile(
    r"resets?\b(?P<gap>[^\n]{0,12}?)"
    r"(?P<hour>\d{1,2})(?::(?P<minute>\d{2}))?\s*(?P<ampm>[ap]\.?m\.?)?"
    + _TZ_TAIL,
    re.IGNORECASE,
)

# A relative-countdown preposition in the gap before a time-only token marks a
# duration ("resets in 00:30", "try again within 5:00"), NOT an absolute clock
# time — those must not yield a reset_at.
_RELATIVE_RESET_GAP_RE = re.compile(r"\b(?:in|after|within|every)\b", re.IGNORECASE)
# Explicit numeric UTC/GMT offset, e.g. "UTC+02:00", "GMT-5", "+0530".
_TZ_OFFSET_RE = re.compile(r"^(?:UTC|GMT)?\s*([+-])(\d{1,2})(?::?(\d{2}))?$", re.IGNORECASE)


def _format_utc(dt: datetime) -> str:
    """Render a timezone-aware datetime as compact UTC ISO ``YYYY-MM-DDTHH:MM:SSZ``."""
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _resolve_reset_tz(name: Optional[str]) -> Optional[tzinfo]:
    """Resolve a parenthesized timezone token to a ``tzinfo``.

    Returns ``timezone.utc`` when no timezone was given (the conservative,
    documented default for unzoned reset text), a resolved zone for ``UTC``/
    ``GMT``/``Z``, an explicit numeric offset (``UTC+02:00``, ``GMT-5``), or a
    recognized IANA name (e.g. ``America/Los_Angeles``), and ``None`` when an
    *explicit* timezone token is present but unrecognized (``PDT``, ``Pacific
    Time``) — the caller then treats the reset as unparseable rather than
    emitting a confidently-wrong UTC timestamp.
    """
    if not name:
        return timezone.utc
    cleaned = name.strip()
    if cleaned.upper() in ("UTC", "GMT", "Z", "UT"):
        return timezone.utc
    offset = _TZ_OFFSET_RE.match(cleaned)
    if offset:
        sign = -1 if offset.group(1) == "-" else 1
        hours = int(offset.group(2))
        minutes = int(offset.group(3) or 0)
        if hours > 23 or minutes > 59:
            return None
        return timezone(sign * timedelta(hours=hours, minutes=minutes))
    try:
        return ZoneInfo(cleaned)
    except Exception:
        return None


def _reset_hour_to_24h(hour: int, ampm: Optional[str]) -> Optional[int]:
    """Convert a parsed clock hour (12h with am/pm, or 24h) to 0-23, or None.

    ``ampm`` may be a dotted form (``a.m.``/``p.m.``); dots are normalized away.
    """
    if ampm:
        marker = ampm.replace(".", "").lower()
        if not 1 <= hour <= 12:
            return None
        if marker == "am":
            return 0 if hour == 12 else hour
        return 12 if hour == 12 else hour + 12
    return hour if 0 <= hour <= 23 else None


def _iso_reset_to_utc(raw: str) -> Optional[datetime]:
    """Parse an explicit ISO-8601 reset timestamp to an aware UTC datetime."""
    candidate = raw.strip().replace(" ", "T")
    if candidate.endswith("Z"):
        candidate = candidate[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(candidate)
    except ValueError:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


def _match_tz(match: "re.Match[str]") -> Optional[str]:
    """Return the timezone token from a reset match, preferring a parenthesized
    token (``tz``) and falling back to a bare trailing abbreviation/offset
    (``tzbare``) so an unparenthesized zone like ``11pm PST`` is not silently
    dropped and read as UTC."""
    groups = match.groupdict()
    return groups.get("tz") or groups.get("tzbare")


def _dated_reset_to_datetime(match: "re.Match[str]", now: datetime) -> Optional[datetime]:
    """Build a reset datetime from a month/day/time match.

    An explicit 4-digit year, when captured, is honored verbatim — even if it
    lies in the past (the provider stated it, so a past reset reads as "retry
    now"). Otherwise the year is inferred as the next future occurrence (a date
    already past this year rolls forward)."""
    month = _MONTHS.get(match.group("month").lower()[:3])
    hour = _reset_hour_to_24h(int(match.group("hour")), match.group("ampm"))
    minute = int(match.group("minute") or 0)
    day = int(match.group("day"))
    if month is None or hour is None or not 1 <= day <= 31 or not 0 <= minute <= 59:
        return None
    tz = _resolve_reset_tz(_match_tz(match))
    if tz is None:  # explicit but unrecognized timezone -> unparseable
        return None
    year_token = match.groupdict().get("year")
    if year_token:
        try:
            return datetime(int(year_token), month, day, hour, minute, tzinfo=tz)
        except ValueError:
            return None
    # Anchor year inference to the reset *timezone's* local year, not the UTC
    # year: near a New Year boundary `now` can already be in the next year in
    # UTC while still in the previous year in the reset zone (or vice versa), so
    # using `now.year` would skip the correct candidate and land a full year off
    # (e.g. "resets Dec 31, 11:45pm (America/Los_Angeles)" at 2026-01-01T07:30Z).
    base_year = now.astimezone(tz).year
    for year in (base_year, base_year + 1):
        try:
            local = datetime(year, month, day, hour, minute, tzinfo=tz)
        except ValueError:
            return None
        if local.astimezone(timezone.utc) >= now:
            return local
    return None


def _time_only_reset_to_datetime(match: "re.Match[str]", now: datetime) -> Optional[datetime]:
    """Build a reset datetime from a time-of-day match against ``now``'s date,
    rolling to the next day when the time has already passed."""
    hour = _reset_hour_to_24h(int(match.group("hour")), match.group("ampm"))
    minute = int(match.group("minute") or 0)
    if hour is None or not 0 <= minute <= 59:
        return None
    tz = _resolve_reset_tz(_match_tz(match))
    if tz is None:  # explicit but unrecognized timezone -> unparseable
        return None
    local_now = now.astimezone(tz)
    candidate = local_now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if candidate.astimezone(timezone.utc) < now:
        candidate = candidate + timedelta(days=1)
    return candidate


def _parse_reset_at(
    text: Optional[str], *, now: Optional[datetime] = None
) -> Tuple[str, str]:
    """Parse a provider reset time out of sanitized limit text.

    Returns ``(reset_at, reset_source)`` where ``reset_at`` is a normalized UTC
    ISO-8601 string ``YYYY-MM-DDTHH:MM:SSZ`` (or ``""`` when no reset time can be
    read) and ``reset_source`` is one of:

    * ``parsed_text`` — an explicit date or full timestamp was read from text,
    * ``estimated`` — only a time-of-day was given, so the date was inferred,
    * ``none`` — nothing parseable.

    Only recognized date/time tokens are ever read out of ``text``; the
    surrounding free text is never echoed, so the result is safe to emit even
    when the input carries untrusted provider output. Unzoned times are
    interpreted as UTC (a conservative, documented default). ``now`` is
    injectable for deterministic tests and defaults to the current UTC time.
    """
    if not text:
        return "", "none"
    if now is None:
        now = datetime.now(timezone.utc)
    elif now.tzinfo is None:
        now = now.replace(tzinfo=timezone.utc)

    # 1) Explicit ISO-8601 timestamp (carries its own date; honored verbatim).
    match = _RESET_ISO_RE.search(text)
    if match:
        dt = _iso_reset_to_utc(match.group("iso"))
        if dt is not None:
            return _format_utc(dt), "parsed_text"

    # 2) Month-name date + time (year inferred -> next future occurrence).
    match = _RESET_DATE_RE.search(text)
    if match:
        dt = _dated_reset_to_datetime(match, now)
        if dt is not None:
            return _format_utc(dt), "parsed_text"

    # 3) Time-of-day only (date inferred -> next future occurrence; estimated).
    #    Require an am/pm marker OR an explicit minute so a bare "resets 11"
    #    cannot parse as an ambiguous time, and reject relative countdowns
    #    ("resets in 00:30") whose HH:MM looks like a clock time but is a
    #    duration.
    match = _RESET_TIME_RE.search(text)
    if (
        match
        and (match.group("ampm") or match.group("minute"))
        and not _RELATIVE_RESET_GAP_RE.search(match.group("gap"))
    ):
        dt = _time_only_reset_to_datetime(match, now)
        if dt is not None:
            return _format_utc(dt), "estimated"

    return "", "none"


def _provider_limit_marker(
    *,
    provider: str,
    status: str,
    reason: str,
    reset_at: str = "",
    reset_source: str = "none",
) -> str:
    """Format the stable, secret-safe ``PDD_PROVIDER_LIMIT`` marker line.

    Every field is constrained to a fixed enum (or a normalized UTC timestamp
    for ``reset_at``); out-of-range inputs are coerced to conservative defaults
    so the marker can never carry untrusted text. An unmappable provider is
    reported as the literal ``unknown`` (a fixed token, never the raw string) —
    in practice unreachable because the emission seam always passes a known
    provider, but it keeps the marker safe if a future caller does not.
    """
    if provider not in _MARKER_PROVIDERS:
        provider = "unknown"
    if status not in _MARKER_STATUSES:
        status = "credential_limit"
    if reason not in _MARKER_REASONS:
        reason = "credential_limit"
    if reset_source not in _MARKER_SOURCES:
        reset_source = "none"
    if reset_at and not _RESET_AT_RE.fullmatch(reset_at):
        reset_at, reset_source = "", "none"
    return (
        f"{PDD_PROVIDER_LIMIT_MARKER} provider={provider} status={status} "
        f"reason={reason} reset_at={reset_at} reset_source={reset_source}"
    )


def _credential_limit_reason(error_message: str) -> str:
    """Map a Claude Code subscription-cap envelope to a marker ``reason``.

    ``session``/``usage`` map to their specific reasons; weekly/monthly/overall
    caps map to the overarching ``credential_limit``.
    """
    match = re.search(
        r"hit\s+your\s+(session|usage|weekly|monthly)?\s*limit",
        error_message,
        re.IGNORECASE,
    )
    subtype = (match.group(1) or "").lower() if match and match.group(1) else ""
    if subtype == "session":
        return "session_limit"
    if subtype == "usage":
        return "usage_limit"
    return "credential_limit"


def _classify_provider_limit(
    provider: str, error_message: Optional[str], *, now: Optional[datetime] = None
) -> Optional[str]:
    """Return the ``PDD_PROVIDER_LIMIT`` marker line for a real provider/
    credential limit, or ``None`` when the error is not a reset-able limit.

    Piggybacks on the existing vetted classification so it inherits the
    credential-limit false-positive guards and the generic-429 short-circuit:

    * ``credential-limit`` (Claude Code subscription/session/usage/weekly cap)
      -> ``status=credential_limit`` with a session/usage/credential reason and
      a parsed reset time when the envelope carries one.
    * generic transient 429 (no permanent classification) ->
      ``status=429 reason=rate_limit`` with no reset metadata.

    auth / quota / billing / oauth / provider-config permanent errors are NOT
    reset-able limits and return ``None`` (no scheduling marker).
    """
    if not error_message:
        return None
    permanent_class = _classify_permanent_error(error_message)
    if permanent_class == "credential-limit":
        reset_at, reset_source = _parse_reset_at(error_message, now=now)
        return _provider_limit_marker(
            provider=provider,
            status="credential_limit",
            reason=_credential_limit_reason(error_message),
            reset_at=reset_at,
            reset_source=reset_source,
        )
    if permanent_class is None and _is_rate_limited(error_message):
        # Generic transient 429: usually carries no reset metadata
        # (-> reset_at= reset_source=none), but capture it when the body does
        # expose a parseable reset (e.g. a Retry-After rendered as
        # "resets <ISO>") so cloud can schedule precisely instead of guessing.
        reset_at, reset_source = _parse_reset_at(error_message, now=now)
        return _provider_limit_marker(
            provider=provider,
            status="429",
            reason="rate_limit",
            reset_at=reset_at,
            reset_source=reset_source,
        )
    return None


def _marker_provider_label(
    provider: str, env: Optional[Dict[str, str]] = None
) -> str:
    """Map an internal provider name to its marker ``provider=`` value.

    ``antigravity`` is collapsed to ``google`` everywhere in the agentic
    preference list, so the marker re-derives the ``antigravity`` label when the
    selected Google CLI is ``agy`` (vs. legacy ``gemini``) — otherwise the
    issue's ``antigravity`` enum value would never appear.
    """
    if provider == "google" and _get_google_cli_name(env) == "agy":
        return "antigravity"
    return provider


def _emit_provider_limit_marker(
    provider: str, error_message: Optional[str], *, env: Optional[Dict[str, str]] = None
) -> Optional[str]:
    """Emit the ``PDD_PROVIDER_LIMIT`` marker for ``error_message`` if it is a
    real provider/credential limit; return the marker line (or ``None``).

    Printed on plain stdout — deliberately unstyled and NOT quiet-gated — so the
    cloud scheduler can parse it even when human diagnostics are suppressed.

    Best-effort telemetry: any failure while building/printing the marker is
    swallowed so a marker bug can never break the agentic run it annotates.
    """
    try:
        marker = _classify_provider_limit(
            _marker_provider_label(provider, env), error_message
        )
        if marker is not None:
            print(marker, flush=True)
        return marker
    except Exception as exc:  # pragma: no cover - defensive: marker must never crash the run
        _provider_limit_logger.debug(
            "Provider-limit marker emission failed for %s: %s", provider, exc
        )
        return None


def _codex_auth_failure_message(error_detail: str) -> Optional[str]:
    """Return a concise user-facing message for stale Codex CLI auth."""
    msg = error_detail.lower()
    auth_patterns = [
        "access token could not be refreshed",
        "please sign in again",
        "codex/responses",
        "chatgpt.com/backend-api/codex",
    ]
    if not any(pattern in msg for pattern in auth_patterns):
        return None
    if "401" not in msg and "unauthorized" not in msg and "sign in" not in msg:
        return None

    return (
        "Codex CLI authentication failed: the stored ChatGPT/Codex login token "
        "could not be refreshed. Run `codex login` (or `codex login --device-auth`; "
        "use `codex login --with-api-key` for API-key auth) and retry. "
        "To avoid Codex for this run, set `PDD_AGENTIC_PROVIDER=anthropic,google`. "
        "Other ways to disable Codex auto-detection: unset `PDD_CODEX_AUTH_AVAILABLE` "
        "(if set in env), or run `codex logout` / remove `~/.codex/auth.json` "
        "(picked up by `_has_codex_auth_file` since Issue #813 round-6)."
    )


def _extract_codex_jsonl_error(stdout: str) -> str:
    """Extract the most useful error message from Codex JSON/JSONL stdout."""
    if not stdout:
        return ""

    def _message_from_value(value: Any) -> str:
        if isinstance(value, str):
            return value.strip()
        if isinstance(value, dict):
            for key in ("message", "detail", "reason", "error", "output", "result"):
                msg = _message_from_value(value.get(key))
                if msg:
                    return msg
        if isinstance(value, list):
            for item in value:
                msg = _message_from_value(item)
                if msg:
                    return msg
        return ""

    def _message_from_event(event: Any) -> str:
        if not isinstance(event, dict):
            return ""

        event_type = str(event.get("type") or "").lower()
        has_error_signal = (
            "error" in event_type
            or "failed" in event_type
            or bool(event.get("is_error"))
            or "error" in event
        )
        if not has_error_signal:
            return ""

        for key in ("error", "message", "detail", "reason", "output", "result"):
            msg = _message_from_value(event.get(key))
            if msg:
                return msg
        return ""

    terminal_error = ""
    last_error = ""
    for raw_line in stdout.splitlines() or [stdout]:
        line = raw_line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        msg = _message_from_event(event)
        if msg:
            last_error = msg
            event_type = str(event.get("type") or "").lower() if isinstance(event, dict) else ""
            if event_type in {"turn.failed", "task.failed", "session.failed"}:
                terminal_error = msg
    return (terminal_error or last_error)[:MAX_ERROR_SNIPPET_LENGTH]


def _is_codex_stdin_notice(text: str) -> bool:
    return text.strip().startswith("Reading additional input from stdin")


# Interrupt context: set by agentic orchestrators so KeyboardInterrupt handling
# can report how far the workflow progressed (console + core dumps).
_agentic_interrupt_context: Optional[Dict[str, Any]] = None


def set_agentic_progress(
    workflow: str,
    current_step: int,
    total_steps: int,
    step_name: str,
    completed_steps: Optional[List[int]] = None,
) -> None:
    """Record current step progress for KeyboardInterrupt reporting and core dumps."""
    global _agentic_interrupt_context
    _agentic_interrupt_context = {
        "workflow": workflow,
        "current_step": current_step,
        "total_steps": total_steps,
        "step_name": step_name,
        "completed_steps": completed_steps or [],
    }


def clear_agentic_progress() -> None:
    """Clear progress context (call at start of workflow or on normal completion)."""
    global _agentic_interrupt_context
    _agentic_interrupt_context = None


def get_and_clear_agentic_interrupt_context() -> Optional[Dict[str, Any]]:
    """Return current progress and clear it (used by error handler on KeyboardInterrupt)."""
    global _agentic_interrupt_context
    ctx = _agentic_interrupt_context
    _agentic_interrupt_context = None
    return ctx


# Job deadline constants — prevent agentic retry loops from consuming the full job timeout
JOB_TIMEOUT_MARGIN_SECONDS: float = 120.0   # Reserve for cleanup/reporting after last attempt
MIN_ATTEMPT_TIMEOUT_SECONDS: float = 60.0   # Don't start an attempt if less than this remains

def get_job_deadline() -> Optional[float]:
    """Return the absolute Unix timestamp deadline from PDD_JOB_DEADLINE env var.

    Set by the server (jobs.py) when launching subprocess jobs so that
    the agentic retry loop can budget its attempts within the job timeout.

    Returns:
        Float deadline timestamp, or None if unset / invalid.
    """
    val = os.environ.get("PDD_JOB_DEADLINE")
    if val:
        try:
            return float(val)
        except (ValueError, TypeError):
            return None
    return None


# GitHub State Markers
GITHUB_STATE_MARKER_START = "<!-- PDD_WORKFLOW_STATE:"
GITHUB_STATE_MARKER_END = "-->"

@dataclass
class Pricing:
    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 1.0

# Pricing Configuration
# Gemini: Based on test expectations (Flash: $0.35/$1.05, Cached 50%)
GEMINI_PRICING_BY_FAMILY = {
    "flash": Pricing(0.35, 1.05, 0.5),
    "pro": Pricing(3.50, 10.50, 0.5), # Placeholder for Pro
}

# Codex: Based on test expectations ($1.50/$6.00, Cached 25%)
CODEX_PRICING = Pricing(1.50, 6.00, 0.25)

# Anthropic Claude: Token-based fallback pricing when total_cost_usd is unavailable
# Cache read is 90% discount, cache write is 25% premium over input
ANTHROPIC_PRICING_BY_FAMILY = {
    "opus": Pricing(15.0, 75.0, 0.1),       # Claude Opus 4
    "sonnet": Pricing(3.0, 15.0, 0.1),      # Claude Sonnet 4
    "haiku": Pricing(0.80, 4.0, 0.1),       # Claude Haiku 3.5
}

console = Console()


# ---------------------------------------------------------------------------
# Agentic Debug Logging
# ---------------------------------------------------------------------------

AGENTIC_LOG_DIR = ".pdd/agentic-logs"
_AGENTIC_SESSION_ID: Optional[str] = None


_PROVIDER_MODEL_ENV: Dict[str, str] = {
    "anthropic": "CLAUDE_MODEL",
    "google": "GEMINI_MODEL",
    "openai": "CODEX_MODEL",
    "opencode": "OPENCODE_MODEL",
}


def _get_provider_model(provider: str) -> Optional[str]:
    """Return the requested model for *provider* from its env var.

    Returns ``None`` when the env var is unset, empty, or the provider is
    unknown, signalling "provider default" in the audit log.
    """
    env_var = _PROVIDER_MODEL_ENV.get(provider)
    if not env_var:
        return None
    value = os.environ.get(env_var) or ""
    return value.strip() or None


def _log_agentic_interaction(
    label: str,
    prompt: str,
    response: str,
    cost: float,
    provider: str,
    success: bool,
    duration: float,
    cwd: Path,
    *,
    model: Optional[str] = None,
    false_positive: bool = False,
    include_bodies: bool = True,
) -> Optional[_PddOwnedLogWrite]:
    """
    Append one record per provider attempt to ``.pdd/agentic-logs/session_*.jsonl``.

    Issue #1376: every attempt (success, failure, false-positive) leaves a
    record so the log answers "which provider/model produced step N's output"
    without ``--verbose``. ``include_bodies=False`` writes a summary-only
    record (omits ``prompt``/``response``) to keep file size manageable when
    the same prompt repeats across many successful steps.

    Args:
        label: Step identifier (e.g., ``"step1"``).
        prompt: Full prompt text sent to the agent.
        response: Full response text from the agent.
        cost: Cost in USD for this interaction.
        provider: Provider name (``"anthropic"``, ``"google"``, ``"openai"``).
        success: Whether the run-level outcome was a success.
        duration: Duration in seconds.
        cwd: Working directory for the task.
        model: Requested model (e.g., ``"claude-opus-4-7"``) or ``None`` for
            "provider default".
        false_positive: True when the provider call returned but the PDD
            heuristic rejected the output (e.g., short ``"Done."`` reply).
            Pairs with ``success=False``.
        include_bodies: When True, include the full ``prompt`` and ``response``
            text. When False, omit them but keep ``prompt_length`` and
            ``response_length`` so downstream tooling can still gauge size.

    Returns:
        The PDD-owned log append metadata when the write succeeds, otherwise
        ``None``.
    """
    global _AGENTIC_SESSION_ID

    try:
        # Ensure log directory exists
        log_dir = Path(cwd) / AGENTIC_LOG_DIR
        log_dir.mkdir(parents=True, exist_ok=True)

        # Initialize session ID on first call (one file per workflow run)
        if _AGENTIC_SESSION_ID is None:
            _AGENTIC_SESSION_ID = datetime.now().strftime("%Y%m%d_%H%M%S")

        log_file = log_dir / f"session_{_AGENTIC_SESSION_ID}.jsonl"
        before_errors: List[str] = []
        before_signature = _filesystem_signature(log_file, before_errors)

        entry: Dict[str, Any] = {
            "timestamp": datetime.now().isoformat(),
            "label": label,
            "cwd": str(cwd),
            "provider": provider,
            "model": model,
            "success": success,
            "false_positive": false_positive,
            "cost_usd": cost,
            "duration_seconds": round(duration, 2),
            "prompt_length": len(prompt),
            "response_length": len(response),
        }
        if include_bodies:
            entry["prompt"] = prompt
            entry["response"] = response

        with open(log_file, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
        after_errors: List[str] = []
        after_signature = _filesystem_signature(log_file, after_errors)
        if before_errors or after_errors or after_signature == "missing":
            return None
        return _PddOwnedLogWrite(
            path=log_file,
            before_signature=before_signature,
            after_signature=after_signature,
        )
    except Exception:
        return None  # Don't break workflow for logging errors


# ---------------------------------------------------------------------------
# CLI Discovery (addresses GitHub issue #234: Claude not found during agentic fallback)
# ---------------------------------------------------------------------------


def _load_agentic_config() -> Dict[str, Any]:
    """
    Load agentic CLI configuration from .pddrc.

    Looks for an 'agentic' section in .pddrc with CLI path overrides:

        agentic:
          claude_path: /path/to/claude
          codex_path: /path/to/codex
          gemini_path: /path/to/gemini

    Returns empty dict if no config found.
    """
    import yaml

    # Search for .pddrc in current dir and parent dirs
    search_path = Path.cwd()
    pddrc_path: Optional[Path] = None
    for _ in range(MAX_PDDRC_SEARCH_DEPTH):
        candidate = search_path / ".pddrc"
        if candidate.is_file():
            pddrc_path = candidate
            break
        parent = search_path.parent
        if parent == search_path:
            break
        search_path = parent

    # Also check home directory
    if not pddrc_path:
        home_pddrc = Path.home() / ".pddrc"
        if home_pddrc.is_file():
            pddrc_path = home_pddrc

    if not pddrc_path:
        return {}

    try:
        with open(pddrc_path, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
        if isinstance(config, dict):
            return config.get("agentic", {}) or {}
    except Exception:
        pass

    return {}


def _find_cli_binary(name: str, config: Optional[Dict[str, Any]] = None) -> Optional[str]:
    """
    Find a CLI binary using multiple strategies.

    This function addresses a common issue where CLI tools like 'claude' are
    installed and runnable from the user's shell, but not found by shutil.which()
    when pdd runs. This happens because shell profiles (.bashrc, .zshrc) may add
    directories to PATH that aren't available in the pdd process environment.

    Strategies (in order):
        1. Check for explicit path override in .pddrc agentic config
        2. Try shutil.which() for standard PATH lookup
        3. Search common installation directories

    Args:
        name: CLI binary name (e.g., "claude", "codex", "gemini")
        config: Optional pre-loaded agentic config dict (avoids repeated file reads)

    Returns:
        Full path to the binary if found, None otherwise
    """
    # Strategy 1: Check .pddrc config override
    if config is None:
        config = _load_agentic_config()

    config_key = f"{name}_path"
    if config_key in config:
        custom_path = Path(config[config_key])
        if custom_path.exists() and os.access(custom_path, os.X_OK):
            return str(custom_path)

    # Strategy 2: Standard PATH lookup
    path_result = shutil.which(name)
    if path_result:
        return path_result

    # Strategy 3: Search common installation directories. Home-relative paths
    # are added at runtime because tests and embedding environments may patch
    # Path.home() after this module has already been imported.
    for path in _iter_common_cli_paths(name):
        # Handle nvm-style paths that need glob expansion
        # nvm installs to ~/.nvm/versions/node/vX.Y.Z/bin/
        if "nvm" in str(path) and path.name == "node":
            # Glob for all node versions and check for the CLI in each
            try:
                for version_dir in path.glob("*/bin"):
                    cli_path = version_dir / name
                    if cli_path.exists() and os.access(cli_path, os.X_OK):
                        return str(cli_path)
            except Exception:
                pass
        elif path.exists() and os.access(path, os.X_OK):
            return str(path)

    return None


def _iter_common_cli_paths(name: str) -> List[Path]:
    """Return common CLI paths, including runtime-expanded home paths.

    ``_COMMON_CLI_PATHS`` is intentionally kept as a mutable module-level table
    for tests and .pddrc-style overrides, but entries containing ``Path.home()``
    are evaluated when the module is imported. Add an equivalent runtime set so
    discovery still honors the current home directory.
    """
    paths = list(_COMMON_CLI_PATHS.get(name, []))
    if name in {"claude", "codex", "gemini", "opencode", "agy"}:
        home = Path.home()
        paths.extend([
            home / ".npm-global" / "bin" / name,
            home / ".local" / "bin" / name,
            home / "bin" / name,
            home / ".nvm" / "versions" / "node",
        ])
        if name == "agy":
            paths.append(home / ".antigravity" / "bin" / "agy")

    seen: set[str] = set()
    unique_paths: List[Path] = []
    for path in paths:
        key = str(path)
        if key in seen:
            continue
        seen.add(key)
        unique_paths.append(path)
    return unique_paths


def _get_cli_diagnostic_info(name: str) -> str:
    """
    Generate diagnostic information for CLI discovery failures.

    Returns a helpful message for troubleshooting when a CLI binary cannot be found.
    """
    lines = [
        f"CLI '{name}' not found. Troubleshooting steps:",
        "",
        f"1. Check installation: which {name}",
        f"2. Common installation paths searched:",
    ]

    for path in _iter_common_cli_paths(name):
        lines.append(f"   - {path}")

    lines.extend([
        "",
        "3. Configure custom path in .pddrc:",
        f"   agentic:",
        f"     {name}_path: /path/to/{name}",
        "",
        f"4. Current PATH: {os.environ.get('PATH', 'not set')[:MAX_PATH_DISPLAY_LENGTH]}...",
    ])

    return "\n".join(lines)


def _get_google_cli_binary(env: Optional[Dict[str, str]] = None) -> Optional[str]:
    """Resolve the Google provider CLI binary path based on PDD_GOOGLE_CLI and availability.

    Shares the same selection logic as ``_get_google_cli_name``; returns the
    filesystem path rather than the logical name.  The two functions MUST stay
    in sync so that availability detection and subprocess construction always
    agree on which binary is selected.

    Selection rules:
        - ``agy`` / ``gemini``: explicit pin (errors at run time if missing).
        - ``auto`` (default): use the same logical-name resolver as
          ``_get_google_cli_name`` so command construction and the launched
          executable cannot disagree.
    """
    if env is None:
        env = os.environ
    pref = env.get("PDD_GOOGLE_CLI", "auto").strip().lower()
    if pref == "agy":
        return _find_cli_binary("agy")
    if pref == "gemini":
        return _find_cli_binary("gemini")
    cli_name = _get_google_cli_name(env)
    return _find_cli_binary(cli_name) if cli_name else None


def _has_google_api_key_for_cli(cli: str, env: Optional[Dict[str, str]] = None) -> bool:
    """Return whether *env* has an API key usable by the selected Google CLI."""
    if env is None:
        env = os.environ
    if cli == "agy":
        return bool(
            env.get("ANTIGRAVITY_API_KEY")
            or env.get("GOOGLE_API_KEY")
            # Compatibility: PDD maps GEMINI_API_KEY to GOOGLE_API_KEY before
            # launching agy so existing Gemini-key users keep working.
            or env.get("GEMINI_API_KEY")
        )
    if cli == "gemini":
        return bool(env.get("GEMINI_API_KEY") or env.get("GOOGLE_API_KEY"))
    return False


def _has_agy_oauth_credentials() -> bool:
    """Return True when Antigravity (``agy``) appears signed in locally.

    Antigravity CLI authenticates through the OS secure keyring for
    subscription/Google Sign-In users, so a populated
    ``~/.gemini/antigravity-cli/oauth_creds.json`` is not the only valid
    auth signal. Count the JSON token file when present, and otherwise accept
    the Antigravity onboarding + active Google account files as the local
    keyring-backed sign-in marker. Runtime still surfaces an actionable
    "Authentication required." error if the keyring session is stale.
    """
    creds_path = Path.home() / ".gemini" / "antigravity-cli" / "oauth_creds.json"
    try:
        data = json.loads(creds_path.read_text(encoding="utf-8"))
        if isinstance(data, dict) and bool(
            data.get("refresh_token") or data.get("access_token")
        ):
            return True
    except (OSError, json.JSONDecodeError):
        pass

    onboarding_path = (
        Path.home() / ".gemini" / "antigravity-cli" / "cache" / "onboarding.json"
    )
    accounts_path = Path.home() / ".gemini" / "google_accounts.json"
    try:
        onboarding = json.loads(onboarding_path.read_text(encoding="utf-8"))
        accounts = json.loads(accounts_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(onboarding, dict) or not isinstance(accounts, dict):
        return False
    onboarding_complete = bool(
        onboarding.get("onboardingComplete")
        or onboarding.get("consumerOnboardingComplete")
        or onboarding.get("enterpriseOnboardingComplete")
    )
    active_account = accounts.get("active")
    return (
        onboarding_complete
        and isinstance(active_account, str)
        and bool(active_account.strip())
    )


def _has_google_vertex_auth(env: Optional[Dict[str, str]] = None) -> bool:
    """Return True when Google Vertex auth env is configured for the CLIs."""
    if env is None:
        env = os.environ
    if env.get("GOOGLE_GENAI_USE_VERTEXAI") != "true":
        return False
    return bool(
        env.get("GOOGLE_APPLICATION_CREDENTIALS")
        or env.get("GOOGLE_CLOUD_PROJECT")
        or env.get("VERTEXAI_PROJECT")
        or env.get("VERTEX_PROJECT")
    )


def _has_legacy_gemini_oauth_credentials() -> bool:
    """Return True when ONLY the legacy Gemini OAuth file is populated."""
    creds_path = Path.home() / ".gemini" / "oauth_creds.json"
    try:
        data = json.loads(creds_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    return bool(data.get("refresh_token") or data.get("access_token"))


def _get_google_cli_name(env: Optional[Dict[str, str]] = None) -> Optional[str]:
    """Return the *logical* name of the selected Google CLI binary ("agy" or "gemini").

    Uses the same resolution logic as ``_get_google_cli_binary`` but returns
    the preference-key name rather than the filesystem path.  This decouples
    binary-identity checks from ``os.path.basename(cli_path)``, which breaks
    when ``.pddrc`` or ``PDD_GOOGLE_CLI`` points at a wrapper, symlink, or
    versioned binary (e.g. ``/usr/local/bin/agy-1.0.1``).
    """
    if env is None:
        env = os.environ
    pref = env.get("PDD_GOOGLE_CLI", "auto").strip().lower()
    if pref == "agy":
        return "agy" if _find_cli_binary("agy") else None
    if pref == "gemini":
        return "gemini" if _find_cli_binary("gemini") else None
    agy_bin = _find_cli_binary("agy")
    gemini_bin = _find_cli_binary("gemini")
    if agy_bin and gemini_bin:
        # Prefer agy for the migration, except when the only configured auth
        # signal is legacy Gemini OAuth. In that case selecting agy makes
        # runtime availability drop Google even though setup correctly reports
        # legacy Gemini as configured.
        if (
            _has_google_api_key_for_cli("agy", env)
            or _has_google_vertex_auth(env)
            or _has_agy_oauth_credentials()
        ):
            return "agy"
        if _has_legacy_gemini_oauth_credentials():
            return "gemini"
        return "agy"
    if agy_bin:
        return "agy"
    if gemini_bin:
        return "gemini"
    return None


def get_available_agents() -> List[str]:
    """
    Returns list of available provider names based on CLI existence and API key configuration.

    Uses _find_cli_binary() for robust CLI discovery that searches:
    1. .pddrc config overrides
    2. Standard PATH (shutil.which)
    3. Common installation directories
    """
    available = []

    # 1. Anthropic (Claude)
    # Available if 'claude' CLI exists. API key not strictly required (subscription auth).
    if _find_cli_binary("claude"):
        available.append("anthropic")

    # 2. Google (Gemini / Antigravity)
    # Available if the resolved Google CLI binary exists AND a non-interactive
    # auth path that *pairs with that specific binary* is configured. API keys
    # are binary-specific, while Vertex auth works with both binaries. OAuth
    # files are binary-specific: agy reads
    # ~/.gemini/antigravity-cli/oauth_creds.json; legacy gemini reads
    # ~/.gemini/oauth_creds.json. Marking google "available" because *some*
    # Google OAuth exists, then having the binary fail at runtime with
    # "Authentication required.", is a worse UX than just routing to a
    # different available provider — pair the auth signal with the binary.
    google_bin = _get_google_cli_binary()
    google_cli_name = _get_google_cli_name()
    # Pair the API-key signal with the active binary: ANTIGRAVITY_API_KEY is
    # consumed by agy but not by legacy gemini. GOOGLE_API_KEY is accepted by
    # both, and PDD bridges GEMINI_API_KEY to GOOGLE_API_KEY for agy.
    has_google_key = _has_google_api_key_for_cli(google_cli_name or "")
    has_vertex_auth = _has_google_vertex_auth()
    has_matching_oauth = False
    if google_cli_name == "agy":
        has_matching_oauth = _has_agy_oauth_credentials()
    elif google_cli_name == "gemini":
        has_matching_oauth = _has_legacy_gemini_oauth_credentials()

    if google_bin and (has_google_key or has_vertex_auth or has_matching_oauth):
        available.append("google")

    # 3. OpenAI (Codex)
    # Available if 'codex' CLI exists AND any supported auth path is present:
    #   - OPENAI_API_KEY env (direct API auth)
    #   - PDD_CODEX_AUTH_AVAILABLE (cloud waterfall signal)
    #   - ~/.codex/auth.json with a token (local `codex login` ChatGPT auth).
    # Issue #813 round-6 follow-up: keep the runtime check aligned with
    # `pdd setup`'s detection (`_has_provider_oauth("openai")`) so a user
    # with only the file-based login isn't told Codex is configured during
    # setup but then silently dropped from the runtime preference list.
    has_codex_oauth = _has_codex_auth_file()
    if _find_cli_binary("codex") and (
        os.environ.get("OPENAI_API_KEY")
        or os.environ.get("PDD_CODEX_AUTH_AVAILABLE")
        or has_codex_oauth
    ):
        available.append("openai")

    # 4. OpenCode (multi-provider CLI)
    # Available if 'opencode' CLI exists AND at least one usable credential
    # signal is present: stored OpenCode auth.json with provider data, an
    # OpenCode config source declaring a provider, or any provider credential
    # env var represented in pdd/data/llm_model.csv. OPENCODE_MODEL alone is
    # NOT a credential — it's a model knob.
    if _find_cli_binary("opencode") and _has_opencode_credentials():
        available.append("opencode")

    return available


def _has_gemini_oauth_credentials() -> bool:
    """Return True when Gemini/Antigravity CLI stored OAuth credentials are present.

    Gemini CLI supports first-party OAuth auth stored under ~/.gemini. Treating
    API keys and Vertex env as the only available auth paths makes PDD skip a
    working local Gemini CLI and fall into broken providers.
    """
    for creds_path in [
        Path.home() / ".gemini" / "oauth_creds.json",
        Path.home() / ".gemini" / "antigravity-cli" / "oauth_creds.json"
    ]:
        try:
            data = json.loads(creds_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(data, dict):
            if bool(data.get("refresh_token") or data.get("access_token")):
                return True
    return False


def _has_codex_auth_file() -> bool:
    """Return True when Codex CLI stored ChatGPT login is present.

    Codex CLI persists its ChatGPT/OAuth token at ``~/.codex/auth.json``
    (created by ``codex login``). Treating ``OPENAI_API_KEY`` and
    ``PDD_CODEX_AUTH_AVAILABLE`` as the only auth signals makes PDD skip
    a working local Codex CLI when the user has only the file-based login,
    and (Issue #813 round-6 follow-up) creates a UX inconsistency where
    ``pdd setup`` calls Codex configured via this same file but
    ``get_available_agents()`` then drops it from the runtime preference
    list.
    """
    auth_path = Path.home() / ".codex" / "auth.json"
    try:
        data = json.loads(auth_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    return bool(
        data.get("token")
        or data.get("tokens")
        or data.get("OPENAI_API_KEY")
    )

# ---------------------------------------------------------------------------
# OpenCode helpers (auth detection, model resolution, JSONL parsing)
# ---------------------------------------------------------------------------

# Provider credential env vars used by OpenCode-backed providers. The
# authoritative source is ``pdd/data/llm_model.csv`` — the constant below is a
# minimal fallback used only when CSV loading fails (import errors, missing
# pandas, etc.) so detection still works in degraded environments. The
# ``_opencode_provider_env_keys()`` helper merges this fallback with every env
# var named in the CSV's ``api_key`` column, so multi-key rows like
# ``AZURE_API_KEY|AZURE_API_BASE|AZURE_API_VERSION`` and provider-specific
# keys like ``GMI_API_KEY``/``SNOWFLAKE_API_KEY`` are picked up automatically.
_OPENCODE_PROVIDER_ENV_KEYS_FALLBACK: Tuple[str, ...] = (
    "ANTHROPIC_API_KEY",
    "OPENAI_API_KEY",
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    "OPENROUTER_API_KEY",
    "GITHUB_TOKEN",
    "XAI_API_KEY",
    "DEEPSEEK_API_KEY",
    "MISTRAL_API_KEY",
    "COHERE_API_KEY",
    "MOONSHOT_API_KEY",
    "AZURE_API_KEY",
    "AZURE_AI_API_KEY",
    "AWS_ACCESS_KEY_ID",
    "GROQ_API_KEY",
    "TOGETHERAI_API_KEY",
    "FIREWORKS_AI_API_KEY",
    "FIREWORKS_API_KEY",
    "PERPLEXITYAI_API_KEY",
    "REPLICATE_API_KEY",
    "DEEPINFRA_API_KEY",
    "ZAI_API_KEY",
    "DASHSCOPE_API_KEY",
    "MINIMAX_API_KEY",
    "OLLAMA_HOST",
    "LMSTUDIO_HOST",
)

# Env vars that credential an OpenCode provider but that no CSV ``api_key``
# row references (typically OAuth/device-flow providers whose CSV rows have an
# empty ``api_key``). ``_opencode_configured_providers`` consults this map
# after the CSV walk so the fallback resolver can pick a model for these
# providers — otherwise ``_has_opencode_credentials`` would say "available"
# while the resolver returns ``None``.
_OPENCODE_ENV_VAR_TO_PROVIDER: Dict[str, str] = {
    "GITHUB_TOKEN": "github-copilot",
}


def _opencode_provider_env_keys() -> Tuple[str, ...]:
    """Return the union of provider credential env vars from llm_model.csv.

    Derives the env-var allowlist from the catalog the rest of the OpenCode
    code path already trusts (``pdd/data/llm_model.csv``) instead of a static
    list that drifts out of sync with the CSV. Each row's ``api_key`` field
    may be a single env var or a pipe-delimited multi-var set
    (``AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME``); every
    individual var is included so that a single API-key signal — even a
    partial multi-key set — is sufficient to flip ``_has_opencode_credentials``
    to ``True``. Falls back to ``_OPENCODE_PROVIDER_ENV_KEYS_FALLBACK`` when
    CSV loading is unavailable.
    """
    keys: set = set(_OPENCODE_PROVIDER_ENV_KEYS_FALLBACK)
    try:
        df = _load_model_data(None)
    except Exception:
        df = None
    if df is not None and not getattr(df, "empty", True):
        try:
            for raw in df["api_key"].dropna().tolist():
                field = str(raw).strip()
                if not field or field.lower() == "api_key":
                    continue
                for k in field.split("|"):
                    k = k.strip()
                    if k:
                        keys.add(k)
        except Exception:
            pass
    return tuple(sorted(keys))


def _opencode_auth_file_has_credentials(path: Path) -> bool:
    """Return True when ``path`` is an OpenCode auth.json with usable provider data.

    OpenCode CLI persists provider credentials at
    ``~/.local/share/opencode/auth.json`` as ``{provider: {...}, ...}``. Any
    non-empty provider entry counts as a usable credential signal.
    """
    try:
        if not path.exists() or path.stat().st_size == 0:
            return False
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict) or not data:
        return False
    # Any provider entry that is a non-empty dict or non-empty string counts.
    for value in data.values():
        if isinstance(value, dict) and value:
            return True
        if isinstance(value, str) and value.strip():
            return True
    return False


def _opencode_config_paths(cwd: Optional[Path] = None) -> List[Path]:
    """Return candidate OpenCode config file locations (existing files only).

    Order: explicit ``OPENCODE_CONFIG`` env var, project ``opencode.json``
    walking up from ``cwd``, then global ``~/.config/opencode/opencode.json``.
    """
    paths: List[Path] = []
    explicit = os.environ.get("OPENCODE_CONFIG", "").strip()
    if explicit:
        p = Path(explicit)
        if p.is_file():
            paths.append(p)
    start = cwd or Path.cwd()
    try:
        cur = start.resolve()
    except OSError:
        cur = start
    for _ in range(MAX_PDDRC_SEARCH_DEPTH):
        candidate = cur / "opencode.json"
        if candidate.is_file():
            paths.append(candidate)
            break
        parent = cur.parent
        if parent == cur:
            break
        cur = parent
    global_cfg = Path.home() / ".config" / "opencode" / "opencode.json"
    if global_cfg.is_file():
        paths.append(global_cfg)
    # Deduplicate while preserving order
    seen: set[str] = set()
    unique: List[Path] = []
    for p in paths:
        key = str(p)
        if key in seen:
            continue
        seen.add(key)
        unique.append(p)
    return unique


# Field names within an OpenCode ``provider.<id>`` mapping that carry the
# secret material. Compared case-insensitively after stripping ``-``/``_``.
_OPENCODE_PROVIDER_CREDENTIAL_FIELDS = frozenset(
    {"apikey", "key", "token", "bearer", "bearertoken", "accesstoken", "secret"}
)


# Tokenizer for stripping JSONC comments while preserving string contents.
# A naive ``re.sub(r"//[^\n]*", "", text)`` mangles valid configs that
# contain ``"baseURL": "https://..."`` inside JSON strings — the ``//``
# inside the URL gets eaten along with the rest of the line.
# This pattern matches a complete double-quoted JSON string (with backslash
# escapes) OR a block comment OR a line comment, in that priority order;
# strings pass through untouched while comments are dropped.
_JSONC_TOKEN_RE = re.compile(
    r'"(?:\\.|[^"\\])*"'
    r'|/\*[\s\S]*?\*/'
    r'|//[^\n]*'
)


def _strip_jsonc_comments(text: str) -> str:
    """Strip JSONC line/block comments while preserving string contents.

    The previous implementation used ``re.sub(r"//[^\\n]*", "", text)`` which
    silently deleted ``https://...`` inside JSON string values, so a normal
    OpenCode provider config with ``baseURL`` plus ``apiKey`` failed JSON
    parsing and was reported unconfigured.
    """
    def _repl(match: "re.Match[str]") -> str:
        token = match.group(0)
        if token.startswith("//") or token.startswith("/*"):
            return ""
        return token
    return _JSONC_TOKEN_RE.sub(_repl, text)


def _parse_opencode_config_text(text: str) -> Optional[Dict[str, Any]]:
    """Parse a JSON/JSONC OpenCode config payload to a dict, or ``None``."""
    if not text:
        return None
    try:
        data = json.loads(_strip_jsonc_comments(text))
    except (json.JSONDecodeError, ValueError):
        return None
    return data if isinstance(data, dict) else None


def _opencode_data_declares_provider(
    data: Optional[Dict[str, Any]],
    base_dir: Optional[Path] = None,
) -> bool:
    """Return True when parsed OpenCode config declares usable provider auth.

    ``base_dir`` is the directory of the config file the data was parsed from
    (or ``None`` for inline ``OPENCODE_CONFIG_CONTENT``). It is passed to the
    template resolver so that ``{file:relative.txt}`` references resolve
    against the config directory, matching the OpenCode config contract
    (https://opencode.ai/docs/config/).
    """
    if not isinstance(data, dict):
        return False
    provider = data.get("provider")
    if isinstance(provider, dict):
        for value in provider.values():
            if _opencode_provider_value_has_usable_credential(value, base_dir=base_dir):
                return True
    return False


def _iter_opencode_config_texts(
    cwd: Optional[Path] = None,
) -> List[Tuple[str, Optional[Path]]]:
    """Yield ``(text, base_dir)`` pairs from all OpenCode config sources.

    Includes both file-backed sources (``OPENCODE_CONFIG``, project
    ``opencode.json``, global ``~/.config/opencode/opencode.json``) and the
    ``OPENCODE_CONFIG_CONTENT`` env var, which the prompt contract treats as
    an inline config payload equivalent to a discovered file. ``base_dir`` is
    the directory of the config file (used to resolve ``{file:...}``
    substitutions per the OpenCode config contract); for inline content there
    is no on-disk anchor so ``base_dir`` is ``None``.
    """
    texts: List[Tuple[str, Optional[Path]]] = []
    for cfg in _opencode_config_paths(cwd):
        try:
            texts.append((cfg.read_text(encoding="utf-8"), cfg.parent))
        except OSError:
            continue
    inline = os.environ.get("OPENCODE_CONFIG_CONTENT", "")
    if inline and inline.strip():
        texts.append((inline, None))
    return texts

# Containers within a provider mapping that may nest credential fields.
_OPENCODE_PROVIDER_CREDENTIAL_CONTAINERS = frozenset({"options", "auth", "headers"})


def _resolve_opencode_template_value(
    value: Any,
    base_dir: Optional[Path] = None,
) -> Optional[str]:
    """Resolve an OpenCode config template ``{env:VAR}`` / ``{file:PATH}``.

    Returns the resolved non-empty string, or ``None`` when the template
    cannot be resolved (env var unset, file missing/empty). Plain strings
    pass through after stripping; non-strings return ``None``.

    Per the OpenCode config docs (https://opencode.ai/docs/config/),
    relative ``{file:...}`` paths resolve against the directory of the
    config file that referenced them — not the PDD process cwd. ``base_dir``
    carries that anchor through from the iterator. Absolute paths and
    ``~``-prefixed paths are honored as-is. When ``base_dir`` is ``None``
    (inline ``OPENCODE_CONFIG_CONTENT`` has no on-disk anchor) we fall back
    to the existing cwd-relative behavior.
    """
    if not isinstance(value, str):
        return None
    s = value.strip()
    if not s:
        return None
    m = re.fullmatch(r"\{env:([^}]+)\}", s)
    if m:
        v = os.environ.get(m.group(1).strip())
        return v.strip() if v and v.strip() else None
    m = re.fullmatch(r"\{file:([^}]+)\}", s)
    if m:
        raw = m.group(1).strip()
        candidate = Path(raw).expanduser()
        # Anchor relative paths to the config file directory if known.
        if not candidate.is_absolute() and base_dir is not None and not raw.startswith("~"):
            candidate = base_dir / candidate
        try:
            text = candidate.read_text(encoding="utf-8").strip()
        except OSError:
            return None
        return text or None
    # Plain string with no template: treat as a literal credential value.
    return s


def _opencode_provider_value_has_usable_credential(
    value: Any,
    base_dir: Optional[Path] = None,
) -> bool:
    """Return True when an OpenCode ``provider.<id>`` value carries usable auth.

    OpenCode config files frequently contain provider preferences (model
    name, options) without credentials, including unresolved
    ``{env:VAR}`` / ``{file:PATH}`` references. This walks one level deep
    into the value, looking only for credential-shaped fields whose
    resolved string is non-empty. ``base_dir`` is forwarded to the template
    resolver so ``{file:relative.txt}`` references are anchored to the
    config file directory.
    """
    if isinstance(value, str):
        return _resolve_opencode_template_value(value, base_dir=base_dir) is not None
    if not isinstance(value, dict):
        return False
    for key, sub in value.items():
        if not isinstance(key, str):
            continue
        normalized = key.lower().replace("-", "").replace("_", "")
        if normalized in _OPENCODE_PROVIDER_CREDENTIAL_FIELDS:
            if isinstance(sub, str):
                if _resolve_opencode_template_value(sub, base_dir=base_dir) is not None:
                    return True
            elif isinstance(sub, dict):
                for v in sub.values():
                    if isinstance(v, str) and _resolve_opencode_template_value(v, base_dir=base_dir) is not None:
                        return True
            continue
        if normalized in _OPENCODE_PROVIDER_CREDENTIAL_CONTAINERS and isinstance(sub, dict):
            if _opencode_provider_value_has_usable_credential(sub, base_dir=base_dir):
                return True
    return False


def _opencode_config_declares_provider(path: Path) -> bool:
    """Return True when an OpenCode config file declares usable provider auth.

    A bare ``model`` preference or an empty ``provider`` mapping is
    diagnostic-only — it must not flip availability. A ``provider`` entry
    qualifies only when it contains a credential-shaped field (apiKey, key,
    token, bearer, ...) whose resolved value is non-empty. Unresolved
    ``{env:VAR}`` / ``{file:PATH}`` references with the env var unset or
    the file missing do not qualify.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return False
    # OpenCode supports JSONC. ``_parse_opencode_config_text`` strips
    # comments without eating ``//`` that appears inside string values
    # (e.g. ``"baseURL": "https://..."``). The config-file directory is
    # passed as ``base_dir`` so ``{file:relative.txt}`` substitutions
    # resolve against the config file's directory, per the OpenCode docs.
    return _opencode_data_declares_provider(
        _parse_opencode_config_text(text), base_dir=path.parent
    )


def _has_opencode_credentials(cwd: Optional[Path] = None) -> bool:
    """Return True when any OpenCode credential signal is present.

    Signals (any one is sufficient):
      - ``~/.local/share/opencode/auth.json`` parses to non-empty provider data
      - An OpenCode config source declares a provider/model
      - Any provider credential env var from llm_model.csv is set
    """
    auth_path = Path.home() / ".local" / "share" / "opencode" / "auth.json"
    if _opencode_auth_file_has_credentials(auth_path):
        return True
    # File-backed configs and the inline ``OPENCODE_CONFIG_CONTENT`` env var
    # both qualify per the prompt contract.
    for text, base_dir in _iter_opencode_config_texts(cwd):
        if _opencode_data_declares_provider(
            _parse_opencode_config_text(text), base_dir=base_dir
        ):
            return True
    for key in _opencode_provider_env_keys():
        val = os.environ.get(key)
        if val and val.strip():
            return True
    return False


def _translate_to_opencode_model(model_id: str) -> str:
    """Translate LiteLLM-oriented model IDs to OpenCode ``provider/model`` form.

    Rules:
      * ``github_copilot/X`` -> ``github-copilot/X``
      * ``gemini/X`` -> ``google/X``
      * Bare ``claude-...`` -> ``anthropic/claude-...``
      * Bare ``gpt-...`` -> ``openai/gpt-...``
      * IDs already in ``provider/model`` form pass through unchanged.
    """
    if not model_id:
        return model_id
    mid = model_id.strip()
    if mid.startswith("github_copilot/"):
        return "github-copilot/" + mid[len("github_copilot/"):]
    if mid.startswith("gemini/"):
        return "google/" + mid[len("gemini/"):]
    if "/" in mid:
        return mid
    if mid.startswith("claude-"):
        return f"anthropic/{mid}"
    if mid.startswith("gpt-"):
        return f"openai/{mid}"
    return mid


def _opencode_configured_providers(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> set:
    """Return the OpenCode provider IDs that have a usable credential source.

    Used by the CSV-based model fallback to filter candidate rows to providers
    OpenCode can actually route to. Sources (any one is sufficient):

      * Top-level keys in ``~/.local/share/opencode/auth.json``
      * ``provider`` mapping keys in OpenCode config files (project, global,
        ``OPENCODE_CONFIG``, or inline ``OPENCODE_CONFIG_CONTENT``)
      * CSV rows in ``pdd/data/llm_model.csv`` whose *full* ``api_key`` env
        var set is satisfied in ``env`` — pipe-delimited multi-var entries
        like ``AZURE_API_KEY|AZURE_API_BASE|AZURE_API_VERSION`` MUST all be
        set; partial credentials must not flip a provider to "configured"
        because OpenCode cannot actually route to it.
    """
    src = env if env is not None else os.environ
    providers: set = set()

    auth_path = Path.home() / ".local" / "share" / "opencode" / "auth.json"
    try:
        if auth_path.exists() and auth_path.stat().st_size > 0:
            data = json.loads(auth_path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                for key, value in data.items():
                    if isinstance(value, dict) and value:
                        providers.add(key)
                    elif isinstance(value, str) and value.strip():
                        providers.add(key)
    except (OSError, json.JSONDecodeError):
        pass

    for text, base_dir in _iter_opencode_config_texts(cwd):
        cfg_data = _parse_opencode_config_text(text)
        if not isinstance(cfg_data, dict):
            continue
        provider_dict = cfg_data.get("provider")
        if isinstance(provider_dict, dict):
            for k, v in provider_dict.items():
                # Only count provider entries that actually carry usable
                # auth — a bare options/model preference or an unresolved
                # ``{env:VAR}`` reference does not constitute a credential.
                if _opencode_provider_value_has_usable_credential(v, base_dir=base_dir):
                    providers.add(k)

    # Walk the CSV catalog and add a provider only when *every* env var in
    # its pipe-delimited ``api_key`` field is set. Mapping the CSV row to an
    # OpenCode provider ID goes through ``_translate_to_opencode_model`` so
    # the rules stay in lockstep with how the fallback labels rows.
    try:
        df = _load_model_data(None)
    except Exception:
        df = None
    if df is not None and not getattr(df, "empty", True):
        for _, row in df.iterrows():
            api_key_field = str(row.get("api_key") or "").strip()
            if not api_key_field:
                # Empty ``api_key`` (no-key/device-flow rows like
                # ``github_copilot/...``) cannot make a provider configured
                # via env vars; auth.json / opencode.json handle those.
                continue
            keys = [k.strip() for k in api_key_field.split("|") if k.strip()]
            if not keys:
                continue
            if not all((src.get(k) or "").strip() for k in keys):
                continue
            model_id = str(row.get("model") or "").strip()
            if not model_id:
                continue
            translated = _translate_to_opencode_model(model_id)
            # Only rows that translate to OpenCode's required ``provider/model``
            # form contribute a provider here. Rows whose translation is bare
            # (e.g. AWS Bedrock IDs like ``anthropic.claude-opus-4-7`` that
            # lack a known OpenCode provider prefix) must NOT pollute the
            # configured-provider set, otherwise ``_resolve_opencode_csv_fallback``
            # would happily echo that bare ID back as ``--model`` and OpenCode
            # would reject it.
            if "/" not in translated:
                continue
            prefix = translated.split("/", 1)[0]
            if prefix:
                providers.add(prefix)

    # Some OpenCode providers are credentialed by env vars that are not part
    # of any CSV ``api_key`` field (e.g. ``GITHUB_TOKEN`` for ``github-copilot``,
    # which uses device-flow / OAuth so its CSV rows have an empty ``api_key``).
    # Without this mapping the env var alone makes ``_has_opencode_credentials``
    # answer True while ``_resolve_opencode_csv_fallback`` returns ``None``,
    # so OpenCode appears available but no model is selectable.
    for env_var, provider_id in _OPENCODE_ENV_VAR_TO_PROVIDER.items():
        if (src.get(env_var) or "").strip():
            providers.add(provider_id)

    return providers


def _resolve_opencode_csv_fallback(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> Optional[str]:
    """Pick an OpenCode model from ``llm_model.csv`` using auth-aware filtering.

    Walks the CSV rows in descending DeepSWE-first rank order and returns the
    first row whose ``api_key`` env vars are all set AND whose
    ``_translate_to_opencode_model`` output has a provider prefix in the
    configured-provider set. Older/custom CSVs without ``model_rank_score``
    fall back to raw ``coding_arena_elo``. Returns ``None`` when no row
    qualifies (caller surfaces an actionable error).
    """
    src = env if env is not None else os.environ
    try:
        df = _load_model_data(None)
    except Exception:
        return None
    if df is None or getattr(df, "empty", True):
        return None

    configured = _opencode_configured_providers(env=src, cwd=cwd)
    if not configured:
        return None

    try:
        rank_df = df.copy()
        if "model_rank_score" not in rank_df.columns:
            rank_df["model_rank_score"] = rank_df["coding_arena_elo"]
        else:
            rank_df["model_rank_score"] = rank_df["model_rank_score"].fillna(
                rank_df["coding_arena_elo"]
            )
        sorted_df = rank_df.sort_values("model_rank_score", ascending=False)
    except Exception:
        return None

    # A row qualifies when its translated provider prefix is in the
    # configured-provider set. ``configured`` already merges signals from
    # ``~/.local/share/opencode/auth.json``, OpenCode config files, and
    # provider env vars, so a user who ran ``opencode auth login`` for a
    # provider — or who set its API key env var — gets CSV-driven fallback
    # without also having to set both. This intentionally lets no-key /
    # device-flow rows like ``github_copilot/...`` participate when
    # OpenCode has the ``github-copilot`` provider configured, instead of
    # being skipped before translation.
    for _, row in sorted_df.iterrows():
        model_id = str(row.get("model") or "").strip()
        if not model_id:
            continue
        translated = _translate_to_opencode_model(model_id)
        # OpenCode requires ``--model provider/model`` form. Skip rows whose
        # translation is bare (e.g. AWS Bedrock IDs like
        # ``anthropic.claude-opus-4-7``) — passing them through would make
        # OpenCode reject the run with an invalid-model error.
        if "/" not in translated:
            continue
        prefix = translated.split("/", 1)[0]
        if prefix in configured:
            return translated
    return None


def _opencode_csv_cost(model_id: Optional[str], tokens: Optional[Dict[str, Any]]) -> float:
    """Compute USD cost for an OpenCode run from the CSV pricing row.

    Falls back here when OpenCode JSONL omits ``step_finish.part.cost`` so
    successful runs are not silently reported as ``$0.00``. ``model_id`` may
    be either the OpenCode ``provider/model`` form or a bare CSV model name;
    we match against the CSV ``model`` column directly. Returns ``0.0`` when
    we cannot match the row or no token counts are available.

    Pricing in ``llm_model.csv`` is per-million tokens. The Anthropic
    conventions used elsewhere (cache_read 90% off, cache_write 25% premium
    over input) are applied uniformly here for parity with the existing
    `ANTHROPIC_PRICING_BY_FAMILY` formula — backends without cache events
    just see those counters at zero.
    """
    if not model_id:
        return 0.0
    if not isinstance(tokens, dict):
        return 0.0
    try:
        df = _load_model_data(None)
    except Exception:
        return 0.0
    if df is None or getattr(df, "empty", True):
        return 0.0
    # Build a *provider-aware* candidate list. A naive suffix-strip fallback
    # like ``model_id.rsplit("/", 1)[1]`` would match an OpenCode ID such as
    # ``github-copilot/gpt-5`` against the unrelated OpenAI ``gpt-5`` row in
    # the CSV (charging $11.25/M instead of GitHub Copilot's $0.0). Each rule
    # below is the inverse of a translation in ``_translate_to_opencode_model``
    # and only strips the OpenCode provider prefix when the suffix can only
    # belong to that provider's CSV row family.
    candidates = [model_id]
    if "/" in model_id:
        head, tail = model_id.split("/", 1)
        if head == "github-copilot":
            candidates.append("github_copilot/" + tail)
        elif head == "google":
            candidates.append("gemini/" + tail)
        elif head == "anthropic" and tail.startswith("claude-"):
            # Anthropic native CSV rows are bare ``claude-...``.
            candidates.append(tail)
        elif head == "openai" and tail.startswith("gpt-"):
            # OpenAI native CSV rows are bare ``gpt-...``.
            candidates.append(tail)
        else:
            # Generic last-segment fallback for routers like
            # ``openrouter/openai/gpt-5.3-codex`` whose final segment is the
            # CSV model id. Kept conservative: only the *last* segment, and
            # only when the prefix isn't one we already de-translated above
            # — this avoids the cross-provider mismatch the inverse rules
            # above were added to prevent.
            candidates.append(model_id.rsplit("/", 1)[1])
    row = None
    for cand in candidates:
        match = df[df["model"] == cand]
        if not match.empty:
            row = match.iloc[0]
            break
    if row is None:
        return 0.0
    try:
        input_per_m = float(row.get("input") or 0.0)
        output_per_m = float(row.get("output") or 0.0)
    except (TypeError, ValueError):
        return 0.0
    input_tokens = int(tokens.get("input") or 0)
    output_tokens = int(tokens.get("output") or 0)
    cache_read = int(tokens.get("cache_read") or 0)
    cache_write = int(tokens.get("cache_write") or 0)
    if input_tokens <= 0 and output_tokens <= 0 and cache_read <= 0 and cache_write <= 0:
        return 0.0
    new_input = max(0, input_tokens - cache_read - cache_write)
    cost = (
        new_input * input_per_m / 1_000_000
        + output_tokens * output_per_m / 1_000_000
        + cache_read * input_per_m * 0.1 / 1_000_000
        + cache_write * input_per_m * 1.25 / 1_000_000
    )
    return float(cost)


def _resolve_opencode_model(env: Optional[Dict[str, str]] = None) -> Optional[str]:
    """Resolve the OpenCode model from ``OPENCODE_MODEL`` only.

    Returns the env var value verbatim (including nested slashes such as
    ``openrouter/openai/gpt-5.3-codex``), or ``None`` when unset. CSV-based
    fallback resolution lives in :func:`_resolve_opencode_model_for_run` so
    callers that only want the env-var view (tests, diagnostics) are not
    coupled to filesystem probes.
    """
    src = env if env is not None else os.environ
    raw = (src.get("OPENCODE_MODEL") or "").strip()
    if raw:
        return raw
    return None


def _resolve_opencode_model_for_run(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> Optional[str]:
    """Resolve the OpenCode model with auth-aware CSV fallback.

    Order per the prompt contract: (1) ``OPENCODE_MODEL`` env var, kept
    verbatim; (2) auth-filtered ``llm_model.csv`` row whose translated
    ``provider/model`` identifier maps to a configured OpenCode provider.
    """
    src = env if env is not None else os.environ
    raw = (src.get("OPENCODE_MODEL") or "").strip()
    if raw:
        return raw
    return _resolve_opencode_csv_fallback(env=src, cwd=cwd)


def _parse_opencode_jsonl(stdout: str) -> Dict[str, Any]:
    """Parse OpenCode JSONL output into a normalized accounting dict.

    OpenCode emits one JSON object per line (``--format json``) with events
    such as ``step_start``, ``step_finish``, ``text``, ``tool_use``, and
    ``error``. Returns a dict with keys:

      * ``text``: concatenated visible text payloads
      * ``cost``: summed ``step_finish.part.cost`` values (USD)
      * ``cost_reported``: True iff any cost field appeared
      * ``model``: model name surfaced by the run (empty when absent)
      * ``error``: first error message encountered (empty when none)
      * ``tokens``: dict with ``input``, ``output``, ``reasoning``,
        ``cache_read``, ``cache_write`` counters
    """
    text_parts: List[str] = []
    cost_total: float = 0.0
    cost_reported = False
    model_names: List[str] = []
    error_msg = ""
    tokens = {"input": 0, "output": 0, "reasoning": 0, "cache_read": 0, "cache_write": 0}

    if not stdout:
        return {
            "text": "",
            "cost": 0.0,
            "cost_reported": False,
            "model": "",
            "error": "",
            "tokens": tokens,
        }

    def _add_model(name: Any) -> None:
        if isinstance(name, str) and name.strip() and name not in model_names:
            model_names.append(name.strip())

    def _accumulate_tokens(usage: Any) -> None:
        if not isinstance(usage, dict):
            return
        for src_key, dst_key in (
            ("input", "input"),
            ("input_tokens", "input"),
            ("prompt_tokens", "input"),
            ("output", "output"),
            ("output_tokens", "output"),
            ("completion_tokens", "output"),
            ("reasoning", "reasoning"),
            ("reasoning_tokens", "reasoning"),
        ):
            v = usage.get(src_key)
            if isinstance(v, (int, float)):
                tokens[dst_key] += int(v)
        cache = usage.get("cache")
        if isinstance(cache, dict):
            for src_key, dst_key in (
                ("read", "cache_read"),
                ("write", "cache_write"),
            ):
                v = cache.get(src_key)
                if isinstance(v, (int, float)):
                    tokens[dst_key] += int(v)

    for raw_line in stdout.splitlines():
        line = raw_line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(event, dict):
            continue

        ev_type = event.get("type", "")

        # Capture model from any event that carries it.
        _add_model(event.get("model"))
        for nested_key in ("session", "message", "part"):
            nested = event.get(nested_key)
            if isinstance(nested, dict):
                _add_model(nested.get("model"))

        if ev_type == "error":
            msg = event.get("message") or event.get("error") or ""
            if isinstance(msg, dict):
                msg = msg.get("message") or msg.get("error") or ""
            if msg and not error_msg:
                error_msg = str(msg)
            continue

        if ev_type in ("step_start", "tool_use"):
            continue

        if ev_type == "step_finish":
            part = event.get("part")
            if isinstance(part, dict):
                cost_val = part.get("cost")
                if isinstance(cost_val, (int, float)):
                    cost_total += float(cost_val)
                    cost_reported = True
                _accumulate_tokens(part.get("usage") or part.get("tokens"))
            _accumulate_tokens(event.get("usage") or event.get("tokens"))
            continue

        if ev_type == "text":
            part = event.get("part")
            if isinstance(part, dict) and isinstance(part.get("text"), str):
                text_parts.append(part["text"])
            elif isinstance(event.get("text"), str):
                text_parts.append(event["text"])
            elif isinstance(event.get("content"), str):
                text_parts.append(event["content"])
            continue

        # Tolerate top-level cost on unknown events for forward compatibility.
        cost_val = event.get("cost")
        if isinstance(cost_val, (int, float)):
            cost_total += float(cost_val)
            cost_reported = True

    model_str = "+".join(sorted(model_names)) if len(model_names) > 1 else (model_names[0] if model_names else "")

    return {
        "text": "".join(text_parts),
        "cost": cost_total,
        "cost_reported": cost_reported,
        "model": model_str,
        "error": error_msg,
        "tokens": tokens,
    }


def _calculate_gemini_cost(stats: Dict[str, Any]) -> float:
    """Calculates cost for Gemini based on token stats."""
    total_cost = 0.0
    models = stats.get("models", {})
    
    for model_name, data in models.items():
        tokens = data.get("tokens", {})
        prompt = tokens.get("prompt", 0)
        candidates = tokens.get("candidates", 0)
        cached = tokens.get("cached", 0)
        
        # Determine pricing family
        family = "flash" if "flash" in model_name.lower() else "pro"
        pricing = GEMINI_PRICING_BY_FAMILY.get(family, GEMINI_PRICING_BY_FAMILY["flash"])
        
        # Logic: new_input = max(0, prompt - cached)
        # Assuming 'prompt' is total input tokens
        new_input = max(0, prompt - cached)
        
        input_cost = (new_input / 1_000_000) * pricing.input_per_million
        cached_cost = (cached / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
        output_cost = (candidates / 1_000_000) * pricing.output_per_million
        
        total_cost += input_cost + cached_cost + output_cost
        
    return total_cost

def _calculate_codex_cost(usage: Dict[str, Any]) -> float:
    """Calculates cost for Codex based on usage stats."""
    input_tokens = usage.get("input_tokens", 0)
    output_tokens = usage.get("output_tokens", 0)
    cached_tokens = usage.get("cached_input_tokens", 0)
    
    pricing = CODEX_PRICING
    
    # Logic: new_input = max(0, input - cached)
    new_input = max(0, input_tokens - cached_tokens)
    
    input_cost = (new_input / 1_000_000) * pricing.input_per_million
    cached_cost = (cached_tokens / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    output_cost = (output_tokens / 1_000_000) * pricing.output_per_million
    
    return input_cost + cached_cost + output_cost


def _calculate_anthropic_cost(data: Dict[str, Any]) -> float:
    """Calculate cost from Claude Code JSON when total_cost_usd is missing.

    Tries modelUsage per-model costUSD first, then falls back to token-based
    estimation from the usage field.
    """
    # Try 1: Sum costUSD from modelUsage (most accurate)
    raw_model_usage = data.get("modelUsage", {})
    model_usage = raw_model_usage if isinstance(raw_model_usage, dict) else {}
    if model_usage:
        total = sum(
            float(info.get("costUSD", 0.0))
            for info in model_usage.values()
            if isinstance(info, dict)
        )
        if total > 0:
            return total

    # Try 2: Token-based estimation from aggregate usage field
    usage = data.get("usage", {})
    if isinstance(usage, dict) and usage:
        family = _anthropic_pricing_family_for_aggregate(data, model_usage)
        cost = _calculate_anthropic_usage_cost(usage, family)
        if cost is not None:
            return cost

    # Try 3: Token-based estimation from validated per-model modelUsage fields.
    model_usage_cost = _calculate_anthropic_model_usage_token_cost(model_usage)
    if model_usage_cost is not None:
        return model_usage_cost

    return 0.0


_INPUT_TOKEN_KEYS: Tuple[str, ...] = ("input_tokens", "inputTokens")
_OUTPUT_TOKEN_KEYS: Tuple[str, ...] = ("output_tokens", "outputTokens")
_CACHE_READ_TOKEN_KEYS: Tuple[str, ...] = (
    "cache_read_input_tokens",
    "cached_input_tokens",
    "cacheReadInputTokens",
    "cachedInputTokens",
)
_CACHE_CREATION_TOKEN_KEYS: Tuple[str, ...] = (
    "cache_creation_input_tokens",
    "cacheCreationInputTokens",
)


def _validated_token_counter(
    usage: Dict[str, Any],
    aliases: Tuple[str, ...],
    *,
    required: bool,
) -> Optional[int]:
    """Return a non-negative token count, or None for missing/invalid required data."""
    value = None
    found = False
    for key in aliases:
        if key in usage:
            value = usage[key]
            found = True
            break

    if not found:
        return None if required else 0
    if isinstance(value, bool) or not isinstance(value, int):
        return None
    if value < 0:
        return None
    return value


def _validated_anthropic_token_counts(
    usage: Dict[str, Any],
) -> Optional[Tuple[int, int, int, int]]:
    """Return validated Anthropic token counters in canonical order."""
    input_tokens = _validated_token_counter(
        usage,
        _INPUT_TOKEN_KEYS,
        required=True,
    )
    output_tokens = _validated_token_counter(
        usage,
        _OUTPUT_TOKEN_KEYS,
        required=True,
    )
    cache_read = _validated_token_counter(
        usage,
        _CACHE_READ_TOKEN_KEYS,
        required=False,
    )
    cache_creation = _validated_token_counter(
        usage,
        _CACHE_CREATION_TOKEN_KEYS,
        required=False,
    )
    if (
        input_tokens is None
        or output_tokens is None
        or cache_read is None
        or cache_creation is None
    ):
        return None
    return input_tokens, output_tokens, cache_read, cache_creation


def _anthropic_pricing_family_from_model_name(model_name: Optional[str]) -> Optional[str]:
    """Return the Anthropic pricing family implied by an observed model name."""
    if not isinstance(model_name, str) or not model_name:
        return None
    name_lower = model_name.lower()
    if "opus" in name_lower:
        return "opus"
    if "haiku" in name_lower:
        return "haiku"
    if "sonnet" in name_lower:
        return "sonnet"
    return None


def _anthropic_pricing_family_from_model_usage(
    model_usage: Dict[str, Any],
) -> Optional[str]:
    """Infer aggregate pricing family from modelUsage keys."""
    selected = None
    for model_name in model_usage.keys():
        family = _anthropic_pricing_family_from_model_name(str(model_name))
        if family == "opus":
            return "opus"
        if family == "haiku" and selected is None:
            selected = "haiku"
        elif family == "sonnet" and selected is None:
            selected = "sonnet"
    return selected


def _calculate_anthropic_usage_cost(
    usage: Dict[str, Any],
    family: Optional[str],
) -> Optional[float]:
    """Calculate Anthropic token cost from validated usage counters."""
    counts = _validated_anthropic_token_counts(usage)
    if counts is None:
        return None
    input_tokens, output_tokens, cache_read, cache_creation = counts

    pricing_family = family or "sonnet"
    pricing = ANTHROPIC_PRICING_BY_FAMILY.get(
        pricing_family,
        ANTHROPIC_PRICING_BY_FAMILY["sonnet"],
    )

    # new_input = total input minus cached reads and cache creation (those tokens are billed separately)
    new_input = max(0, input_tokens - cache_read - cache_creation)
    input_cost = (new_input / 1_000_000) * pricing.input_per_million
    cache_read_cost = (cache_read / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    cache_write_cost = (cache_creation / 1_000_000) * pricing.input_per_million * 1.25
    output_cost = (output_tokens / 1_000_000) * pricing.output_per_million

    return input_cost + cache_read_cost + cache_write_cost + output_cost


def _calculate_anthropic_model_usage_token_cost(
    model_usage: Dict[str, Any],
) -> Optional[float]:
    """Estimate cost from validated per-model modelUsage token counters."""
    if not model_usage:
        return None

    total = 0.0
    saw_valid_usage = False
    for model_name, usage in model_usage.items():
        if not isinstance(usage, dict) or not _has_token_counter_key(usage):
            continue
        family = (
            _anthropic_pricing_family_from_model_name(str(model_name))
            or "sonnet"
        )
        cost = _calculate_anthropic_usage_cost(usage, family)
        if cost is None:
            return None
        total += cost
        saw_valid_usage = True

    return total if saw_valid_usage else None


def _build_claude_usage_record(
    model_name: str,
    usage: Dict[str, Any],
) -> Optional[Dict[str, Any]]:
    """Build one JSON-serializable Claude usage record from validated counters."""
    counts = _validated_anthropic_token_counts(usage)
    if counts is None:
        return None
    input_tokens, output_tokens, cached_input_tokens, cache_creation_input_tokens = counts

    return {
        "model": model_name,
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "cached_input_tokens": cached_input_tokens,
        "cache_creation_input_tokens": cache_creation_input_tokens,
    }


def _has_token_counter_key(usage: Dict[str, Any]) -> bool:
    """Return True when a usage object contains any known token counter key."""
    aliases = (
        _INPUT_TOKEN_KEYS
        + _OUTPUT_TOKEN_KEYS
        + _CACHE_READ_TOKEN_KEYS
        + _CACHE_CREATION_TOKEN_KEYS
    )
    return any(key in usage for key in aliases)


def _has_counter_alias(usage: Dict[str, Any], aliases: Tuple[str, ...]) -> bool:
    """Return True when any alias in a counter family is present."""
    return any(key in usage for key in aliases)


def _has_complete_cache_counters(usage: Dict[str, Any]) -> bool:
    """Return True when both cache-read and cache-creation counters are explicit."""
    return (
        _has_counter_alias(usage, _CACHE_READ_TOKEN_KEYS)
        and _has_counter_alias(usage, _CACHE_CREATION_TOKEN_KEYS)
    )


def _has_nonzero_or_invalid_cache_counter(usage: Dict[str, Any]) -> bool:
    """Return True when aggregate cache counters should not be silently dropped."""
    for aliases in (_CACHE_READ_TOKEN_KEYS, _CACHE_CREATION_TOKEN_KEYS):
        value = _validated_token_counter(usage, aliases, required=False)
        if value is None or value > 0:
            return True
    return False


def _merge_missing_cache_counters(
    per_model_usage: Dict[str, Any],
    aggregate_usage: Dict[str, Any],
) -> Dict[str, Any]:
    """Fill absent per-model cache counters from aggregate Claude usage."""
    merged = dict(per_model_usage)
    for aliases in (_CACHE_READ_TOKEN_KEYS, _CACHE_CREATION_TOKEN_KEYS):
        if any(key in merged for key in aliases):
            continue
        for key in aliases:
            if key in aggregate_usage:
                merged[key] = aggregate_usage[key]
                break
    return merged


def _extract_anthropic_model_from_envelope(data: Dict[str, Any]) -> Optional[str]:
    """Extract a concrete Claude model from known JSON envelope locations."""
    model = data.get("model")
    if isinstance(model, str) and model:
        return model

    for key in ("message", "response", "result", "advisor"):
        value = data.get(key)
        if not isinstance(value, dict):
            continue
        model = value.get("model")
        if isinstance(model, str) and model:
            return model
    return None


def _anthropic_pricing_family_for_aggregate(
    data: Dict[str, Any],
    model_usage: Dict[str, Any],
) -> str:
    """Pick a pricing family for aggregate Claude usage from observed models."""
    return (
        _anthropic_pricing_family_from_model_usage(model_usage)
        or _anthropic_pricing_family_from_model_name(
            _extract_anthropic_model_from_envelope(data)
        )
        or "sonnet"
    )


def _extract_anthropic_standard_usage(
    data: Any,
    *,
    actual_model: Optional[str],
) -> AgenticUsage:
    """Extract GVS-compatible usage from a Claude Code JSON envelope."""
    if not isinstance(data, dict):
        return None

    model_usage = data.get("modelUsage")
    if isinstance(model_usage, dict) and model_usage:
        records: List[Dict[str, Any]] = []
        names = sorted(str(name) for name in model_usage if name)
        aggregate_usage = data.get("usage")
        aggregate_has_nonzero_cache = (
            isinstance(aggregate_usage, dict)
            and _has_nonzero_or_invalid_cache_counter(aggregate_usage)
        )
        for model_name in names:
            per_model_usage = model_usage.get(model_name)
            has_per_model_counters = (
                isinstance(per_model_usage, dict)
                and _has_token_counter_key(per_model_usage)
            )
            if (
                len(names) > 1
                and aggregate_has_nonzero_cache
                and has_per_model_counters
                and not _has_complete_cache_counters(per_model_usage)
            ):
                return None
            record_usage = per_model_usage
            if (
                len(names) == 1
                and isinstance(record_usage, dict)
                and isinstance(aggregate_usage, dict)
            ):
                record_usage = _merge_missing_cache_counters(
                    record_usage,
                    aggregate_usage,
                )
            record = (
                _build_claude_usage_record(model_name, record_usage)
                if isinstance(record_usage, dict)
                else None
            )
            if (
                record is None
                and not has_per_model_counters
                and len(names) == 1
                and isinstance(aggregate_usage, dict)
            ):
                record = _build_claude_usage_record(model_name, aggregate_usage)
            if record is None:
                return None
            records.append(record)
        if records:
            return {"claude": records}

    usage = data.get("usage")
    if not isinstance(usage, dict):
        return None

    model_name = (
        _extract_anthropic_model_from_envelope(data)
        or actual_model
    )
    if not model_name:
        return None

    record = _build_claude_usage_record(model_name, usage)
    if record is None:
        return None
    return {"claude": [record]}


def run_agentic_task(
    instruction: str,
    cwd: Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
    label: str = "",
    timeout: Optional[float] = None,
    max_retries: int = 1,
    retry_delay: float = DEFAULT_RETRY_DELAY,
    deadline: Optional[float] = None,
    use_playwright: bool = False,
    reasoning_time: Optional[float] = None,
    steers: Optional[List[SteerEntry]] = None,
    claude_policy: Optional[ClaudePolicy] = None,
) -> AgenticTaskResult:
    """
    Runs an agentic task using available providers in preference order.

    Args:
        instruction: The task instruction
        cwd: Working directory
        verbose: Show detailed output
        quiet: Suppress all non-error output
        label: Task label for logging
        timeout: Optional timeout override
        max_retries: Number of attempts per provider before fallback (default: 1 = no retries)
        retry_delay: Base delay in seconds for exponential backoff (default: DEFAULT_RETRY_DELAY)
        deadline: Optional Unix timestamp for job-level time budgeting
        use_playwright: Enable constrained tool access mode for browser-based testing
        reasoning_time: Reasoning-allocation float in [0.0, 1.0] forwarded from the
            top-level ``pdd --time`` flag. When provided, overrides the
            ``PDD_REASONING_EFFORT`` env var for argv injection. ``None``
            means "fall back to env" so unplumbed call sites keep working.
        steers: Optional list of mid-run steering entries to inject into the instruction.
        claude_policy: Optional validated Claude CLI policy contract. When
            present, Anthropic runs must enforce these tool/session/output
            semantics instead of PDD's broad default permission mode.

    Returns:
        AgenticTaskResult(success, output_text, cost_usd, provider_used, usage).
        Four-value unpacking remains supported for legacy callers; structured
        consumers can read ``result.usage`` or ``result[4]``.
    """
    normalized_claude_policy = (
        validate_claude_policy(
            claude_policy,
            interactive=_claude_code_interactive_enabled(os.environ),
        )
        if claude_policy is not None
        else None
    )

    # get_agent_provider_preference() must be called first: for
    # PDD_AGENTIC_PROVIDER=antigravity it sets PDD_GOOGLE_CLI=agy as a side
    # effect, which get_available_agents() then reads to evaluate auth correctly.
    provider_pref = get_agent_provider_preference()
    agents = get_available_agents()

    # Filter agents based on preference order
    candidates = [p for p in provider_pref if p in agents]
    if normalized_claude_policy is not None:
        if "anthropic" not in candidates:
            raise AgenticUnsupportedSemanticsError(
                "claude_policy requires Anthropic/Claude execution; no Anthropic "
                "agent is available to enforce the requested policy"
            )
        candidates = ["anthropic"]

    if not candidates:
        msg = "No agent providers are available (check CLI installation and API keys)"
        if not quiet:
            console.print(f"[bold red]{msg}[/bold red]")
        return AgenticTaskResult(False, msg, 0.0, "", None)

    effective_timeout = timeout if timeout is not None else DEFAULT_TIMEOUT_SECONDS
    effective_deadline = deadline if deadline is not None else get_job_deadline()
    task_start_time = time.time()
    # Issue #902: Cap total time across all providers to prevent 150min burn
    aggregate_deadline = task_start_time + (2 * effective_timeout)

    # Create a unique temp file for the prompt
    prompt_filename = f".agentic_prompt_{uuid.uuid4().hex[:8]}.txt"
    prompt_path = cwd / prompt_filename

    # Inject user feedback from GitHub issue comments (set by GitHub App executor)
    user_feedback = os.environ.get("PDD_USER_FEEDBACK")
    feedback_section = ""
    if user_feedback:
        feedback_section = (
            "\n\n## User Feedback\n"
            "The user provided the following feedback from a previous execution attempt. "
            "Factor this into your response:\n"
            f"{user_feedback}\n"
        )

    steering_section = ""
    if steers:
        steering_section = "\n\n## Steered user input (mid-run)\n"
        steering_section += (
            "The following comments arrived during this run. Factor them into this step:\n"
        )
        for steer in steers:
            steering_section += (
                f"- @{steer.author} ({steer.comment_id}): "
                f"{_steer_body_for_llm(steer.body)}\n"
            )

    full_instruction = (
        f"{instruction}{feedback_section}{steering_section}\n\n"
        "You have full file access to explore and modify files as needed."
    )

    try:
        # Write prompt to file
        with open(prompt_path, "w", encoding="utf-8") as f:
            f.write(full_instruction)

        filesystem_snapshot: Optional[_FilesystemPolicySnapshot] = None
        pdd_owned_log_signatures: Dict[Path, str] = {}
        if _claude_policy_has_filesystem_roots(normalized_claude_policy):
            filesystem_snapshot = _take_filesystem_policy_snapshot(
                cwd,
                normalized_claude_policy or {},
            )
            if filesystem_snapshot.errors:
                detail = _format_audit_paths(filesystem_snapshot.errors)
                return AgenticTaskResult(
                    False,
                    "Filesystem policy audit failed before provider run; "
                    f"refusing to execute: {detail}",
                    0.0,
                    "",
                    None,
                )

        provider_errors: List[str] = []

        for provider in candidates:
            if verbose:
                console.print(f"[dim]Attempting provider: {provider} for task '{label}'[/dim]")

            # Issue #902: Check aggregate budget before starting new provider
            if time.time() > aggregate_deadline:
                if verbose:
                    console.print(f"[yellow]Aggregate step timeout exceeded. Skipping {provider}.[/yellow]")
                break

            last_output = ""
            deadline_exhausted = False
            # Issue #1376 codex round 4: tracks "ANY attempt was logged inline
            # for this provider". Stays True once set — must NOT reset per
            # attempt, because a budget-skipped attempt 2 after a logged
            # attempt 1 would otherwise let the bottom block re-log attempt
            # 1's stale data as a fake second row. Round-2 inline logging
            # already covers per-attempt records (success, FP, and failure),
            # so the bottom block now only needs to fire when zero attempts
            # ran for this provider (budget exhausted before first attempt).
            any_attempt_logged_inside = False
            # Issue #1376 P2: actual model from the last attempt's response
            # (used by both inside-loop logs and the bottom failure log).
            actual_model: Optional[str] = None
            effective_model: Optional[str] = _get_provider_model(provider)
            for attempt in range(1, max_retries + 1):
                # Deadline-aware budget check before each attempt
                now = time.time()
                budgets = []
                if effective_deadline is not None:
                    budgets.append(effective_deadline - now - JOB_TIMEOUT_MARGIN_SECONDS)
                # Issue #902: Honor aggregate step budget
                budgets.append(aggregate_deadline - now)
                
                remaining = min(budgets)
                if remaining < MIN_ATTEMPT_TIMEOUT_SECONDS:
                    if verbose:
                        console.print(
                            f"[yellow]Budget exhausted "
                            f"({remaining:.0f}s remaining < {MIN_ATTEMPT_TIMEOUT_SECONDS}s min). "
                            f"Skipping attempt {attempt}.[/yellow]"
                        )
                    deadline_exhausted = True
                    break
                
                attempt_timeout = min(effective_timeout, remaining)

                if verbose and attempt > 1:
                    console.print(f"[dim]Retry {attempt}/{max_retries} for {provider} (task: {label})[/dim]")

                provider_result = _run_with_provider(
                    provider, prompt_path, cwd, attempt_timeout, verbose, quiet,
                    use_playwright=use_playwright,
                    reasoning_time=reasoning_time,
                    claude_policy=normalized_claude_policy,
                )
                success = bool(provider_result[0])
                output = str(provider_result[1])
                cost = float(provider_result[2])
                actual_model = provider_result[3]
                usage = provider_result[4] if len(provider_result) > 4 else None
                last_output = output
                # Issue #1376: prefer the model the provider actually reported;
                # fall back to the requested model from env vars when the JSON
                # didn't surface one (e.g. early-error returns).
                effective_model = actual_model or _get_provider_model(provider)

                # False Positive Detection
                # Issue #249: Empty output should ALWAYS be detected as false positive,
                # regardless of cost. Claude may consume tokens running tools but produce
                # no text response, which means the task wasn't actually completed.
                # Issue #902: Error-like content with cost > 0 is also a false positive,
                # but only when the output STARTS with "Error:" (genuine terse provider
                # error response, e.g., "Error: rate limit exceeded" or a long
                # single-line CLI error).
                # Issue #1232: Substantive output that merely mentions "Error:" mid-text
                # (e.g., describing error-raising functions) must NOT be demoted. A
                # multi-paragraph findings doc that happens to start with "Error:"
                # also survives via the newline-count gate (`MAX_ERROR_RESPONSE_NEWLINES`).
                if success:
                    stripped_output = output.strip()
                    output_length = len(stripped_output)
                    # Some subscription-channel CLIs do not expose usage stats,
                    # so successful responses always return cost=0.0. Short but
                    # legitimate answers like "4", "Done", or "OK" would otherwise
                    # be demoted to false positives by the zero-cost gate. Empty
                    # output and explicit error signals are still rejected before
                    # this bypass can mark them valid.
                    provider_lacks_cost_reporting = (
                        provider == "google" and _get_google_cli_name() == "agy"
                    ) or (
                        provider == "anthropic"
                        and _claude_code_interactive_enabled()
                    )
                    is_false_positive = (
                        output_length == 0 or  # Empty output is always a false positive
                        (
                            not provider_lacks_cost_reporting
                            and cost == 0.0
                            and output_length < MIN_VALID_OUTPUT_LENGTH
                        ) or  # Zero cost with short output (skipped for CLIs with no usage reporting)
                        (
                            cost > 0.0
                            and stripped_output.startswith("Error:")
                            and stripped_output.count("\n") < MAX_ERROR_RESPONSE_NEWLINES
                            and output_length < 4000
                        )  # Issue #902/#1232: leading "Error:" with few newlines (terse error, not findings doc)
                    )

                    if is_false_positive:
                        if not quiet:
                            console.print(f"[yellow]Provider '{provider}' returned false positive (attempt {attempt}/{max_retries})[/yellow]")
                        # Issue #1376: log false-positive provider replies so the
                        # heuristic-rejection path leaves the same audit trail
                        # as outright failures (was previously silent).
                        _record_pdd_owned_log_signature(
                            _log_agentic_interaction(
                                label=label,
                                prompt=full_instruction,
                                response=output,
                                cost=cost,
                                provider=provider,
                                success=False,
                                duration=time.time() - task_start_time,
                                cwd=cwd,
                                model=effective_model,
                                false_positive=True,
                            ),
                            pdd_owned_log_signatures,
                            filesystem_snapshot,
                        )
                        any_attempt_logged_inside = True
                        # Multi-provider configs (default): fall through to the
                        # next provider instead of burning retries on the same
                        # known-broken one.
                        # Single-provider configs (cloud one-session sync runs
                        # anthropic-only) have nowhere to fall through to —
                        # an immediate `break` means zero retries and one
                        # transient empty response fails the whole sync. Retry
                        # on the same provider with backoff up to max_retries.
                        if len(candidates) == 1 and attempt < max_retries:
                            base_backoff = retry_delay * (2 ** (attempt - 1))
                            jitter = random.uniform(0, retry_delay)
                            backoff = min(base_backoff + jitter, MAX_RETRY_DELAY)
                            # Issue #1384: when the false-positive payload
                            # itself looks like a 429 ("Error: api_error_status:
                            # 429 rate limit exceeded"), apply the same 60s
                            # floor as the not-success retry path below.
                            # Without this, a 429 surfaced through the
                            # successful-but-Error-prefixed path retries on
                            # the default 1s/2s/4s schedule, which burns the
                            # retry budget before the per-minute window clears.
                            if _is_rate_limited(stripped_output or ""):
                                backoff = max(backoff, RATE_LIMIT_BACKOFF_FLOOR)
                                if verbose:
                                    console.print(
                                        f"[yellow]Rate-limited (HTTP 429); raising "
                                        f"backoff floor to {RATE_LIMIT_BACKOFF_FLOOR:.0f}s[/yellow]"
                                    )
                            if not quiet:
                                console.print(f"[dim]Single-provider config: retrying in {backoff:.0f}s...[/dim]")
                            time.sleep(backoff)
                            continue
                        break
                    else:
                        # Check for suspicious files (C, E, T)
                        suspicious = []
                        for name in ["C", "E", "T"]:
                            if (cwd / name).exists():
                                suspicious.append(name)

                        if suspicious:
                            console.print(f"[bold red]SUSPICIOUS FILES DETECTED: {', '.join(['- ' + s for s in suspicious])}[/bold red]")

                        changed_files, filesystem_violation = _audit_filesystem_policy(
                            cwd,
                            normalized_claude_policy,
                            filesystem_snapshot,
                            pdd_owned_log_signatures,
                        )
                        if filesystem_violation is not None:
                            _log_agentic_interaction(
                                label=label,
                                prompt=full_instruction,
                                response=filesystem_violation,
                                cost=cost,
                                provider=provider,
                                success=False,
                                duration=time.time() - task_start_time,
                                cwd=cwd,
                                model=effective_model,
                                include_bodies=verbose,
                            )
                            return AgenticTaskResult(
                                False,
                                filesystem_violation,
                                cost,
                                provider,
                                usage,
                                changed_files=changed_files,
                            )

                        # Issue #1376: always emit a summary record so the audit
                        # log answers "which provider/model produced step N?"
                        # without --verbose. Full prompt+response bodies stay
                        # behind verbose to avoid bloating the file with the
                        # same large prompt repeated across every step.
                        _log_agentic_interaction(
                            label=label,
                            prompt=full_instruction,
                            response=output,
                            cost=cost,
                            provider=provider,
                            success=True,
                            duration=time.time() - task_start_time,
                            cwd=cwd,
                            model=effective_model,
                            include_bodies=verbose,
                        )
                        return AgenticTaskResult(
                            True,
                            output,
                            cost,
                            provider,
                            usage,
                            changed_files=changed_files,
                        )

                # Issue #902: Skip retries for permanent errors (auth, parameters)
                # Issue #1376 codex round 2: log each failed attempt inside
                # the loop so the audit trail captures every retry, not just
                # the final one. Without this, max_retries=3 with 3 failures
                # produces only one JSONL row — exactly the audit-trail gap
                # this PR set out to close.
                if not success:
                    _record_pdd_owned_log_signature(
                        _log_agentic_interaction(
                            label=label,
                            prompt=full_instruction,
                            response=output,
                            cost=cost,
                            provider=provider,
                            success=False,
                            duration=time.time() - task_start_time,
                            cwd=cwd,
                            model=effective_model,
                        ),
                        pdd_owned_log_signatures,
                        filesystem_snapshot,
                    )
                    any_attempt_logged_inside = True

                permanent_class = (
                    _classify_permanent_error(output) if not success else None
                )
                if permanent_class is not None:
                    # Issue #814: emit a default-mode (non-verbose) diagnostic so
                    # the user sees which provider was skipped and why, instead
                    # of the workflow silently advancing to the next provider.
                    # Suppressed under quiet=True so callers honoring the quiet
                    # contract (e.g. Issue #813 paths) stay silent on stdout.
                    #
                    # The line carries the stable classification token (e.g.
                    # ``billing/credit-exhaustion``, ``auth``, ``quota``) — NOT
                    # the raw provider stderr — so credentials echoed in the
                    # body cannot leak to stdout/CI logs and so no Rich-markup
                    # escaping of untrusted text is required. The full output
                    # is still captured in the JSONL audit log above and is
                    # available via ``--verbose``.
                    if not quiet:
                        console.print(
                            f"[yellow]Provider {provider} reported a permanent error "
                            f"({permanent_class}); skipping retries. "
                            f"Use --verbose for the full provider output.[/yellow]"
                        )
                    break

                # Failed - retry with backoff if attempts remain
                if attempt < max_retries:
                    # Issue #902: Exponential backoff with additive jitter and cap
                    # Delay = base * 2^(attempt-1) + random_jitter
                    base_backoff = retry_delay * (2 ** (attempt - 1))
                    jitter = random.uniform(0, retry_delay)
                    backoff = min(base_backoff + jitter, MAX_RETRY_DELAY)
                    # If the previous attempt was rate-limited, raise the
                    # floor so we wait long enough for the limit to clear
                    # instead of burning the next attempt on the same 429.
                    if _is_rate_limited(last_output or ""):
                        backoff = max(backoff, RATE_LIMIT_BACKOFF_FLOOR)
                        if verbose:
                            console.print(
                                f"[yellow]Rate-limited (HTTP 429); raising "
                                f"backoff floor to {RATE_LIMIT_BACKOFF_FLOOR:.0f}s[/yellow]"
                            )

                    if verbose:
                        console.print(f"[dim]Waiting {backoff:.1f}s before retry...[/dim]")
                    time.sleep(backoff)

            # All retries exhausted (or deadline budget exhausted) for this provider
            provider_errors.append(f"{provider}: {last_output[:MAX_ERROR_SNIPPET_LENGTH]}")
            # Issue #1541: emit a stable, secret-safe provider-limit marker so
            # PDD Cloud can schedule a retry after the reset window without
            # scraping raw provider stderr. This post-retry-loop seam fires at
            # most once per provider (the credential-limit branch breaks here;
            # generic 429s reach here only after exhausting retries — a 429 that
            # recovers returns earlier and emits nothing). Only real
            # credential-limit / generic-429 classifications produce a marker;
            # auth/quota/etc. produce none. Deliberately NOT quiet-gated: the
            # cloud scheduler needs the marker even when human diagnostics are
            # suppressed.
            _emit_provider_limit_marker(provider, last_output)
            if verbose:
                console.print(f"[yellow]Provider {provider} failed after {max_retries} attempts: {last_output}[/yellow]")
            # Issue #1072 / #1376 (codex round 2): inline per-attempt logging
            # above already emits one record per provider attempt (success,
            # FP, or failure). This bottom block now only covers the
            # budget-exhausted-before-first-attempt case where no inline log
            # ran — any_attempt_logged_inside stays False from
            # initialization in that path, and we still want a record
            # documenting the provider was skipped.
            if not any_attempt_logged_inside:
                _log_agentic_interaction(
                    label=label,
                    prompt=full_instruction,
                    response=last_output,
                    cost=0.0,
                    provider=provider,
                    success=False,
                    duration=time.time() - task_start_time,
                    cwd=cwd,
                    model=effective_model,
                )
            # If deadline was exhausted, don't try other providers either
            if deadline_exhausted or time.time() > aggregate_deadline:
                break

        return AgenticTaskResult(
            False,
            f"All agent providers failed: {'; '.join(provider_errors)}",
            0.0,
            "",
            None,
        )

    finally:
        # Cleanup prompt file
        if prompt_path.exists():
            try:
                os.remove(prompt_path)
            except OSError:
                pass


import logging as _logging
_scope_guard_logger = _logging.getLogger(__name__ + ".scope_guard")


def _revert_out_of_scope_changes(
    cwd: Path,
    allowed_paths: set[Path],
) -> List[Path]:
    """
    Revert any git-tracked file changes outside the allowed set.

    After an agentic task, this function detects deletions and modifications
    to files not in *allowed_paths* and restores them to their ``HEAD`` state.

    Skips silently when *cwd* is not a git repo, when git is unavailable,
    or when none of the *allowed_paths* reside under *cwd*.

    Args:
        cwd: Root of the git repository.
        allowed_paths: Set of resolved absolute paths the agent is permitted
            to modify.

    Returns:
        List of paths that were reverted.
    """
    cwd_str = str(cwd.resolve())
    if not any(str(p).startswith(cwd_str) for p in allowed_paths):
        return []
    # Use the structured ``--porcelain=v1 -z`` parser so staged renames
    # surface BOTH the new and old paths as discrete fields. The earlier
    # text-mode ``line[3:]`` parser collapsed renames into a literal
    # ``"old -> new"`` path that ``git checkout HEAD -- <fake>`` never
    # matched, so an out-of-scope rename silently survived the guard.
    # See issue #1080.
    from pdd.git_porcelain import parse_porcelain_z  # local import: avoid cycles
    try:
        result = subprocess.run(
            ["git", "-C", str(cwd), "status", "--porcelain=v1", "-z", "-uno"],
            capture_output=True, timeout=30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as exc:
        _scope_guard_logger.warning("Scope guard: git status failed: %s", exc)
        return []
    if result.returncode != 0:
        _scope_guard_logger.warning(
            "Scope guard: git status returned %d: %s",
            result.returncode, result.stderr.decode("utf-8", errors="replace").strip(),
        )
        return []
    entries = parse_porcelain_z(result.stdout)
    reverted: List[Path] = []
    paths_to_checkout: List[str] = []  # paths to restore from HEAD
    paths_to_reset: List[str] = []     # paths to unstage from the index
    paths_to_unlink: List[str] = []    # paths to remove from the worktree
    for entry in entries:
        new_resolved = (cwd / entry.path).resolve()
        is_rename = entry.old_path is not None and "R" in entry.status
        is_copy = entry.old_path is not None and "C" in entry.status
        if is_rename:
            old_resolved = (cwd / entry.old_path).resolve()
            in_scope = (
                new_resolved in allowed_paths
                and old_resolved in allowed_paths
            )
        elif is_copy:
            in_scope = new_resolved in allowed_paths
        else:
            in_scope = new_resolved in allowed_paths
        if in_scope:
            continue
        if is_rename:
            # Rename: restore old path from HEAD, unstage + delete new path.
            paths_to_checkout.append(entry.old_path)
            paths_to_reset.extend([entry.path, entry.old_path])
            paths_to_unlink.append(entry.path)
            reverted.append(old_resolved)
            reverted.append(new_resolved)
        elif is_copy:
            # Copy: only the destination is changed. The source old_path
            # is informational and must not be reset, checked out, or
            # reported as reverted.
            paths_to_reset.append(entry.path)
            paths_to_unlink.append(entry.path)
            reverted.append(new_resolved)
        else:
            paths_to_checkout.append(entry.path)
            reverted.append(new_resolved)
    if not reverted:
        return reverted
    try:
        if paths_to_reset:
            subprocess.run(
                ["git", "-C", str(cwd), "reset", "HEAD", "--"] + paths_to_reset,
                capture_output=True, timeout=30,
            )
        if paths_to_checkout:
            subprocess.run(
                ["git", "-C", str(cwd), "checkout", "HEAD", "--"] + paths_to_checkout,
                capture_output=True, timeout=30,
            )
        for rel in paths_to_unlink:
            try:
                (cwd / rel).unlink()
            except FileNotFoundError:
                pass
            except OSError as exc:
                _scope_guard_logger.warning(
                    "Scope guard: failed to remove %s: %s", rel, exc,
                )
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as exc:
        _scope_guard_logger.warning(
            "Scope guard: git revert failed for %d file(s): %s",
            len(reverted), exc,
        )
        reverted.clear()
    else:
        if reverted:
            _scope_guard_logger.info(
                "Scope guard reverted %d out-of-scope file(s): %s",
                len(reverted),
                ", ".join(str(p.name) for p in reverted[:10]),
            )
    return reverted

_CLAUDE_OAUTH_PROBE_TIMEOUT_SECONDS = 10
_ANTHROPIC_KEY_STRIP_NOTICE_LOGGED: Dict[str, bool] = {}


@functools.lru_cache(maxsize=1)
def _probe_claude_auth_status() -> Dict[str, Any]:
    """Cached `claude auth status` output for OAuth detection (Issue #813).

    Returns ``{}`` on any failure (CLI missing, timeout, non-zero exit, parse
    error, missing subcommand on older Claude Code). Callers must treat that as
    'no OAuth detected' and leave the API key in place.

    Probe runs with ANTHROPIC_API_KEY/ANTHROPIC_AUTH_TOKEN popped to avoid an
    env-supplied key shadowing the OAuth signal in the JSON payload, and uses
    ``subprocess.run`` directly (not ``_subprocess_run``) so it isn't
    intercepted by mocks for the main provider call site.
    """
    cli_path = _find_cli_binary("claude")
    if not cli_path:
        return {}

    probe_env = os.environ.copy()
    probe_env.pop("ANTHROPIC_API_KEY", None)
    probe_env.pop("ANTHROPIC_AUTH_TOKEN", None)

    # Claude Code documents `claude auth status` as the JSON-producing probe.
    # Some versions accepted/required `--json`, while others reject that flag.
    # Try the documented shape first, then fall back to the flag form so either
    # CLI version can still report the stored OAuth credential.
    probe_commands = (
        [cli_path, "auth", "status"],
        [cli_path, "auth", "status", "--json"],
    )

    for command in probe_commands:
        try:
            result = subprocess.run(
                command,
                env=probe_env,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                timeout=_CLAUDE_OAUTH_PROBE_TIMEOUT_SECONDS,
                check=False,
            )
        except (subprocess.TimeoutExpired, OSError):
            return {}

        if result.returncode != 0:
            continue

        try:
            data = json.loads((result.stdout or "").strip())
        except json.JSONDecodeError:
            continue

        if isinstance(data, dict):
            return data

    return {}


_CLAUDE_OAUTH_AUTH_METHODS = frozenset({
    # Local interactive `claude auth login` — keychain-backed Max/Pro OAuth.
    "claude.ai",
    # Env-supplied OAuth (CLAUDE_CODE_OAUTH_TOKEN) — used by the cloud
    # GitHub App executor's waterfall, where the token comes from
    # Secret Manager rather than a keychain login.
    #
    # Caveat: `claude auth status` does not validate the token, so a
    # bogus or stale CLAUDE_CODE_OAUTH_TOKEN still reports loggedIn:true and
    # will trigger our pop. We accept this — the resulting "invalid OAuth
    # token" error is more actionable than the silent shadowing the pop
    # protects against. The cloud waterfall isolates each attempt to one
    # credential type, so the conjunction (bogus token + valid API key)
    # shouldn't arise in production.
    "oauth_token",
})


def _claude_has_oauth_login() -> bool:
    """True when Claude Code has a usable first-party OAuth credential.

    Drives the ANTHROPIC_API_KEY pop in ``_run_with_provider`` (Issue #813).
    ``subscriptionType`` is intentionally not required: API-credit OAuth users
    leave that field null but still want OAuth to win over a stale env key.

    Both keychain OAuth (``authMethod == "claude.ai"``) and env OAuth
    (``authMethod == "oauth_token"``, e.g. ``CLAUDE_CODE_OAUTH_TOKEN``) count
    as OAuth here. Empirical: with both ``CLAUDE_CODE_OAUTH_TOKEN`` and
    ``ANTHROPIC_API_KEY`` set under ``CI=1`` the API key still wins the
    real call (Issue #813's shadowing pattern), so the cloud waterfall
    pattern needs the same protection as local Max users.

    Bedrock/Vertex routes report ``apiProvider != "firstParty"`` and are
    correctly excluded here.
    """
    info = _probe_claude_auth_status()
    return (
        bool(info.get("loggedIn"))
        and info.get("authMethod") in _CLAUDE_OAUTH_AUTH_METHODS
        and info.get("apiProvider") == "firstParty"
    )


def _strip_anthropic_creds_for_claude_subprocess(
    env: Dict[str, str], *, verbose: bool = False, quiet: bool = False
) -> bool:
    """Pop stale ANTHROPIC_API_KEY / ANTHROPIC_AUTH_TOKEN when claude has OAuth.

    Issue #813: PDD always sets ``CI=1`` to keep the claude CLI non-interactive.
    Under ``CI=1``, Claude Code prefers ``ANTHROPIC_API_KEY`` over the user's
    stored OAuth credential, so a depleted key in the parent shell silently
    routes every call to the API tier and fails with 'Credit balance is too
    low' even though ``claude auth status`` still reports the Max account.

    Pop only when an OAuth login is confirmed, so users without OAuth (pure
    API-key setups, including the GitHub App executor that injects keys from
    Secret Manager) keep working unchanged.

    Returns True iff something was popped (for tests and the one-shot notice).

    Provider-scope note: codex/gemini have analogous shadowing risks
    (``codex login status``, ``_has_gemini_oauth_credentials``). They are out
    of scope for this fix; extend here when the symptom is empirically
    reproduced for those providers.
    """
    if env.get("CLAUDE_CODE_USE_BEDROCK") or env.get("CLAUDE_CODE_USE_VERTEX"):
        return False

    # Match common truthy spellings only ("1", "true", "yes", "on" — case-
    # insensitive). Bare-presence checks misread `PDD_KEEP_ANTHROPIC_API_KEY=0`
    # or `=false` as opt-in, defeating the fix in environments where the var
    # is set to a disabling value.
    if (env.get("PDD_KEEP_ANTHROPIC_API_KEY") or "").strip().lower() in {
        "1", "true", "yes", "on",
    }:
        return False

    if not (env.get("ANTHROPIC_API_KEY") or env.get("ANTHROPIC_AUTH_TOKEN")):
        return False

    if not _claude_has_oauth_login():
        return False

    env.pop("ANTHROPIC_API_KEY", None)
    env.pop("ANTHROPIC_AUTH_TOKEN", None)

    # ``quiet`` suppresses both the one-shot notice and the verbose echo to
    # honor the orchestrator's "no non-error output" contract — scripted
    # workflows redirect / parse stdout and a stray dim line breaks them.
    if quiet:
        return True

    if not _ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.get("done"):
        console.print(
            "[dim]Issue #813: dropped ANTHROPIC_API_KEY/AUTH_TOKEN from claude "
            "subprocess env — local OAuth login detected. Set "
            "PDD_KEEP_ANTHROPIC_API_KEY=1 to override.[/dim]"
        )
        _ANTHROPIC_KEY_STRIP_NOTICE_LOGGED["done"] = True
    elif verbose:
        console.print(
            "[dim]Issue #813: dropped ANTHROPIC_API_KEY/AUTH_TOKEN from claude "
            "subprocess env (OAuth detected).[/dim]"
        )
    return True


def _subprocess_run(cmd, *, cwd=None, env=None, input=None, capture_output=False,
                    text=False, timeout=None, start_new_session=False, **kwargs):
    """Wrapper around subprocess that uses Popen for proper process group cleanup.

    Provides a subprocess.run-compatible interface but uses Popen internally
    so we can reliably kill the process group on timeout (Issue #830).
    """
    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        env=env,
        stdin=subprocess.PIPE if input is not None or capture_output else None,
        stdout=subprocess.PIPE if capture_output else None,
        stderr=subprocess.PIPE if capture_output else None,
        text=text,
        start_new_session=start_new_session,
    )
    try:
        stdout, stderr = proc.communicate(input=input, timeout=timeout)
    except subprocess.TimeoutExpired:
        if start_new_session:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (ProcessLookupError, OSError):
                pass
        proc.kill()
        proc.wait(timeout=5)
        raise

    result = subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)
    return result


def _claude_code_interactive_enabled(env: Optional[Dict[str, str]] = None) -> bool:
    """Return True when Anthropic provider should use interactive Claude Code."""
    if env is None:
        env = os.environ
    return (
        (env.get(CLAUDE_CODE_MODE_ENV) or "").strip().lower()
        == CLAUDE_CODE_INTERACTIVE_MODE
    )


def _write_claude_reply_mcp_server(server_path: Path) -> None:
    """Write a tiny stdio MCP server exposing the ``pdd_reply`` tool."""
    server_path.write_text(
        r'''#!/usr/bin/env python3
import json
import os
import sys

REPLY_PATH = os.environ["PDD_INTERACTIVE_REPLY_PATH"]
EXPECTED_JOB_ID = os.environ["PDD_INTERACTIVE_JOB_ID"]


def respond(request_id, result=None, error=None):
    message = {"jsonrpc": "2.0", "id": request_id}
    if error is not None:
        message["error"] = error
    else:
        message["result"] = result if result is not None else {}
    sys.stdout.write(json.dumps(message, separators=(",", ":")) + "\n")
    sys.stdout.flush()


def write_reply(arguments):
    job_id = str(arguments.get("job_id") or "")
    if job_id != EXPECTED_JOB_ID:
        raise ValueError("job_id does not match this PDD task")
    text = arguments.get("text")
    if text is None:
        text = ""
    payload = {
        "job_id": job_id,
        "success": bool(arguments.get("success")),
        "text": str(text),
    }
    if arguments.get("cost_usd") is not None:
        payload["cost_usd"] = arguments.get("cost_usd")
    if arguments.get("model") is not None:
        payload["model"] = str(arguments.get("model"))
    tmp_path = REPLY_PATH + ".tmp"
    with open(tmp_path, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, ensure_ascii=True)
    os.replace(tmp_path, REPLY_PATH)


TOOLS = [{
    "name": "pdd_reply",
    "description": "Return the final PDD agentic task result to the caller.",
    "inputSchema": {
        "type": "object",
        "properties": {
            "job_id": {"type": "string"},
            "success": {"type": "boolean"},
            "text": {"type": "string"},
            "cost_usd": {"type": "number"},
            "model": {"type": "string"},
        },
        "required": ["job_id", "success", "text"],
        "additionalProperties": False,
    },
}]


for raw_line in sys.stdin:
    raw_line = raw_line.strip()
    if not raw_line:
        continue
    try:
        request = json.loads(raw_line)
    except json.JSONDecodeError:
        continue
    method = request.get("method")
    request_id = request.get("id")
    if method == "initialize":
        respond(request_id, {
            "protocolVersion": "2024-11-05",
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "pdd-reply", "version": "0.1.0"},
        })
    elif method == "tools/list":
        respond(request_id, {"tools": TOOLS})
    elif method == "tools/call":
        try:
            params = request.get("params") or {}
            if params.get("name") != "pdd_reply":
                raise ValueError("unknown tool")
            write_reply(params.get("arguments") or {})
            respond(request_id, {
                "content": [{"type": "text", "text": "PDD reply recorded."}],
                "isError": False,
            })
        except Exception as exc:
            respond(request_id, {
                "content": [{"type": "text", "text": str(exc)}],
                "isError": True,
            })
    elif method == "ping":
        respond(request_id, {})
    elif method in {"notifications/initialized", "notifications/cancelled"}:
        continue
    elif request_id is not None:
        respond(request_id, {})
''',
        encoding="utf-8",
    )


def _write_claude_interactive_mcp_config(
    config_path: Path,
    server_path: Path,
    reply_path: Path,
    job_id: str,
) -> None:
    """Write a Claude Code MCP config for the temporary PDD reply server."""
    config = {
        "mcpServers": {
            "pdd": {
                "command": sys.executable,
                "args": [str(server_path)],
                "env": {
                    "PDD_INTERACTIVE_REPLY_PATH": str(reply_path),
                    "PDD_INTERACTIVE_JOB_ID": job_id,
                },
            }
        }
    }
    config_path.write_text(json.dumps(config), encoding="utf-8")


def _build_claude_interactive_command(
    *,
    cli_path: str,
    prompt_path: Path,
    config_path: Path,
    job_id: str,
    session_id: str,
    env: Dict[str, str],
    use_playwright: bool = False,
    claude_policy: Optional[ClaudePolicy] = None,
) -> List[str]:
    """Build the Claude Code interactive command without ``-p`` / JSON mode."""
    normalized_policy = (
        validate_claude_policy(claude_policy, interactive=True)
        if claude_policy is not None
        else None
    )
    cmd = [
        cli_path,
        "--session-id", session_id,
        "--mcp-config", str(config_path),
        "--strict-mcp-config",
    ]
    if normalized_policy is not None:
        interactive_policy = {
            **normalized_policy,
            "allowedTools": _interactive_allowed_tools(
                normalized_policy["allowedTools"]
            ),
        }
        _append_claude_policy_args(cmd, interactive_policy)
    elif use_playwright:
        cmd.extend([
            "--allowedTools",
            "Bash,Read,Write,mcp__pdd__pdd_reply",
        ])
    else:
        cmd.append("--dangerously-skip-permissions")

    claude_model = env.get("CLAUDE_MODEL")
    if claude_model:
        cmd.extend(["--model", claude_model])

    if normalized_policy is not None and normalized_policy["allowedTools"] is None:
        try:
            instruction_text = prompt_path.read_text(encoding="utf-8")
        except OSError:
            instruction_text = f"Read the file {prompt_path.name} for your full instructions."
        instruction_prefix = f"Execute these instructions:\n\n{instruction_text}\n\n"
    else:
        instruction_prefix = (
            f"Read the file {prompt_path.name} for your full instructions and execute them. "
        )
    json_instruction = (
        "The caller requires JSON output; return JSON text through pdd_reply. "
        if normalized_policy is not None
        else ""
    )
    cmd.append(
        instruction_prefix +
        f"When finished, call the MCP tool pdd_reply with job_id={job_id!r}, "
        "success=true or false, and text set to the final response for PDD. "
        f"{json_instruction}"
        "Do not stop until pdd_reply succeeds."
    )
    return cmd


def _find_claude_interactive_session_file(
    session_id: str,
    env: Dict[str, str],
    wait_seconds: float = 2.0,
) -> Optional[Path]:
    """Locate Claude Code's JSONL transcript for the given session."""
    home = Path(env.get("HOME") or str(Path.home()))
    projects_dir = home / ".claude" / "projects"
    if not projects_dir.exists():
        return None

    deadline = time.time() + max(0.0, wait_seconds)
    while True:
        matches = list(projects_dir.rglob(f"{session_id}.jsonl"))
        if matches:
            return matches[0]
        if time.time() >= deadline:
            return None
        time.sleep(0.1)


def _estimate_claude_interactive_session_cost(
    session_id: str,
    env: Dict[str, str],
) -> Tuple[float, Optional[str], AgenticUsage]:
    """Estimate interactive Claude cost from the persisted session transcript."""
    usage, latest_model = _extract_claude_interactive_session_usage(session_id, env)
    if not usage:
        return 0.0, latest_model, None

    total_cost = 0.0
    for record in usage.get("claude", []):
        model_name = str(record.get("model") or latest_model or "claude-sonnet")
        total_cost += _calculate_anthropic_cost(
            {
                "usage": {
                    "input_tokens": record.get("input_tokens", 0),
                    "output_tokens": record.get("output_tokens", 0),
                    "cache_read_input_tokens": record.get("cached_input_tokens", 0),
                    "cache_creation_input_tokens": record.get(
                        "cache_creation_input_tokens",
                        0,
                    ),
                },
                "modelUsage": {model_name: {}},
            }
        )

    return total_cost, latest_model, usage


def _extract_claude_interactive_session_usage(
    session_id: str,
    env: Dict[str, str],
) -> Tuple[AgenticUsage, Optional[str]]:
    """Extract JSON-serializable Claude usage from an interactive transcript."""
    session_file = _find_claude_interactive_session_file(session_id, env)
    if session_file is None:
        return None, None

    per_request_usage: Dict[str, Dict[str, Any]] = {}
    latest_model: Optional[str] = None
    try:
        raw_lines = session_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None, None

    for raw_line in raw_lines:
        try:
            item = json.loads(raw_line)
        except json.JSONDecodeError:
            continue
        if item.get("type") != "assistant":
            continue
        # Synthetic error turns (auth failure, usage cap, transient API error)
        # carry the ``<synthetic>`` model and zero usage — never billable and
        # not a real model name. Skip them so they neither pollute the reported
        # model (Issue #1365) nor add empty per-request buckets.
        if _claude_assistant_row_is_synthetic_error(item):
            continue

        request_id = item.get("requestId")
        message = item.get("message") or {}
        model = message.get("model") or item.get("advisorModel")
        if isinstance(model, str) and model:
            latest_model = model

        # Claude writes multiple assistant rows per request (e.g. thinking,
        # tool_use, final text) with the same requestId and usage totals.
        # Count each request exactly once to avoid double-charging.
        if not request_id or request_id in per_request_usage:
            continue

        usage = message.get("usage")
        if not isinstance(usage, dict):
            continue
        per_request_usage[request_id] = {
            "model": model,
            "usage": usage,
        }

    if not per_request_usage:
        return None, latest_model

    usage_keys = (
        "input_tokens",
        "output_tokens",
        "cache_read_input_tokens",
        "cache_creation_input_tokens",
    )
    usage_by_model: Dict[str, Dict[str, int]] = {}
    for record in per_request_usage.values():
        model_name = str(record.get("model") or latest_model or "claude-sonnet")
        usage = record.get("usage") or {}
        bucket = usage_by_model.setdefault(
            model_name,
            {key: 0 for key in usage_keys},
        )
        for key in usage_keys:
            try:
                bucket[key] += int(usage.get(key, 0) or 0)
            except (TypeError, ValueError):
                continue

    usage_records: List[Dict[str, Any]] = []
    for model_name, usage in usage_by_model.items():
        usage_records.append(
            {
                "model": model_name,
                "input_tokens": int(usage.get("input_tokens", 0)),
                "output_tokens": int(usage.get("output_tokens", 0)),
                "cached_input_tokens": int(usage.get("cache_read_input_tokens", 0)),
                "cache_creation_input_tokens": int(
                    usage.get("cache_creation_input_tokens", 0)
                ),
            }
        )

    return {"claude": usage_records}, latest_model


def _claude_assistant_row_is_synthetic_error(item: Dict[str, Any]) -> bool:
    """True when an ``assistant`` transcript row is a synthetic error turn.

    Claude Code emits these for a turn it could not complete (auth failure,
    usage cap, transient API error). They carry ``isApiErrorMessage`` and the
    ``<synthetic>`` model — never produced for genuine model output, which is
    what makes them a structural discriminator that survives the Issue #1340
    false-positive class (ordinary output that merely *prints* auth prose).

    ``isApiErrorMessage`` sits at the row top level today; the ``<synthetic>``
    model sits under ``message``. Both locations are checked so the detector
    tolerates minor transcript-schema drift across Claude Code versions.
    """
    message = item.get("message") or {}
    if item.get("isApiErrorMessage") is True or message.get("isApiErrorMessage") is True:
        return True
    return message.get("model") == CLAUDE_SYNTHETIC_MODEL


# Login markers inside a synthetic error turn — distinguishes a genuine
# logged-out / revoked-OAuth failure ("please run /login") from a non-login
# auth failure (bad API key, 403 model entitlement) that also classifies as the
# "auth" class. The returned message is tailored so a non-login auth failure is
# not mislabeled as oauth/login (which would wrongly tell the caller to rotate
# OAuth / run /login).
_INTERACTIVE_LOGIN_MARKER_PATTERN: str = r"not\s+logged\s+in|please\s+run\s+/login"


def _interactive_auth_failure_message(detail: str) -> str:
    """Deterministic, PDD-owned, credential-safe message for an auth failure.

    Re-classifies as ``oauth/login`` only when the synthetic turn actually
    indicates a login problem; otherwise as the generic ``auth`` class. Never
    echoes ``detail`` itself (raw provider text can quote credentials).
    """
    if re.search(_INTERACTIVE_LOGIN_MARKER_PATTERN, detail.lower()):
        return (
            "Claude Code interactive session is not logged in (oauth/login): "
            "please run /login. PDD detected a synthetic authentication-failure "
            "turn in the session transcript with no usable reply; fast-failing so "
            "the caller can rotate credentials instead of waiting for the full "
            "interactive step timeout."
        )
    return (
        "Claude Code interactive session authentication failed (auth). PDD "
        "detected a synthetic authentication-failure turn in the session "
        "transcript with no usable reply; fast-failing so the caller can advance "
        "instead of waiting for the full interactive step timeout."
    )


def _interactive_credential_limit_message(detail: str) -> str:
    """Deterministic, PDD-owned, credential-safe message for an interactive
    subscription/usage cap (``credential-limit``).

    Symmetric to :func:`_interactive_auth_failure_message`. When the latest
    assistant turn is a synthetic ``credential-limit`` failure — the Claude Code
    subscription hit its weekly/usage limit mid-run ("You've hit your limit ·
    resets <time>") — the PTY loop fast-fails with this message instead of
    parking until the per-step timeout. The stable ``credential-limit`` token
    lets the pdd_cloud OAuth-token waterfall force-rotate to a fresh credential
    (the reset window is hours-to-days, so retrying the same token is futile).
    Kept deliberately distinct from an API-tier 429 so this never lands on the
    60s rate-limit retry floor. Never echoes ``detail`` (raw provider text can
    quote the reset time / account info).
    """
    return (
        "Claude Code interactive session reached its Claude subscription cap — "
        "you've hit your limit · resets at a provider-set time (PDD "
        "credential-limit). PDD detected a synthetic credential-limit turn in "
        "the session transcript with no usable reply; fast-failing so the caller "
        "rotates to the next OAuth credential instead of waiting for the full "
        "interactive step timeout."
    )


def _claude_assistant_row_text(message: Dict[str, Any]) -> str:
    """Concatenate the text parts of an assistant message's content."""
    return " ".join(
        part.get("text", "")
        for part in (message.get("content") or [])
        if isinstance(part, dict) and part.get("type") == "text"
    )


def _auth_state_after_row(state: Optional[str], item: Dict[str, Any]) -> Optional[str]:
    """Fold one transcript row into the running terminal-auth state (Issue #1365).

    Returns the auth-failure message iff this row makes the session's latest
    ``assistant`` turn a terminal synthetic auth failure. The latest assistant
    turn wins: a genuine model turn supersedes an earlier error and returns
    ``None``. A synthetic auth/oauth-login turn arms the auth fast-fail; a
    synthetic ``credential-limit`` turn (Claude subscription/usage cap) arms the
    credential-limit fast-fail so the caller rotates credentials. A transient
    synthetic error (overload/network/timeout) still returns ``None`` (the
    caller keeps its retry/timeout fallback).
    Non-assistant rows (including the per-retry ``system``/``api_error`` rows)
    leave the state unchanged, so an in-flight, still-retrying turn is never
    killed mid-retry.

    Captured against Claude Code CLI 2.1.161. The signal degrades gracefully: if
    a future CLI surfaces auth failures only via system rows, changes the
    ``<synthetic>`` marker, or alters the content shape, this returns ``None``
    and the caller falls back to the original timeout (no false positive). The
    real-CLI manual validation in the PR re-confirms the shape.
    """
    if item.get("type") != "assistant":
        return state
    if not _claude_assistant_row_is_synthetic_error(item):
        # Genuine model output: authentication worked; supersede any prior error.
        return None
    text = _claude_assistant_row_text(item.get("message") or {})
    classification = _classify_permanent_error(text)
    if classification in ("auth", "oauth/login"):
        return _interactive_auth_failure_message(text)
    if classification == "credential-limit":
        # A mid-run subscription/usage cap parks the PTY at the prompt the same
        # way an auth failure does; arm a credential-limit fast-fail so the
        # caller rotates to the next OAuth token instead of burning the step
        # timeout (the cloud waterfall force-rotates on this stable token).
        return _interactive_credential_limit_message(text)
    return None


def _scan_claude_transcript_for_auth_failure(session_file: Path) -> Optional[str]:
    """Terminal auth-failure message for a whole transcript, or ``None``.

    One-shot full scan (used by the exit-path check and tests). The PTY loop
    instead reads incrementally via :func:`_advance_interactive_auth_scan` so a
    long session does not re-read the growing transcript on every poll (Issue
    #1365).
    """
    try:
        raw_lines = session_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    state: Optional[str] = None
    for raw_line in raw_lines:
        try:
            item = json.loads(raw_line)
        except json.JSONDecodeError:
            continue
        state = _auth_state_after_row(state, item)
    return state


def _advance_interactive_auth_scan(
    session_file: Path,
    offset: int,
    buffer: bytes,
    state: Optional[str],
) -> Tuple[Optional[str], int, bytes]:
    """Incrementally fold newly-appended transcript bytes into the auth state.

    Reads only the bytes written since ``offset`` (the JSONL transcript is
    append-only), so a long healthy session pays O(total transcript) across the
    whole run rather than O(n) per poll. ``buffer`` carries an incomplete
    trailing line between calls; ``state`` is the running terminal-auth message
    from :func:`_auth_state_after_row`. The scan continues for the lifetime of
    the session, so a later auth failure after an early healthy turn is still
    caught (Issue #1365). Returns the updated ``(state, offset, buffer)``.
    """
    try:
        size = session_file.stat().st_size
    except OSError:
        return state, offset, buffer
    if size < offset:  # file truncated/rotated — restart the scan
        offset, buffer, state = 0, b"", None
    if size <= offset:
        return state, offset, buffer
    try:
        with open(session_file, "rb") as handle:
            handle.seek(offset)
            chunk = handle.read()
            offset = handle.tell()
    except OSError:
        return state, offset, buffer
    parts = (buffer + chunk).split(b"\n")
    buffer = parts.pop()  # trailing partial line (empty if chunk ended on \n)
    for raw in parts:
        raw = raw.strip()
        if not raw:
            continue
        try:
            item = json.loads(raw)
        except json.JSONDecodeError:
            continue
        state = _auth_state_after_row(state, item)
    return state, offset, buffer


def _interactive_auth_decision(state: Optional[str], buffer: bytes) -> Optional[str]:
    """Committed auth state, overridden by a complete-but-unterminated last line.

    The incremental scanner only commits newline-terminated lines, but a hung
    session's final synthetic auth turn may sit in the transcript without its
    trailing newline yet. If that buffered remainder already parses as a
    complete JSON row, fold it in for the fast-fail decision (without committing
    it — it is re-read once its newline arrives). Issue #1365.
    """
    tail = buffer.strip()
    if not tail:
        return state
    try:
        item = json.loads(tail)
    except json.JSONDecodeError:
        return state
    return _auth_state_after_row(state, item)


def _detect_claude_interactive_auth_failure(
    session_id: str,
    env: Dict[str, str],
) -> Optional[str]:
    """Locate the interactive session transcript and scan it (Issue #1365).

    Convenience wrapper (full scan) used by callers that have only the
    ``session_id`` (the same ``--session-id`` JSONL PDD already reads for cost) —
    the exit-path check and tests. The PTY runner caches the located path and
    reads incrementally via :func:`_advance_interactive_auth_scan` instead, to
    avoid a full-tree search and a full re-read on every poll. A revoked or
    logged-out interactive session
    surfaces a synthetic auth turn within a few seconds and then parks the TUI
    at the prompt forever; detecting it lets the caller fast-fail (and the cloud
    OAuth waterfall rotate credentials) instead of burning the step timeout.
    """
    session_file = _find_claude_interactive_session_file(
        session_id, env, wait_seconds=0.0
    )
    if session_file is None:
        return None
    return _scan_claude_transcript_for_auth_failure(session_file)


def _terminate_process_group(proc: subprocess.Popen, sig: int) -> None:
    try:
        os.killpg(os.getpgid(proc.pid), sig)
    except (ProcessLookupError, OSError):
        try:
            proc.send_signal(sig)
        except (ProcessLookupError, OSError):
            pass


def _parse_claude_interactive_reply(
    reply_path: Path,
    job_id: str,
) -> Tuple[bool, str, float, Optional[str]]:
    try:
        data = json.loads(reply_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return False, f"Invalid Claude interactive reply: {exc}", 0.0, None

    if str(data.get("job_id") or "") != job_id:
        return False, "Claude interactive reply job_id mismatch", 0.0, None

    text = data.get("text")
    if text is None:
        text = ""
    elif not isinstance(text, str):
        text = json.dumps(text, ensure_ascii=True)

    try:
        cost = float(data.get("cost_usd") or 0.0)
    except (TypeError, ValueError):
        cost = 0.0

    model = data.get("model")
    if not isinstance(model, str) or not model:
        model = None

    return bool(data.get("success")), text, cost, model


def _claude_interactive_needs_trust_confirmation(output_tail: str) -> bool:
    """Detect Claude Code's interactive workspace trust prompt."""
    cleaned = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", output_tail)
    cleaned = re.sub(r"\x1b[@-Z\\-_]", "", cleaned)
    lowered = cleaned.lower()
    return all(
        token in lowered
        for token in ("quick", "safety", "check", "trust", "folder", "enter", "confirm")
    )


def _run_interactive_pty_until_reply(
    cmd: List[str],
    *,
    cwd: Path,
    env: Dict[str, str],
    timeout: float,
    reply_path: Path,
    job_id: str,
    session_id: Optional[str] = None,
) -> Tuple[bool, str, float, Optional[str]]:
    """Run an interactive CLI under a PTY until the MCP reply file appears.

    When ``session_id`` is provided, the loop also fast-fails on a post-launch
    authentication failure (Issue #1365): a revoked or logged-out interactive
    session writes a synthetic auth-error turn to its transcript and then sits
    at the prompt forever, so without this check the runner would burn the full
    ``timeout`` per dead credential. ``session_id`` defaults to ``None`` so
    non-interactive callers keep the original behaviour.
    """
    try:
        import pty
        import select
    except ImportError:
        return False, "Claude Code interactive mode requires POSIX PTY support", 0.0, None

    master_fd, slave_fd = pty.openpty()
    output_chunks: List[str] = []
    proc: Optional[subprocess.Popen] = None
    trust_confirmed = False
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=cwd,
            env=env,
            stdin=slave_fd,
            stdout=slave_fd,
            stderr=slave_fd,
            start_new_session=True,
            text=False,
        )
        os.close(slave_fd)
        slave_fd = -1
        start = time.time()
        deadline = start + timeout
        # Issue #1365: throttled post-launch auth-failure check. First check is
        # deferred by a grace window so a healthy session has time to start a
        # real turn before we inspect its transcript. The transcript path is
        # located once and cached so a long healthy session does not pay a
        # full-tree rglob on every poll.
        next_auth_check = start + INTERACTIVE_AUTH_FASTFAIL_GRACE_SECONDS
        auth_session_file: Optional[Path] = None
        auth_offset = 0  # bytes of transcript already scanned (incremental)
        auth_buffer = b""  # carried incomplete trailing transcript line
        auth_state: Optional[str] = None  # running terminal-auth message
        auth_last_size = -1  # transcript size at previous poll (quiescence gate)

        while True:
            if reply_path.exists():
                parsed = _parse_claude_interactive_reply(reply_path, job_id)
                _terminate_process_group(proc, signal.SIGTERM)
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    _terminate_process_group(proc, signal.SIGKILL)
                    proc.wait(timeout=5)
                return parsed

            if proc.poll() is not None:
                break

            now = time.time()
            if session_id and now >= next_auth_check:
                if auth_session_file is None:
                    auth_session_file = _find_claude_interactive_session_file(
                        session_id, env, wait_seconds=0.0
                    )
                if auth_session_file is not None:
                    try:
                        current_size = auth_session_file.stat().st_size
                    except OSError:
                        current_size = auth_last_size
                    # Quiescent = the transcript has not grown since the previous
                    # poll. (auth_last_size < 0 is the first observation.)
                    quiescent = auth_last_size >= 0 and current_size == auth_last_size
                    auth_last_size = current_size
                    auth_state, auth_offset, auth_buffer = _advance_interactive_auth_scan(
                        auth_session_file, auth_offset, auth_buffer, auth_state
                    )
                    auth_failure = _interactive_auth_decision(auth_state, auth_buffer)
                    # Fast-fail only when the transcript shows a terminal auth
                    # error AND has stopped growing — the #1365 "parked at the
                    # prompt forever" hang. While the session is still writing
                    # (e.g. a later row that may supersede the auth error is
                    # mid-append, possibly not yet newline-terminated), defer to
                    # the next poll so a recovering session is never killed on a
                    # stale/partial trailing line.
                    if auth_failure is not None and quiescent:
                        _terminate_process_group(proc, signal.SIGTERM)
                        try:
                            proc.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            _terminate_process_group(proc, signal.SIGKILL)
                            proc.wait(timeout=5)
                        return False, auth_failure, 0.0, None
                next_auth_check = now + INTERACTIVE_AUTH_FASTFAIL_INTERVAL_SECONDS

            remaining = deadline - time.time()
            if remaining <= 0:
                _terminate_process_group(proc, signal.SIGKILL)
                proc.wait(timeout=5)
                tail = "".join(output_chunks)[-MAX_ERROR_SNIPPET_LENGTH:]
                return False, f"Claude interactive mode timed out. Output tail: {tail}", 0.0, None

            readable, _, _ = select.select([master_fd], [], [], min(0.2, remaining))
            if master_fd in readable:
                try:
                    chunk = os.read(master_fd, 4096)
                except OSError:
                    chunk = b""
                if chunk:
                    decoded = chunk.decode("utf-8", errors="replace")
                    output_chunks.append(decoded)
                    if not trust_confirmed:
                        output_tail = "".join(output_chunks)[-4000:]
                        if _claude_interactive_needs_trust_confirmation(output_tail):
                            os.write(master_fd, b"\r")
                            trust_confirmed = True

        if reply_path.exists():
            return _parse_claude_interactive_reply(reply_path, job_id)

        # Issue #1365: a revoked/logged-out session may EXIT (or exit during the
        # grace window) after writing the synthetic auth turn rather than hang.
        # Classify that exit as the same permanent auth failure so the caller
        # rotates credentials instead of retrying a dead one as a generic error.
        if session_id:
            auth_failure = _detect_claude_interactive_auth_failure(session_id, env)
            if auth_failure is not None:
                return False, auth_failure, 0.0, None

        tail = "".join(output_chunks)[-MAX_ERROR_SNIPPET_LENGTH:]
        returncode = proc.returncode if proc is not None else None
        return (
            False,
            f"Claude interactive mode exited without pdd_reply "
            f"(exit={returncode}). Output tail: {tail}",
            0.0,
            None,
        )
    except Exception as exc:
        if proc is not None and proc.poll() is None:
            _terminate_process_group(proc, signal.SIGKILL)
        return False, f"Claude interactive mode failed: {exc}", 0.0, None
    finally:
        if slave_fd != -1:
            try:
                os.close(slave_fd)
            except OSError:
                pass
        try:
            os.close(master_fd)
        except OSError:
            pass


def _run_claude_interactive_with_mcp(
    *,
    cli_path: str,
    prompt_path: Path,
    cwd: Path,
    timeout: float,
    env: Dict[str, str],
    use_playwright: bool = False,
    claude_policy: Optional[ClaudePolicy] = None,
) -> _ProviderRunResult:
    """Run Claude Code interactively and collect its result through MCP."""
    if os.name != "posix":
        return _ProviderRunResult(
            False,
            "Claude Code interactive mode requires a POSIX platform",
            0.0,
            None,
            None,
        )

    job_id = uuid.uuid4().hex
    session_id = str(uuid.uuid4())
    with tempfile.TemporaryDirectory(prefix="pdd-claude-interactive-") as tmp_dir:
        tmp_path = Path(tmp_dir)
        server_path = tmp_path / "pdd_reply_mcp_server.py"
        config_path = tmp_path / "mcp_config.json"
        reply_path = tmp_path / "reply.json"
        _write_claude_reply_mcp_server(server_path)
        _write_claude_interactive_mcp_config(
            config_path,
            server_path,
            reply_path,
            job_id,
        )
        cmd = _build_claude_interactive_command(
            cli_path=cli_path,
            prompt_path=prompt_path,
            config_path=config_path,
            job_id=job_id,
            session_id=session_id,
            env=env,
            use_playwright=use_playwright,
            claude_policy=claude_policy,
        )
        success, text, cost, model = _run_interactive_pty_until_reply(
            cmd,
            cwd=cwd,
            env=env,
            timeout=timeout,
            reply_path=reply_path,
            job_id=job_id,
            session_id=session_id,
        )
        session_cost, session_model, usage = _estimate_claude_interactive_session_cost(
            session_id,
            env,
        )
        if session_cost > 0.0 or cost == 0.0:
            cost = session_cost
        return _ProviderRunResult(
            success,
            text,
            cost,
            model or session_model or env.get("CLAUDE_MODEL"),
            usage,
        )


def _run_with_provider(
    provider: str,
    prompt_path: Path,
    cwd: Path,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
    verbose: bool = False,
    quiet: bool = False,
    cli_path: Optional[str] = None,
    label: str = "",
    use_playwright: bool = False,
    reasoning_time: Optional[float] = None,
    claude_policy: Optional[ClaudePolicy] = None,
) -> Union[Tuple[bool, str, float, Optional[str]], _ProviderRunResult]:
    """
    Internal helper to run a specific provider's CLI.
    Returns a provider result whose iteration yields
    (success, output_or_error, cost, actual_model). Claude paths may expose
    structured usage at index 4 while preserving four-value unpacking.

    Issue #1376: ``actual_model`` is the model name extracted from the
    provider's JSON response (e.g. ``claude-sonnet-4-6``,
    ``gemini-3-flash-preview``, ``gpt-5``). ``None`` when the response did
    not surface a model name (early-exit error paths) — callers blend with
    env-var lookup for "actual or requested" semantics.

    Args:
        provider: Provider name (anthropic, google, openai)
        prompt_path: Path to the prompt file
        cwd: Working directory
        timeout: Timeout in seconds
        verbose: Verbose output
        quiet: Suppress output
        cli_path: Optional explicit CLI path (if None, uses _find_cli_binary)
        label: Task label for heartbeat messages
        use_playwright: Enable constrained tool access for browser testing
        reasoning_time: Reasoning-allocation float in [0.0, 1.0]. When provided,
            takes precedence over the ``PDD_REASONING_EFFORT`` env var.
            ``None`` means "fall back to env" so unplumbed call sites
            keep receiving the signal via the global variable set by
            ``pdd/core/cli.py``.
    """

    # Prepare Environment
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    env.pop("PDD_OUTPUT_COST_PATH", None)
    # Force CLI agents to stay in the worktree instead of following
    # the .git file pointer back to the main repo (Issue #894).
    env["GIT_WORK_TREE"] = str(cwd)

    # Issue #813: under CI=1 the claude CLI prefers ANTHROPIC_API_KEY over the
    # user's stored OAuth (Max/Pro) credential. Drop a stale key only when an
    # OAuth login is confirmed so API-key-only setups (e.g. GitHub App
    # executor with Secret-Manager-injected keys) still work.
    if provider == "anthropic":
        _strip_anthropic_creds_for_claude_subprocess(env, verbose=verbose, quiet=quiet)

    # Get CLI binary name for this provider
    cli_name = CLI_COMMANDS.get(provider)
    if not cli_name:
        return False, f"Unknown provider {provider}", 0.0, None

    # Find CLI binary path (use explicit path if provided)
    if cli_path is None:
        if provider == "google":
            cli_path = _get_google_cli_binary(env)
            if not cli_path:
                return False, f"CLI for google provider not found. PDD_GOOGLE_CLI={env.get('PDD_GOOGLE_CLI', 'auto')}", 0.0, None
        else:
            cli_path = _find_cli_binary(cli_name)
    if not cli_path:
        return False, f"CLI '{cli_name}' not found. {_get_cli_diagnostic_info(cli_name)}", 0.0, None

    cmd: List[str] = []

    # Read prompt content for providers that pipe via stdin
    prompt_content = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else ""

    # Reasoning-effort plumbing. Three input paths converge here, in
    # precedence order:
    # 1. ``CODEX_REASONING_EFFORT`` env var — Codex-specific override, accepts
    #    ``low|medium|high|xhigh`` (xhigh is Codex-only, used by the cloud
    #    worker for GPT-5.4 routing). Only consulted when provider == "openai".
    # 2. Explicit ``reasoning_time`` kwarg threaded down from a command that
    #    saw ``--time`` on argv (cli.py only forwards when ``time_explicit`` is
    #    True, so a default ``ctx.obj["time"]`` does NOT reach here).
    # 3. ``PDD_REASONING_EFFORT`` env var set by pdd/core/cli.py for call
    #    sites that don't thread the kwarg (sync, split, test_generate,
    #    update, verify, crash, etc.).
    # ``CODEX_REASONING_EFFORT`` only fires for the openai branch below; the
    # generic ``reasoning_effort`` resolved here covers paths 2 and 3 and is
    # what the anthropic/gemini logging notices read.
    if reasoning_time is not None:
        from .reasoning import time_to_effort_level
        reasoning_effort = time_to_effort_level(reasoning_time)
    else:
        reasoning_effort = (env.get("PDD_REASONING_EFFORT") or "").strip().lower()
        if reasoning_effort not in {"low", "medium", "high"}:
            reasoning_effort = ""

    # Construct Command using discovered cli_path (Issue #234 fix)
    if provider == "anthropic":
        if _claude_code_interactive_enabled(env):
            if reasoning_effort and not quiet:
                console.print(
                    f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but PDD's "
                    "Claude Code interactive bridge does not map it to a CLI flag; "
                    "applies to llm_invoke steps only, not this subprocess.[/dim]"
                )
            return _run_claude_interactive_with_mcp(
                cli_path=cli_path,
                prompt_path=prompt_path,
                cwd=cwd,
                timeout=timeout,
                env=env,
                use_playwright=use_playwright,
                claude_policy=claude_policy,
            )

        # Use -p - to pipe prompt as direct user message via stdin.
        # This prevents Claude from interpreting file-discovered instructions
        # as "automated bot workflow" and refusing to execute.
        if claude_policy is not None:
            normalized_policy = validate_claude_policy(claude_policy)
            cmd = [cli_path, "-p", "-"]
            _append_claude_policy_args(cmd, normalized_policy)
            cmd.extend(["--output-format", "json"])
        elif use_playwright:
            # Playwright mode: constrained tool access with cost ceiling
            cmd = [
                cli_path,
                "-p", "-",
                "--allowedTools", "Bash", "Read", "Write",
                "--max-turns", "30",
                "--output-format", "json",
            ]
        else:
            cmd = [
                cli_path,
                "-p", "-",
                "--dangerously-skip-permissions",
                "--output-format", "json",
            ]
        # Allow model override via CLAUDE_MODEL env var (Issue #318)
        claude_model = env.get("CLAUDE_MODEL")
        if claude_model:
            cmd.extend(["--model", claude_model])
        if reasoning_effort and not quiet:
            # Always surface outside --quiet mode — silently dropping the user's
            # reasoning signal is a support-ticket generator. The Claude Code CLI
            # has no --reasoning-effort flag today, so clarify that the effort
            # applies to LiteLLM-invoked steps (analysis/verification) but not
            # to this code-writing subprocess.
            console.print(
                f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but Claude Code CLI "
                "has no reasoning-effort flag; applies to llm_invoke steps only, "
                "not this subprocess.[/dim]"
            )
    elif provider == "google":
        resolved_bin = _get_google_cli_name(env)
        if resolved_bin == "agy":
            # Antigravity CLI args.
            # Verified empirically against agy 1.0.1: `--output-format` is NOT
            # a supported flag (`agy --help` lists only --print/--print-timeout
            # /--continue/--conversation/--dangerously-skip-permissions/-i/
            # --log-file/--sandbox/--add-dir; an earlier round-1 review fix
            # that added `--output-format json` made every google run exit 1
            # with `flags provided but not defined: -output-format` instead of
            # the pre-fix "Invalid JSON output"). agy emits PLAIN TEXT on
            # stdout; the agy parse branch further down treats stdout as the
            # response body and surfaces `cost=0, model=null` to the audit
            # log because the CLI does not currently expose usage stats.
            # Unlike the legacy gemini CLI, agy can read the print prompt from
            # stdin. Pipe the prompt body instead of putting it on argv so large
            # issue prompts cannot hit OS argument limits or leak through
            # process listings while the subprocess is running.
            cmd = [
                cli_path,
                "--dangerously-skip-permissions",
                "--print",
            ]
            if env.get("GEMINI_API_KEY") and not (
                env.get("GOOGLE_API_KEY") or env.get("ANTIGRAVITY_API_KEY")
            ):
                env["GOOGLE_API_KEY"] = env["GEMINI_API_KEY"]
            if timeout:
                cmd.extend(["--print-timeout", f"{int(timeout)}s"])

            if env.get("GEMINI_MODEL") and not quiet:
                console.print(
                    "[dim]GEMINI_MODEL requested, but Antigravity CLI has no equivalent "
                    "flag; ignored.[/dim]"
                )
        else:
            # Legacy Gemini CLI
            # Do NOT use -p flag for Gemini. The -p flag passes text literally,
            # so passing a file path gives Gemini the path string instead of content.
            # Instead, pass a short instruction as positional argument telling Gemini
            # to read the prompt file (matches old _run_google_variants pattern).
            cmd = [
                cli_path,
                f"Read the file {prompt_path.name} for your full instructions and execute them.",
                "--yolo",
                "--output-format", "json"
            ]
            # Allow model override via GEMINI_MODEL env var (mirrors CLAUDE_MODEL for anthropic)
            gemini_model = env.get("GEMINI_MODEL")
            if gemini_model:
                cmd.extend(["--model", gemini_model])
        if reasoning_effort and not quiet:
            # See Claude Code branch above for rationale — same constraint applies.
            console.print(
                f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but Google provider CLI "
                "has no reasoning-effort flag; applies to llm_invoke steps only, "
                "not this subprocess.[/dim]"
            )
    elif provider == "openai":
        # --full-auto sets --sandbox workspace-write (Landlock+seccomp), which
        # panics on gVisor (Cloud Run) and Docker-on-macOS. Since the PDD worker
        # container IS the sandbox boundary, use danger-full-access instead.
        # Ref: https://github.com/openai/codex/issues/6828
        sandbox_mode = env.get("CODEX_SANDBOX_MODE", "danger-full-access")
        cmd = [cli_path]
        # Codex accepts -c / --config only as a top-level flag before the
        # subcommand; appending after "exec" is silently ignored.
        # Codex-specific override: CODEX_REASONING_EFFORT takes precedence
        # over the generic reasoning_effort (kwarg / PDD_REASONING_EFFORT)
        # and additionally accepts ``xhigh`` for GPT-5.4 routing — the
        # cloud worker sets this env var directly when promoting Codex to
        # an extra-high reasoning budget regardless of the user's --time.
        codex_effort = (env.get("CODEX_REASONING_EFFORT") or "").strip().lower()
        if codex_effort in {"low", "medium", "high", "xhigh"}:
            effective_codex_effort: Optional[str] = codex_effort
        elif reasoning_effort:
            effective_codex_effort = reasoning_effort
        else:
            effective_codex_effort = None
        if effective_codex_effort:
            cmd.extend(["-c", f"model_reasoning_effort={effective_codex_effort}"])
        # Codex --model is a top-level flag; keep it before the subcommand so
        # the final "-" remains the explicit stdin prompt operand.
        codex_model = env.get("CODEX_MODEL")
        if codex_model:
            cmd.extend(["--model", codex_model])
        cmd.extend([
            "exec",
            "--sandbox", sandbox_mode,
            "--json",
            "-"
        ])
    elif provider == "opencode":
        # OpenCode is a multi-provider routing CLI: a single binary that
        # delegates to whichever backend (Anthropic, OpenAI, GitHub Copilot,
        # OpenRouter, etc.) the resolved ``provider/model`` identifier names.
        # Routing requires a model identifier — without it OpenCode has no
        # deterministic default we can rely on, so fail fast with an
        # actionable message instead of letting the CLI surface a generic
        # error far from the configuration source.
        model_id = _resolve_opencode_model_for_run(env, cwd=cwd)
        if not model_id:
            return False, (
                "Cannot resolve an OpenCode model: OPENCODE_MODEL is not set "
                "and no llm_model.csv row matches a configured OpenCode "
                "provider. Set OPENCODE_MODEL to a 'provider/model' identifier "
                "(e.g., 'anthropic/claude-sonnet-4-6', "
                "'openrouter/openai/gpt-5', 'github-copilot/gpt-5'), configure "
                "a provider via `opencode auth login`, or set a backend "
                "provider env var (ANTHROPIC_API_KEY, OPENAI_API_KEY, "
                "GEMINI_API_KEY, OPENROUTER_API_KEY, GITHUB_TOKEN, ...)."
            ), 0.0, None
        translated_model = _translate_to_opencode_model(model_id)
        cmd = [
            cli_path,
            "run",
            "--dir", str(cwd),
            "--format", "json",
            "--dangerously-skip-permissions",
            "--model", translated_model,
        ]
        agent_name = (env.get("OPENCODE_AGENT") or "").strip()
        if agent_name:
            cmd.extend(["--agent", agent_name])
        variant_name = (env.get("OPENCODE_VARIANT") or "").strip()
        if variant_name:
            cmd.extend(["--variant", variant_name])
        # The OpenCode CLI requires a positional ``message`` argument for
        # ``opencode run`` (https://opencode.ai/docs/cli/) — earlier revisions
        # passed only ``--`` and piped the prompt body on stdin, which the CLI
        # does not consume in non-interactive mode. The full prompt is in
        # ``prompt_path``; pass only a short directive on argv so large issue
        # prompts cannot exceed OS argv limits while OpenCode still receives a
        # valid trailing message. Using ``--`` first ensures the directive is
        # parsed as the message and not a flag.
        cmd.append("--")
        cmd.append(
            f"Read the file {prompt_path.name} for your full instructions and execute them."
        )
    else:
        return False, f"Unknown provider {provider}", 0.0, None

    # Claude and Codex both support stdin. Passing the prompt path as Codex's
    # positional argument makes the path string the prompt, not the file body.
    # OpenCode reads the prompt from the file referenced in the trailing
    # message argv, so it does NOT receive the body via stdin.
    stdin_content = prompt_content if (
        provider in {"anthropic", "openai"}
        or (provider == "google" and _get_google_cli_name(env) == "agy")
    ) else None

    try:
        result = _subprocess_run(
            cmd,
            cwd=cwd,
            env=env,
            input=stdin_content,
            capture_output=True,
            text=True,
            timeout=timeout,
            start_new_session=True,
        )
    except subprocess.TimeoutExpired:
        return False, "Timeout expired", 0.0, None
    except Exception as e:
        return False, str(e), 0.0, None

    if result.returncode != 0:
        if provider == "openai":
            stdout_error = _extract_codex_jsonl_error(result.stdout or "")
            combined_error = "\n".join(
                part for part in [
                    result.stderr or "",
                    (result.stdout or "")[:MAX_ERROR_SNIPPET_LENGTH],
                ]
                if part
            )
            codex_auth_message = _codex_auth_failure_message(combined_error)
            if codex_auth_message:
                return False, codex_auth_message, 0.0, None
            if stdout_error:
                return False, f"Exit code {result.returncode}: {stdout_error}", 0.0, None
            if result.stderr and not _is_codex_stdin_notice(result.stderr):
                error_detail = result.stderr
            else:
                error_detail = (result.stdout or result.stderr or "")[:MAX_ERROR_SNIPPET_LENGTH]
            return False, f"Exit code {result.returncode}: {error_detail}", 0.0, None
        error_detail = result.stderr or result.stdout[:500]
        return False, f"Exit code {result.returncode}: {error_detail}", 0.0, None

    # OpenCode: parse JSONL output via the dedicated parser. OpenCode emits a
    # different event schema than Codex/Claude (step_start, text, step_finish,
    # error...) and routes cost via ``step_finish.part.cost``, so it doesn't
    # belong in the shared single-JSON / Codex-NDJSON path below.
    if provider == "opencode":
        parsed = _parse_opencode_jsonl(result.stdout)
        actual_model = parsed.get("model") or None
        err = parsed.get("error") or ""
        # Cost: prefer JSONL-reported cost; fall back to CSV pricing when
        # OpenCode did not surface a cost field (some backends/sessions omit
        # ``step_finish.part.cost``). Returning $0.00 for a successful run
        # silently breaks cost-accounting acceptance.
        if parsed.get("cost_reported"):
            cost = float(parsed.get("cost") or 0.0)
        else:
            tokens = parsed.get("tokens") or {}
            csv_model_id = actual_model or _resolve_opencode_model_for_run(env, cwd=cwd)
            cost = _opencode_csv_cost(csv_model_id, tokens)
        if err:
            # An error event with returncode==0 still represents a routing /
            # provider failure inside OpenCode (e.g., "provider not
            # configured"). Surface as failure, but keep cost and any
            # captured model so callers can audit partial spend.
            return False, str(err), cost, actual_model
        return (
            True,
            str(parsed.get("text") or ""),
            cost,
            actual_model,
        )

    # Diagnostic: capture when CLI exits 0 with empty / whitespace-only stdout.
    # Cloud one-session sync runs hit "All agent providers failed: anthropic: "
    # with a blank provider error and no log trail. Stderr tail + prompt size
    # + auth-key presence is usually enough to tell apart auth failures, rate
    # limits, and genuine empty responses.
    if not result.stdout.strip():
        auth_keys_present = sorted(
            k for k in env
            if ("TOKEN" in k or "API_KEY" in k) and env.get(k)
        )
        stderr_tail = (result.stderr or "")[-500:]
        console.print(
            f"[bold red]Provider {provider} returned exit 0 with EMPTY stdout[/bold red]"
        )
        console.print(
            f"[dim]stderr_tail={stderr_tail!r} prompt_chars={len(stdin_content or '')} "
            f"auth_keys={auth_keys_present} cwd={cwd}[/dim]"
        )

    # Antigravity (`agy`): the CLI emits plain text on stdout (no
    # --output-format flag is supported as of agy 1.0.1, see cmd-build
    # comment above). agy ALSO exits 0 in two failure modes that we must
    # surface as failures instead of treating as a successful response:
    #   - timeout: stdout is exactly `Error: timed out waiting for response`
    #   - missing/expired OAuth in headless mode: stdout starts with
    #     `Authentication required.` followed by the device-code URL.
    # Anything else with exit 0 is treated as the response body. Cost and
    # model are unknown — the audit log will show `cost=0, model=null`
    # until Google ships a structured-output mode.
    if provider == "google" and _get_google_cli_name(env) == "agy":
        text = result.stdout.strip()
        if (
            text.startswith("Error:")
            or text.startswith("Authentication required.")
        ):
            return False, text[:MAX_ERROR_SNIPPET_LENGTH], 0.0, None
        return True, text, 0.0, None

    # Parse JSON Output
    try:
        # Handle JSONL output (Codex sometimes streams)
        output_str = result.stdout.strip()
        data = {}
        
        if provider == "openai" and "\n" in output_str:
            # Parse NDJSON, collecting both the agent response and usage stats
            lines = output_str.splitlines()
            agent_message_data = None
            session_end = None
            for line in lines:
                try:
                    item = json.loads(line)
                    # Legacy Codex format: single event contains both text and usage
                    if item.get("type") == "result":
                        data = item
                        break
                    # Modern Codex CLI (0.104.0+): text in item.completed agent_message
                    if (item.get("type") == "item.completed"
                            and isinstance(item.get("item"), dict)
                            and item["item"].get("type") == "agent_message"):
                        agent_message_data = item
                    # usage/cost stats are in session.end or turn.completed
                    # (Codex CLI 0.105.0+ uses turn.completed instead of session.end)
                    if item.get("type") in ("session.end", "turn.completed"):
                        session_end = item
                except json.JSONDecodeError:
                    continue
            if not data:
                if agent_message_data is not None:
                    # Merge usage AND model from session.end so cost calculation
                    # works AND the audit log captures the actual model name
                    # (Issue #1376 codex round 3: previously only `usage` was
                    # carried over, so default-model Codex runs logged
                    # `model: null` because session.end.model was discarded).
                    if session_end is not None:
                        merged: Dict[str, Any] = {**agent_message_data}
                        if "usage" in session_end:
                            merged["usage"] = session_end.get("usage", {})
                        if "model" in session_end:
                            merged["model"] = session_end.get("model")
                        data = merged
                    else:
                        data = agent_message_data
                elif session_end is not None:
                    data = session_end
                elif lines:
                    try:
                        data = json.loads(lines[-1])
                    except:
                        pass
        else:
            # Claude Code may emit non-JSON text to stdout (npm warnings,
            # upgrade prompts) alongside the JSON result.  Try parsing as
            # single JSON first, then fall back to line-by-line extraction.
            try:
                data = json.loads(output_str)
            except json.JSONDecodeError:
                data = _extract_json_from_output(output_str)

        success, text, cost, actual_model = _parse_provider_json(provider, data)
        if cost == 0.0 and verbose and isinstance(data, dict):
            console.print(
                f"[dim]Warning: {provider} returned $0 cost. "
                f"JSON keys: {sorted(data.keys())}[/dim]"
            )
        if provider == "anthropic":
            return _ProviderRunResult(
                success,
                text,
                cost,
                actual_model,
                _extract_anthropic_standard_usage(
                    data,
                    actual_model=actual_model,
                ),
            )
        return success, text, cost, actual_model
    except json.JSONDecodeError:
        # Fallback if CLI didn't output valid JSON (sometimes happens on crash)
        return False, f"Invalid JSON output: {result.stdout[:MAX_ERROR_SNIPPET_LENGTH]}...", 0.0, None


def _extract_json_from_output(output_str: str) -> dict:
    """Extract a JSON object from output that may contain non-JSON text.

    Claude Code may emit non-JSON text to stdout (npm warnings, upgrade
    prompts) alongside the JSON result.  Try line-by-line extraction first,
    then fall back to brace-depth matching on the full string.

    Raises ``json.JSONDecodeError`` if no valid JSON object can be found.
    """
    # Try each line individually
    for line in output_str.splitlines():
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            return json.loads(line)
        except json.JSONDecodeError:
            continue

    # Fallback: brace-depth matching to find the first complete JSON object
    depth = 0
    start_index: Optional[int] = None
    in_string = False
    escape = False

    for i, ch in enumerate(output_str):
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue

        if ch == '"':
            in_string = True
            continue

        if ch == "{":
            if depth == 0:
                start_index = i
            depth += 1
        elif ch == "}" and depth > 0:
            depth -= 1
            if depth == 0 and start_index is not None:
                candidate = output_str[start_index : i + 1]
                try:
                    return json.loads(candidate)
                except json.JSONDecodeError:
                    start_index = None
                    continue

    raise json.JSONDecodeError(
        "No valid JSON object found in output", output_str[:200], 0
    )


def _extract_provider_model_from_data(provider: str, data: Dict[str, Any]) -> Optional[str]:
    """Extract the actual model name from a provider's JSON response.

    Issue #1376 codex review (P2): supplements ``_get_provider_model`` (env-var
    only) so the audit log can record the model the provider *actually* used,
    not just the one the user asked for. Falls back to ``None`` when the JSON
    doesn't expose a model name; callers blend with env-var lookup for a
    "actual or requested" view.

    - Anthropic: keys of ``modelUsage`` (Claude Code emits one entry per model
      it routed through; if multiple, joins with ``+`` for transparency).
    - Google: keys of ``stats.models`` (Gemini CLI emits one entry per model).
    - OpenAI: ``data["model"]`` (Codex CLI surfaces it on the result envelope).
    """
    if not isinstance(data, dict):
        return None
    try:
        if provider == "anthropic":
            usage = data.get("modelUsage")
            if isinstance(usage, dict) and usage:
                names = [str(k) for k in usage.keys() if k]
                if names:
                    return "+".join(sorted(names)) if len(names) > 1 else names[0]
            model = _extract_anthropic_model_from_envelope(data)
            if model:
                return model
        elif provider == "google":
            models = (data.get("stats") or {}).get("models")
            if isinstance(models, dict) and models:
                names = [str(k) for k in models.keys() if k]
                if names:
                    return "+".join(sorted(names)) if len(names) > 1 else names[0]
        elif provider == "openai":
            model = data.get("model")
            if isinstance(model, str) and model:
                return model
            # Fallback: some Codex schemas place model on session.end / item
            for nested_key in ("session", "item"):
                nested = data.get(nested_key)
                if isinstance(nested, dict):
                    nm = nested.get("model")
                    if isinstance(nm, str) and nm:
                        return nm
    except Exception:
        return None
    return None


def _parse_provider_json(
    provider: str, data: Dict[str, Any]
) -> Tuple[bool, str, float, Optional[str]]:
    """
    Extracts (success, text_response, cost_usd, actual_model) from provider JSON.

    Issue #1376: returns the model the provider actually used (when the JSON
    response carries it) so the audit log can answer "which provider/model
    produced step N?" without relying on env-var overrides.
    """
    cost = 0.0
    output_text = ""
    actual_model = _extract_provider_model_from_data(provider, data)

    try:
        if provider == "anthropic":
            # Use total_cost_usd if available, otherwise estimate from token usage
            cost = float(data.get("total_cost_usd", 0.0))
            if cost == 0.0:
                cost = _calculate_anthropic_cost(data)
            # Result might be in 'result' or 'response'
            output_text = data.get("result") or data.get("response") or ""
            # Claude Code JSON includes is_error when the session failed
            # (auth, refusal, crash). Propagate as failure so callers can
            # retry or fall through instead of treating it as success.
            #
            # Issue #814 codex iter-13: preserve `api_error_status` in the
            # text we hand to `_classify_permanent_error` /
            # `_is_rate_limited`. Without it, a 429 envelope whose
            # `result` is just "Please go to Plans & Billing..." would
            # match the weak billing-page pattern and be misclassified
            # as permanent — bypassing the intended rate-limit retry.
            if data.get("is_error"):
                api_status = data.get("api_error_status")
                detail = str(output_text) or "CLI reported is_error with no message"
                if api_status is not None:
                    detail = f"HTTP {api_status}: {detail}"
                return False, detail, cost, actual_model

        elif provider == "google":
            stats = data.get("stats", {})
            cost = _calculate_gemini_cost(stats)
            output_text = data.get("result") or data.get("response") or data.get("output") or ""

        elif provider == "openai":
            usage = data.get("usage", {})
            cost = _calculate_codex_cost(usage)
            # Modern Codex CLI (0.104.0+): text at data["item"]["text"]
            item = data.get("item", {})
            if isinstance(item, dict) and item.get("type") == "agent_message":
                output_text = item.get("text", "")
            else:
                output_text = data.get("result") or data.get("output") or ""

        return True, str(output_text), cost, actual_model

    except Exception as e:
        return False, f"Error parsing {provider} JSON: {e}", 0.0, actual_model


# --- GitHub State Persistence ---

def _build_state_marker(workflow_type: str, issue_number: int) -> str:
    return f"{GITHUB_STATE_MARKER_START}{workflow_type}:issue-{issue_number}"

def _serialize_state_comment(workflow_type: str, issue_number: int, state: Dict) -> str:
    marker = _build_state_marker(workflow_type, issue_number)
    json_str = json.dumps(state, indent=2)
    return f"{marker}\n{json_str}\n{GITHUB_STATE_MARKER_END}"

def _parse_state_from_comment(body: str, workflow_type: str, issue_number: int) -> Optional[Dict]:
    marker = _build_state_marker(workflow_type, issue_number)
    if marker not in body:
        return None
    
    try:
        # Extract content between marker and end marker
        start_idx = body.find(marker) + len(marker)
        end_idx = body.find(GITHUB_STATE_MARKER_END, start_idx)
        
        if end_idx == -1:
            return None
            
        json_str = body[start_idx:end_idx].strip()
        return json.loads(json_str)
    except (json.JSONDecodeError, ValueError):
        return None


def _flatten_comment_pages(payload: Any) -> List[Dict]:
    """Flatten GitHub comment payloads from one page or slurped pages."""
    comments: List[Dict] = []
    if isinstance(payload, dict):
        comments.append(payload)
    elif isinstance(payload, list):
        for item in payload:
            comments.extend(_flatten_comment_pages(item))
    return comments


def _load_gh_paginated_comments(stdout: str) -> List[Dict]:
    """Parse comments emitted by ``gh api --paginate`` with or without slurp."""
    text = stdout.strip()
    if not text:
        return []

    try:
        return _flatten_comment_pages(json.loads(text))
    except json.JSONDecodeError:
        pass

    decoder = json.JSONDecoder()
    index = 0
    comments: List[Dict] = []
    while index < len(text):
        while index < len(text) and text[index].isspace():
            index += 1
        if index >= len(text):
            break
        payload, index = decoder.raw_decode(text, index)
        comments.extend(_flatten_comment_pages(payload))
    return comments

def _find_state_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_type: str,
    cwd: Path
) -> Optional[Tuple[int, Dict]]:
    """
    Returns (comment_id, state_dict) if found, else None.
    """
    if not _find_cli_binary("gh"):
        return None

    try:
        # List comments
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
            "--method", "GET",
            "--paginate",
            "--slurp",
        ]
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        if result.returncode != 0:
            return None

        comments = _load_gh_paginated_comments(result.stdout)
        marker = _build_state_marker(workflow_type, issue_number)

        best: Optional[Tuple[int, Dict]] = None
        for comment in comments:
            body = comment.get("body", "")
            if marker in body:
                state = _parse_state_from_comment(body, workflow_type, issue_number)
                if state:
                    cid = comment["id"]
                    if best is None or cid > best[0]:
                        best = (cid, state)
        return best
    except Exception:
        return None


def _find_all_state_comments(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_type: str,
    cwd: Path,
) -> List[int]:
    """Return EVERY GitHub comment id whose body contains this workflow's
    state marker, in the order GitHub returned them.

    The legacy ``_find_state_comment`` returns only the first match, which
    is fine for the happy path where there is exactly one state comment.
    Issue #1149 surfaced a duplicate-marker hazard: if two workers race
    on first-save and both POST a fresh state comment, or a prior run's
    state was never fully cleared, two valid-looking comments coexist.
    A future normal resume's ``_find_state_comment`` will load whichever
    one GitHub ranks first — usually the OLDER one — silently resuming
    against stale step outputs. Callers that need to deduplicate (clean
    restart pre-clear, or save's first-write dedupe path) must use this
    helper, not the singleton variant.
    """
    if not _find_cli_binary("gh"):
        return []

    try:
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
            "--method", "GET",
            "--paginate",
            "--slurp",
        ]
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        if result.returncode != 0:
            return []
        comments = _load_gh_paginated_comments(result.stdout)
        marker = _build_state_marker(workflow_type, issue_number)
        ids: List[int] = []
        for comment in comments:
            body = comment.get("body", "")
            if marker in body and comment.get("id") is not None:
                ids.append(int(comment["id"]))
        return ids
    except Exception:
        return []


def _github_delete_comment(repo_owner: str, repo_name: str, comment_id: int, cwd: Path) -> bool:
    """Delete one issue comment by id via ``gh api``. Best-effort, never raises."""
    if not _find_cli_binary("gh"):
        return False
    try:
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
            "-X", "DELETE",
        ]
        res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        return res.returncode == 0
    except Exception:
        return False


# Tombstone body written when a state comment cannot be DELETEd. It must
# NOT contain ``GITHUB_STATE_MARKER_START`` so that a subsequent
# ``_find_state_comment`` / ``_find_all_state_comments`` no longer treats
# it as live state.
_GITHUB_STATE_CLEARED_TOMBSTONE = (
    "<!-- PDD_WORKFLOW_STATE_CLEARED -->\n"
    "_PDD workflow state was cleared. The original state comment could "
    "not be deleted (the token may lack delete scope), so its body was "
    "neutralised — this comment no longer carries resumable state and a "
    "rerun will start fresh._"
)


def _github_edit_comment(
    repo_owner: str, repo_name: str, comment_id: int, body: str, cwd: Path
) -> bool:
    """PATCH one issue comment body via ``gh api``. Best-effort, never raises."""
    if not _find_cli_binary("gh"):
        return False
    try:
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
            "-X", "PATCH",
            "-f", f"body={body}",
        ]
        res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        return res.returncode == 0
    except Exception:
        return False


def github_save_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_type: str,
    state: Dict,
    cwd: Path,
    comment_id: Optional[int] = None,
    *,
    dedupe: bool = False,
) -> Optional[int]:
    """
    Creates or updates a GitHub comment with the state. Returns new/existing comment_id.

    When ``dedupe=True`` and ``comment_id is None`` (i.e. this is the
    session's first save and we have no prior id to PATCH), the helper
    first lists ALL comments carrying this workflow's state marker. If
    one or more already exist, it PATCHes the most-recent (highest id)
    in place and DELETEs the rest, returning the PATCHed id. This closes
    the duplicate-marker hazard described on ``_find_all_state_comments``
    in cases where a concurrent worker re-created a state comment in the
    gap between a clean-restart pre-clear and this save.
    """
    if not _find_cli_binary("gh"):
        return None

    body = _serialize_state_comment(workflow_type, issue_number, state)

    try:
        if comment_id:
            # PATCH existing
            cmd = [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
                "-X", "PATCH",
                "-f", f"body={body}"
            ]
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            if res.returncode == 0:
                return comment_id
        else:
            existing_ids: List[int] = []
            if dedupe:
                existing_ids = _find_all_state_comments(
                    repo_owner, repo_name, issue_number, workflow_type, cwd
                )

            if existing_ids:
                # Adopt the most recent comment (GitHub assigns monotonically
                # increasing ids), PATCH it in place, and delete the rest.
                keep_id = max(existing_ids)
                cmd = [
                    "gh", "api",
                    f"repos/{repo_owner}/{repo_name}/issues/comments/{keep_id}",
                    "-X", "PATCH",
                    "-f", f"body={body}",
                ]
                res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
                if res.returncode != 0:
                    return None
                failed_ids = [
                    stale_id for stale_id in existing_ids
                    if stale_id != keep_id
                    and not _github_delete_comment(repo_owner, repo_name, stale_id, cwd)
                ]
                if failed_ids:
                    print(
                        f"[pdd] github_save_state: {len(failed_ids)} stale state "
                        f"comment(s) for issue #{issue_number} could not be deleted: "
                        f"{failed_ids}",
                        file=sys.stderr,
                    )
                return keep_id

            # POST new
            cmd = [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
                "-X", "POST",
                "-f", f"body={body}"
            ]
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            if res.returncode == 0:
                data = json.loads(res.stdout)
                return data.get("id")

        return None
    except Exception:
        return None

def github_load_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_type: str,
    cwd: Path
) -> Tuple[Optional[Dict], Optional[int]]:
    """
    Wrapper to find state. Returns (state, comment_id).
    """
    result = _find_state_comment(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if result:
        return result[1], result[0]
    return None, None

def github_clear_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_type: str,
    cwd: Path,
) -> bool:
    """
    Deletes EVERY GitHub comment carrying this workflow's state marker.

    Previously this helper deleted only the first matching comment
    (whichever ``_find_state_comment`` returned). That left any older /
    duplicate state markers behind, so a subsequent normal resume could
    load a stale state and silently start from the wrong step. Sweeping
    all matches is safe because there should never legitimately be more
    than one state comment per (issue, workflow); when there are, both
    are equally untrustworthy and the next save will repost a fresh one.
    """
    ids = _find_all_state_comments(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if not ids:
        return True  # Already clear

    all_cleared = True
    for cid in ids:
        if _github_delete_comment(repo_owner, repo_name, cid, cwd):
            continue
        # DELETE failed (e.g. the token lacks the delete-comment scope).
        # A stale state comment left behind is loaded with PRIORITY over
        # local state by ``load_workflow_state`` (issue #1212 round-17
        # follow-up), so the next run would replay the stale cache and
        # repeat the old refusal forever. Fall back to neutralising the
        # body: strip the state marker so future loads no longer parse
        # it as resumable state and the workflow reruns from scratch.
        if not _github_edit_comment(
            repo_owner, repo_name, cid, _GITHUB_STATE_CLEARED_TOMBSTONE, cwd
        ):
            all_cleared = False
    return all_cleared

def _should_use_github_state(use_github_state: bool) -> bool:
    if not use_github_state:
        return False
    if os.environ.get("PDD_NO_GITHUB_STATE") == "1":
        return False
    return True

# --- Cached State Validation (Issue #467) ---

def validate_cached_state(
    last_completed_step: Union[int, float],
    step_outputs: Dict[str, str],
    step_order: Optional[List[Union[int, float]]] = None,
    quiet: bool = False,
) -> Union[int, float]:
    """Validate cached state and return actual last successful step.

    Scans step_outputs for entries with "FAILED:" prefix and corrects
    last_completed_step to the actual last successfully completed step.
    This prevents the "blind resume" bug (Issue #467) where the orchestrator
    trusts a corrupted last_completed_step and skips failed steps.

    Args:
        last_completed_step: The stored last_completed_step value.
        step_outputs: Dict mapping step number strings to output strings.
        step_order: Ordered list of step numbers. If None, derived from
            step_outputs keys sorted numerically.
        quiet: If False, prints a warning when correction is applied.

    Returns:
        The corrected last_completed_step value.
    """
    if not step_outputs:
        return last_completed_step

    if step_order is None:
        # Derive order from keys, sorted numerically
        # Filter out non-numeric keys (e.g. "1b", "2b", "7b", "9b") that
        # are informational intermediate-step outputs — only numeric keys
        # (e.g. "1", "1.5", "2", "7.5") participate in validation ordering.
        numeric_keys = []
        for k in step_outputs.keys():
            try:
                float(k)
                numeric_keys.append(k)
            except ValueError:
                continue
        step_order = sorted(numeric_keys, key=lambda k: float(k))
    else:
        # Convert to string keys for lookup
        step_order = [str(s) if not isinstance(s, str) else s for s in step_order]

    actual_last_success: Union[int, float] = 0
    for sn in step_order:
        key = str(sn)
        output_val = step_outputs.get(key, "")
        if not output_val:
            break
        if str(output_val).startswith("FAILED:"):
            break
        # Parse back to numeric for comparison
        try:
            actual_last_success = float(key) if "." in key else int(key)
        except ValueError:
            actual_last_success = 0

    if actual_last_success < last_completed_step:
        if not quiet:
            console.print(
                f"[yellow]State validation: correcting last_completed_step "
                f"from {last_completed_step} to {actual_last_success} "
                f"(found FAILED steps in cache)[/yellow]"
            )
        return actual_last_success

    return last_completed_step


# --- High Level State Wrappers ---


def _steer_cursor_initialized(state: Dict[str, Any]) -> bool:
    """True when GitHub polling may run without treating all history as new steers."""
    if state.get("steer_cursor_seeded"):
        return True
    return state.get("last_steered_comment_id") is not None


def _gh_api_list_issue_comments_cmd(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    *,
    since: Optional[str] = None,
) -> List[str]:
    """Build ``gh api`` argv for listing issue comments.

    ``gh`` treats ``-f`` field parameters as a POST body unless ``--method GET``
    is set, which would 422 on the comments collection endpoint.
    """
    cmd = [
        "gh",
        "api",
        f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
        "--method",
        "GET",
        "--paginate",
        "--slurp",
    ]
    if since:
        cmd.extend(["-f", f"since={since}"])
    return cmd


def _fetch_issue_comments_via_gh(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    *,
    cwd: Path,
    since: Optional[str] = None,
) -> Tuple[Optional[List[Dict]], Optional[str]]:
    """List issue comments via ``gh api``.

    Returns ``(comments, None)`` on success and ``(None, reason)`` on failure.
    """
    if not _find_cli_binary("gh"):
        return None, "gh CLI not found on PATH"
    cmd = _gh_api_list_issue_comments_cmd(
        repo_owner, repo_name, issue_number, since=since
    )
    try:
        res = _subprocess_run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            start_new_session=True,
        )
    except Exception as exc:
        return None, f"gh api error: {exc}"
    if res.returncode != 0:
        detail = (res.stderr or res.stdout or "").strip()
        if len(detail) > 200:
            detail = detail[:200] + "…"
        suffix = f": {detail}" if detail else ""
        return None, f"gh api failed (exit {res.returncode}){suffix}"
    return _load_gh_paginated_comments(res.stdout), None


def _log_steer_seed_skipped(reason: Optional[str], *, quiet: bool) -> None:
    """Warn when baseline steer cursor seed could not run."""
    detail = reason or "could not fetch issue comments"
    msg = (
        f"Mid-run steering: skipped steer cursor seed ({detail}). "
        "GitHub issue comments will not be drained until a successful seed."
    )
    _steer_logger.warning(msg)
    if not quiet:
        console.print(f"[yellow]Warning: {msg}[/yellow]")


def seed_issue_steer_cursor(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    state: Dict[str, Any],
    *,
    cwd: Path,
    quiet: bool = False,
) -> bool:
    """Set steer cursor to the current issue comment tail without returning steers.

    Call once at workflow start so ``drain_issue_steers`` only picks up comments
    posted after the run began. Uses the maximum comment id on the issue (all
    authors, including bots) so later bot progress comments do not rewind the id
    cursor.
    """
    comments, fetch_err = _fetch_issue_comments_via_gh(
        repo_owner, repo_name, issue_number, cwd=cwd
    )
    if comments is None:
        _log_steer_seed_skipped(fetch_err, quiet=quiet)
        return False
    max_id_val = -1
    latest_timestamp: Optional[str] = None
    for comment in comments:
        if not isinstance(comment, dict):
            continue
        cid = comment.get("id")
        try:
            cid_val = int(cid) if cid is not None else 0
        except (ValueError, TypeError):
            cid_val = 0
        if cid_val > max_id_val:
            max_id_val = cid_val
        created_at = comment.get("created_at")
        if created_at and (
            latest_timestamp is None or created_at > latest_timestamp
        ):
            latest_timestamp = created_at

    if max_id_val >= 0:
        state["last_steered_comment_id"] = str(max_id_val)
    if latest_timestamp:
        state["last_steer_at"] = latest_timestamp
    state["steer_cursor_seeded"] = True
    return True


def fetch_issue_updated_at(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    *,
    cwd: Path,
) -> str:
    """Return the GitHub issue ``updated_at`` timestamp, or empty string on failure."""
    if not _find_cli_binary("gh"):
        return ""
    try:
        res = _subprocess_run(
            [
                "gh",
                "api",
                f"repos/{repo_owner}/{repo_name}/issues/{issue_number}",
                "--jq",
                ".updated_at",
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
            start_new_session=True,
        )
        if res.returncode == 0 and res.stdout.strip():
            return res.stdout.strip()
    except Exception:
        pass
    return ""


def ensure_issue_steer_cursor_seeded(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    state: Dict[str, Any],
    *,
    cwd: Path,
    quiet: bool = False,
) -> bool:
    """Seed the steer cursor at workflow start when not yet established.

    Returns True when ``state`` was updated (caller should persist workflow state).
    """
    if not repo_owner or not repo_name or not issue_number:
        return False
    if _steer_cursor_initialized(state):
        return False
    return seed_issue_steer_cursor(
        repo_owner, repo_name, issue_number, state, cwd=cwd, quiet=quiet
    )


def drain_issue_steers(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    state: Dict[str, Any],
    *,
    cwd: Path,
) -> List[SteerEntry]:
    """Drain mid-run user steering inputs (env handoff or GitHub issue comments).

    Sources (in priority order):
    - ``PDD_STEER_JSON`` env var: JSON list of objects with ``comment_id``,
      ``author``, and ``body`` fields.
    - GitHub issue comments via ``gh api`` (when available).

    Persists steering cursor fields in ``state`` for idempotency:
    - ``last_steered_comment_id`` (str)
    - ``last_steer_at`` (ISO timestamp from GitHub, best-effort)
    - ``steer_generation`` (int, increments when new steers are applied)
    - ``steer_cursor_seeded`` (bool, set by ``seed_issue_steer_cursor``)

    GitHub polling is skipped until ``seed_issue_steer_cursor`` (or a resumed
    state with ``last_steered_comment_id``) establishes a baseline cursor.
    """
    steers: List[SteerEntry] = []

    # 1) Env handoff (useful for local tests and cloud runners)
    steer_json = os.environ.get("PDD_STEER_JSON")
    if steer_json:
        try:
            entries = json.loads(steer_json)
        except json.JSONDecodeError:
            entries = None
        if isinstance(entries, list):
            try:
                last_id_val = int(state.get("last_steered_comment_id") or -1)
            except (ValueError, TypeError):
                last_id_val = -1
            max_id_val = last_id_val
            for entry in entries:
                if not isinstance(entry, dict):
                    continue
                cid_raw = entry.get("comment_id", "")
                try:
                    cid_val = int(cid_raw)
                except (ValueError, TypeError):
                    continue
                if cid_val <= last_id_val:
                    continue
                raw_body = str(entry.get("body", ""))
                steers.append(
                    SteerEntry(
                        comment_id=str(cid_val),
                        author=str(entry.get("author", "unknown")),
                        body=_steer_body_for_llm(raw_body),
                    )
                )
                if cid_val > max_id_val:
                    max_id_val = cid_val
            if steers:
                state["last_steered_comment_id"] = str(max_id_val)
                state["last_steer_at"] = (
                    state.get("last_steer_at")
                    or datetime.now(timezone.utc).isoformat()
                )
                state["steer_generation"] = state.get("steer_generation", 0) + 1
                return steers

    # 2) GitHub poll (best-effort)
    if not _find_cli_binary("gh"):
        return []

    if not _steer_cursor_initialized(state):
        # Without a run-start baseline, every historical human comment would be
        # treated as a mid-run steer. Call seed_issue_steer_cursor() first.
        return []

    since = state.get("last_steer_at")
    last_id = state.get("last_steered_comment_id")

    comments, _fetch_err = _fetch_issue_comments_via_gh(
        repo_owner,
        repo_name,
        issue_number,
        cwd=cwd,
        since=since if since else None,
    )
    if comments is None:
        return []

    try:
        last_id_val = int(last_id) if last_id is not None else -1
    except (ValueError, TypeError):
        last_id_val = -1

    max_id_val = last_id_val
    latest_timestamp = since
    new_steers: List[SteerEntry] = []

    for comment in comments:
        if not isinstance(comment, dict):
            continue
        cid = comment.get("id")
        try:
            cid_val = int(cid) if cid is not None else 0
        except (ValueError, TypeError):
            cid_val = 0
        if cid_val <= last_id_val:
            continue

        user = comment.get("user", {}) or {}
        if user.get("type") == "Bot":
            continue

        body = str(comment.get("body", "") or "")

        # Filter out PDD state/progress markers and bot/status comments.
        if GITHUB_STATE_MARKER_START in body or GITHUB_STATE_MARKER_END in body:
            continue
        if "PDD-INCREMENTAL-STATUS" in body:
            continue
        if "PDD_WORKFLOW_STATE" in body:
            continue
        if re.search(r"^## Step \d+/\d+:", body, re.MULTILINE):
            continue

        created_at = comment.get("created_at")
        author = str(user.get("login", "unknown") or "unknown")

        new_steers.append(
            SteerEntry(
                comment_id=str(cid_val),
                author=author,
                body=_steer_body_for_llm(body),
            )
        )

        if cid_val > max_id_val:
            max_id_val = cid_val
        if latest_timestamp is None or (created_at and created_at > latest_timestamp):
            latest_timestamp = created_at

    if new_steers:
        state["last_steered_comment_id"] = str(max_id_val)
        state["last_steer_at"] = latest_timestamp
        state["steer_generation"] = state.get("steer_generation", 0) + 1
        return new_steers

    return []


def drain_step_steers(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    state: Dict[str, Any],
    *,
    cwd: Path,
    quiet: bool = False,
) -> List[SteerEntry]:
    """Drain pending issue comments for the next orchestrator agentic step.

    No-op when *issue_number* or repo coordinates are missing (e.g. split flows).
    """
    if not repo_owner or not repo_name or not issue_number:
        return []
    steers = drain_issue_steers(repo_owner, repo_name, issue_number, state, cwd=cwd)
    if steers and not quiet:
        preview = ", ".join(f"@{entry.author}" for entry in steers[:3])
        suffix = f" (+{len(steers) - 3} more)" if len(steers) > 3 else ""
        console.print(
            f"[cyan]Incorporating mid-run feedback from {preview}{suffix}[/cyan]"
        )
        append_agentic_progress_steer_note(len(steers), preview + suffix)
    return steers


def load_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True
) -> Tuple[Optional[Dict], Optional[int]]:
    """
    Loads state from GitHub (priority) or local file.
    Returns (state_dict, github_comment_id).
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    # Try GitHub first
    if _should_use_github_state(use_github_state):
        gh_state, gh_id = github_load_state(repo_owner, repo_name, issue_number, workflow_type, cwd)
        if gh_state:
            # Cache locally
            try:
                state_dir.mkdir(parents=True, exist_ok=True)
                with open(local_file, "w") as f:
                    json.dump(gh_state, f, indent=2)
            except Exception:
                pass # Ignore local cache errors
            return gh_state, gh_id
    # Fallback to local
    if local_file.exists():
        try:
            with open(local_file, "r") as f:
                return json.load(f), None
        except Exception:
            pass
            
    return None, None

def save_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state: Dict,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True,
    github_comment_id: Optional[int] = None,
    *,
    dedupe: bool = False,
) -> Optional[int]:
    """
    Saves state to local file and GitHub.
    Returns updated github_comment_id.

    Pass ``dedupe=True`` when the caller has reason to suspect duplicate
    state markers may have appeared (e.g. clean restart, where a
    concurrent worker could have re-created a state comment between the
    pre-clear sweep and this save). When set AND ``github_comment_id``
    is None, the save path finds ALL existing state comments for this
    (issue, workflow), PATCHes the most-recent in place, and DELETEs the
    rest — converging to exactly one state comment regardless of prior
    races.
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    # 1. Save Local (atomic: write to tmp then rename)
    try:
        state_dir.mkdir(parents=True, exist_ok=True)
        tmp_file = local_file.with_suffix(".json.tmp")
        with open(tmp_file, "w") as f:
            json.dump(state, f, indent=2)
        tmp_file.replace(local_file)  # atomic on POSIX
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to save local state: {e}[/yellow]")

    # 2. Save GitHub
    if _should_use_github_state(use_github_state):
        new_id = github_save_state(
            repo_owner, repo_name, issue_number, workflow_type, state, cwd,
            github_comment_id, dedupe=dedupe,
        )
        if new_id:
            return new_id
        else:
            console.print("[dim]Warning: Failed to sync state to GitHub[/dim]")
            return None

    return github_comment_id

def clear_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True
) -> bool:
    """
    Clears local and GitHub state.

    Returns ``True`` when both the local file and (when enabled) the
    GitHub state comment(s) were successfully cleared or neutralised, so
    a subsequent ``load_workflow_state`` cannot replay stale cache.
    Returns ``False`` when the remote clear could not be confirmed (the
    GitHub comment could neither be deleted nor neutralised) — callers
    that must guarantee a fresh rerun can react to the failure.
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    local_ok = True
    # Clear Local
    if local_file.exists():
        try:
            os.remove(local_file)
        except Exception:
            local_ok = False

    # Clear GitHub
    github_ok = True
    if _should_use_github_state(use_github_state):
        github_ok = github_clear_state(
            repo_owner, repo_name, issue_number, workflow_type, cwd
        )

    return local_ok and github_ok


# ---------------------------------------------------------------------------
# Step-comment helpers (issue #964)
#
# Models used to post per-step GitHub issue comments themselves via shell
# commands embedded in their prompts. This is unreliable across providers (in
# particular Gemini's sandboxed shell cannot read GH_TOKEN). The orchestrator
# now owns these writes: providers emit a delimited `<step_report>…
# </step_report>` block that the orchestrator extracts, sanitizes, truncates,
# and posts via `post_step_comment(body=…)` using trusted credentials.
# ---------------------------------------------------------------------------

_STEP_REPORT_RE = re.compile(
    r"<step_report>(.*?)</step_report>",
    re.DOTALL | re.IGNORECASE,
)

_SECRET_PATTERNS: Tuple[Tuple["re.Pattern[str]", str], ...] = (
    (re.compile(r"\bghp_[A-Za-z0-9]{20,}"),                "[REDACTED_GITHUB_TOKEN]"),
    (re.compile(r"\bgithub_pat_[A-Za-z0-9_]{20,}"),        "[REDACTED_GITHUB_TOKEN]"),
    (re.compile(r"\b(?:gho_|ghu_|ghs_|ghr_)[A-Za-z0-9]{20,}"), "[REDACTED_GITHUB_TOKEN]"),
    (re.compile(r"\bAIza[A-Za-z0-9_\-]{20,}"),             "[REDACTED_GOOGLE_API_KEY]"),
    (re.compile(r"\bxai-[A-Za-z0-9]{20,}"),                "[REDACTED_XAI_KEY]"),
    (re.compile(r"\bsk-[A-Za-z0-9_\-]{20,}"),              "[REDACTED_OPENAI_KEY]"),
    (re.compile(r"\bgsk_[A-Za-z0-9]{20,}"),                "[REDACTED_GROQ_KEY]"),
)

_ENV_TOKEN_RE    = re.compile(r"\b(GH_TOKEN|GITHUB_TOKEN)\s*=\s*\S+")
_BEARER_TOKEN_RE = re.compile(r"(Authorization:\s*Bearer\s+)\S+", re.IGNORECASE)

_COMMENT_MAX_CHARS = 25_000
_TRUNCATED_MARKER = "\n\n…[truncated]"


def _extract_step_report(text: Optional[str]) -> Optional[str]:
    """Extract the LAST ``<step_report>…</step_report>`` block from text.

    Returns ``None`` if the input is empty or no tagged block is present. The
    extracted body has surrounding whitespace stripped so callers can rely on a
    clean payload. The regex is DOTALL + case-insensitive so the body can span
    multiple lines and providers can emit ``<STEP_REPORT>`` if they choose.
    """
    if not text:
        return None
    matches = _STEP_REPORT_RE.findall(text)
    if not matches:
        return None
    return matches[-1].strip()


# Public alias for orchestrator callers; same semantics as ``_extract_step_report``.
extract_step_report = _extract_step_report


def normalize_step_comments_state(raw: Any) -> Set[int]:
    """Coerce a persisted ``state["step_comments"]`` value into ``Set[int]``.

    Accepts every shape that has ever been persisted:

    * ``None`` / missing key            -> empty set.
    * ``list`` / ``tuple`` of ints      -> set of those ints.
    * ``set`` / ``frozenset``           -> defensive copy of int members.
    * Legacy bug-orchestrator dict, e.g.
      ``{"1": {"posted": True}, "2": {"failed_posted": True}}``
      -> set of int step numbers whose ``posted`` *or* ``failed_posted`` flag
      is truthy. Pending shapes (``fallback_pending`` / ``failed_pending``)
      are skipped so the orchestrator retries them on resume.
    * Malformed or unexpected inputs    -> empty set (never raises).

    ``bool`` is rejected even though it's an ``int`` subclass — the legacy
    dict shape uses booleans as flag values, not step numbers. ``float`` is
    rejected too — orchestrators with fractional steps must project them
    through a composite-key helper before storing.
    """
    if raw is None:
        return set()
    if isinstance(raw, dict):
        out: Set[int] = set()
        for key, value in raw.items():
            try:
                step = int(key)
            except (TypeError, ValueError):
                continue
            if isinstance(value, dict):
                if value.get("posted") is True or value.get("failed_posted") is True:
                    out.add(step)
            elif value is True:
                out.add(step)
        return out
    if isinstance(raw, (list, tuple, set, frozenset)):
        out = set()
        for item in raw:
            if isinstance(item, bool):
                continue
            if isinstance(item, int):
                out.add(item)
                continue
            if isinstance(item, str):
                try:
                    out.add(int(item))
                except ValueError:
                    continue
        return out
    return set()


def post_step_comment_once(
    *,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    step_num: int,
    body: str,
    posted_steps: Set[int],
    cwd: Path,
) -> bool:
    """Post a per-step success comment via ``gh issue comment``, exactly once.

    Idempotent: if ``step_num`` is already in ``posted_steps``, returns
    ``True`` immediately without invoking ``gh``. On a successful new post
    it mutates ``posted_steps`` in place (adds ``step_num``).

    Args:
        repo_owner: GitHub owner / org slug.
        repo_name: GitHub repository name.
        issue_number: Target issue number.
        step_num: Integer key that uniquely identifies this step within the
            workflow. Orchestrators with fractional or iterated steps must
            project their (step_num, iteration) tuples to a deterministic
            int before calling — the helper is ``Set[int]``-typed.
        body: Pre-built comment body. The helper applies its own redaction
            and truncation pass before shelling out; callers don't need to
            sanitize first.
        posted_steps: In-memory ``Set[int]`` of step keys already posted.
            Mutated in place on a successful new post.
        cwd: Working directory for the ``gh`` subprocess.

    Returns:
        ``True`` on success-or-already-posted, ``False`` on missing CLI or
        ``gh`` non-zero exit. Never raises; transient failures are logged
        via ``console.print`` and surfaced as ``False``.
    """
    if step_num in posted_steps:
        return True
    if os.environ.get("PDD_NO_GITHUB_STATE") == "1":
        posted_steps.add(step_num)
        return True
    if not _find_cli_binary("gh"):
        return False
    final_body = _sanitize_comment_body(body)
    try:
        result = subprocess.run(
            [
                "gh", "issue", "comment", str(issue_number),
                "--repo", f"{repo_owner}/{repo_name}",
                "--body", final_body,
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            console.print(
                f"[yellow]Warning: Failed to post step comment for step {step_num}: "
                f"{result.stderr}[/yellow]"
            )
            return False
    except Exception as exc:  # pylint: disable=broad-except
        console.print(
            f"[yellow]Warning: Failed to post step comment for step {step_num}: "
            f"{exc}[/yellow]"
        )
        return False
    posted_steps.add(step_num)
    return True


def _sanitize_comment_body(
    body: Optional[str],
    max_chars: int = _COMMENT_MAX_CHARS,
) -> str:
    """Redact known secret formats and truncate the body.

    Idempotent and conservative: only patterns that look like credentials are
    rewritten, and the function never raises. Truncation happens AFTER redaction
    so a secret near the end of an oversized payload still gets scrubbed.
    """
    if not body:
        return body or ""
    redacted = body
    for pat, repl in _SECRET_PATTERNS:
        redacted = pat.sub(repl, redacted)
    redacted = _ENV_TOKEN_RE.sub(lambda m: f"{m.group(1)}=[REDACTED]", redacted)
    redacted = _BEARER_TOKEN_RE.sub(lambda m: f"{m.group(1)}[REDACTED]", redacted)
    if len(redacted) > max_chars:
        # Reserve room for the marker so the returned length never exceeds the
        # caller-supplied cap (codex review of PR #966). When max_chars is
        # smaller than the marker itself, the marker won't fit either — the
        # final slice enforces the cap unconditionally.
        keep = max(0, max_chars - len(_TRUNCATED_MARKER))
        redacted = (redacted[:keep] + _TRUNCATED_MARKER)[:max_chars]
    return redacted


def post_step_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    step_num: int,
    total_steps: int,
    description: str,
    output: str,
    cwd: Path,
    body: Optional[str] = None,
) -> bool:
    """Post a per-step GitHub issue comment.

    Two modes:

    1. ``body is None`` (legacy / fallback path): used by orchestrators when
       the LLM agent itself failed and therefore could not produce a report.
       The body is the historical FAILED template, kept verbatim for backwards
       compatibility with existing callers (e.g. ``agentic_change_orchestrator``
       hard-stop paths).
    2. ``body is not None``: the orchestrator extracted a ``<step_report>``
       block from a successful run. The body is sanitized + truncated by the
       orchestrator's pipeline; here we additionally strip any leading
       duplicate ``## Step N`` header the model emitted and prepend our own
       canonical header so framing is consistent regardless of provider.

    Args:
        repo_owner: GitHub repository owner.
        repo_name: GitHub repository name.
        issue_number: Issue number to comment on.
        step_num: Current step number.
        total_steps: Total number of steps in the workflow.
        description: Human-readable step description (used in the header).
        output: Raw provider output (still used for the FAILED fallback path).
        cwd: Working directory for the ``gh`` subprocess.
        body: Optional pre-extracted, model-supplied report body. When set,
            takes precedence over the FAILED template.

    Returns:
        True if the comment posted successfully, False otherwise (including
        when ``gh`` is not on PATH).
    """
    if os.environ.get("PDD_NO_GITHUB_STATE") == "1":
        return True
    if not _find_cli_binary("gh"):
        return False

    if body is None:
        # Backwards-compatible fallback for agent-execution failures.
        error_detail = _sanitize_comment_body(output or "", max_chars=1000)
        final_body = (
            f"## Step {step_num}/{total_steps}: {description}\n\n"
            f"**Status:** FAILED\n\n"
            f"### Error Details\n"
            f"```\n{error_detail}\n```\n\n"
            f"---\n"
            f"*Automated fallback comment — agent did not execute for this step.*"
        )
    else:
        # Strip a single leading duplicate "## Step <N>..." line so the
        # orchestrator's canonical header isn't shadowed. Only the FIRST
        # occurrence is removed — interior headers (e.g. inside a fenced
        # block summarising another step) are preserved.
        leading_dup_re = re.compile(
            rf"^\s*##\s+Step\s+{re.escape(str(step_num))}\b[^\n]*\n+",
        )
        stripped = leading_dup_re.sub("", body, count=1)
        sanitized = _sanitize_comment_body(stripped)
        final_body = (
            f"## Step {step_num}/{total_steps}: {description}\n\n"
            f"{sanitized}\n\n"
            f"---\n"
            f"*Posted by PDD orchestrator (trusted credentials).*"
        )

    try:
        attempts = [
            [
                "gh", "issue", "comment", str(issue_number),
                "--repo", f"{repo_owner}/{repo_name}",
                "--body", final_body,
            ],
            [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
                "--method", "POST",
                "-f", f"body={final_body}",
            ],
        ]
        errors = []
        for cmd in attempts:
            result = subprocess.run(
                cmd,
                cwd=cwd,
                capture_output=True,
                text=True,
            )
            if result.returncode == 0:
                return True
            errors.append((result.stderr or result.stdout or "").strip())
        detail = " | ".join(err for err in errors if err)
        console.print(
            f"[yellow]Warning: Failed to post comment for step {step_num}: {detail}[/yellow]"
        )
        return False
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to post comment for step {step_num}: {e}[/yellow]")
        return False


def post_pr_comment(
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    body: str,
    cwd: Path,
) -> bool:
    """
    Post a comment on a pull request.

    Args:
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        pr_number: Pull request number to comment on
        body: Comment body
        cwd: Working directory for subprocess

    Returns:
        True if comment was posted successfully, False otherwise
    """
    if os.environ.get("PDD_NO_GITHUB_STATE") == "1":
        return True
    if not _find_cli_binary("gh"):
        return False

    sanitized_body = _sanitize_comment_body(body)
    attempts = [
        [
            "gh", "pr", "comment", str(pr_number),
            "--repo", f"{repo_owner}/{repo_name}",
            "--body", sanitized_body,
        ],
        [
            "gh", "issue", "comment", str(pr_number),
            "--repo", f"{repo_owner}/{repo_name}",
            "--body", sanitized_body,
        ],
        [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/{pr_number}/comments",
            "--method", "POST",
            "-f", f"body={sanitized_body}",
        ],
    ]
    errors = []
    try:
        for cmd in attempts:
            result = subprocess.run(
                cmd,
                cwd=cwd,
                capture_output=True,
                text=True,
            )
            if result.returncode == 0:
                return True
            errors.append((result.stderr or result.stdout or "").strip())
        detail = " | ".join(err for err in errors if err)
        console.print(f"[yellow]Warning: Failed to post PR comment: {detail}[/yellow]")
        return False
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to post PR comment: {e}[/yellow]")
        return False


def post_final_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    reason: str,
    total_cost: float,
    steps_completed: int,
    total_steps: int,
    cwd: Path,
) -> bool:
    """
    Post a final status comment when the workflow stops early.

    Unlike post_step_comment (which is for step-level failures where the agent
    didn't execute), this is for workflow-level outcomes: NOT_A_BUG, max cycles
    exhausted, missing loop control token, etc.

    Args:
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        issue_number: Issue number to comment on
        reason: Human-readable reason the workflow stopped
        total_cost: Total LLM cost incurred
        steps_completed: Last completed step number
        total_steps: Total number of steps in the workflow
        cwd: Working directory for subprocess

    Returns:
        True if comment was posted successfully, False otherwise
    """
    if not _find_cli_binary("gh"):
        return False

    body = (
        f"## Workflow Stopped\n\n"
        f"**Reason:** {reason}\n\n"
        f"**Progress:** Completed through step {steps_completed}/{total_steps}\n"
        f"**Total cost:** ${total_cost:.4f}\n\n"
        f"---\n"
        f"*Automated status comment — pdd-fix workflow exited early.*"
    )

    try:
        result = subprocess.run(
            [
                "gh", "issue", "comment", str(issue_number),
                "--repo", f"{repo_owner}/{repo_name}",
                "--body", body,
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            console.print(f"[yellow]Warning: Failed to post final comment: {result.stderr}[/yellow]")
            return False
        return True
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to post final comment: {e}[/yellow]")
        return False
