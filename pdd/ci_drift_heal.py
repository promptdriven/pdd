"""pdd/ci_drift_heal.py — CI script for detecting and auto-healing prompt/example drift.

Detects modules with prompt/example drift, heals them via subprocess calls to
`pdd update`/`pdd example`/`pdd auto-deps`/`pdd sync`, finalizes metadata via the
shared `run_metadata_sync` orchestrator (with per-module rollback on failure),
and commits and pushes the healed changes.

Invoked as `python -m pdd.ci_drift_heal`.
"""
from __future__ import annotations

import argparse
import csv
import math
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from rich.console import Console

console = Console()

_HEAL_SUBPROCESS_TIMEOUT = 1200
_HEAL_PROMPT_CHURN_MAX_RATIO_DEFAULT = 5.0
_AUTO_HEAL_SUCCESS_TRAILER = "PDD-Auto-Heal-Checkpoint: success"

_PROTECTED_PATHS = [".pdd/meta", "project_dependencies.csv"]
_INVARIANT_KEYS = {"include", "pdd_tags", "percent_markers", "fenced_blocks"}


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class DriftInfo:
    """Per-module drift record collected during detection."""

    basename: str
    language: str
    operation: str
    reason: str
    prompt_path: Optional[str] = None
    code_path: Optional[str] = None
    example_path: Optional[str] = None
    dependency_dir: Optional[str] = None
    diff_base: Optional[str] = None
    original_operation: Optional[str] = None
    estimated_cost: float = 0.0
    # Set True after `_run_metadata_sync_safe` reports a successful finalization
    # for this module; used by `main()` to drive commit-time staging verification.
    metadata_finalized: bool = False
    metadata_finalization_failed: bool = False
    metadata_finalization_error: str = ""


@dataclass
class HealResult:
    """Result of healing a single module."""

    basename: str
    success: bool
    cost: float = 0.0
    error: str = ""


class PromptRevertError(Exception):
    """Raised when reverting a prompt to HEAD fails or leaves the file dirty."""


# ---------------------------------------------------------------------------
# Repo / path helpers
# ---------------------------------------------------------------------------


def _repo_root() -> Path:
    """Return the repository root via `git rev-parse --show-toplevel`."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
        )
        if result.returncode == 0 and result.stdout.strip():
            return Path(result.stdout.strip())
    except Exception:
        pass
    return Path.cwd()


def _safe_basename(basename: str) -> str:
    """Flatten subdirectory basenames for metadata path semantics."""
    return basename.replace("/", "_").replace("\\", "_")


def _git_relative_path_candidates(path: Any, repo_root: Path) -> Set[str]:
    """Return repo-relative candidate paths (POSIX) for a possibly-symlinked path."""
    if path is None:
        return set()
    p = Path(path)
    candidates: Set[str] = set()
    if not p.is_absolute():
        try:
            candidates.add(p.as_posix())
        except Exception:
            pass
        # Try with repo_root prefix.
        try:
            joined = (repo_root / p).resolve()
            rel = joined.relative_to(repo_root.resolve())
            candidates.add(rel.as_posix())
        except Exception:
            pass
        try:
            joined = (repo_root / p)
            rel = joined.relative_to(repo_root)
            candidates.add(rel.as_posix())
        except Exception:
            pass
    else:
        # Try absolute → repo-relative (preserve symlink form).
        try:
            rel = p.relative_to(repo_root)
            candidates.add(rel.as_posix())
        except Exception:
            pass
        # Try resolved → repo-relative (canonical form).
        try:
            resolved = p.resolve()
            rel = resolved.relative_to(repo_root.resolve())
            candidates.add(rel.as_posix())
        except Exception:
            pass
    return {c for c in candidates if c}


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------


def _get_git_changed_files(diff_base: str) -> Set[str]:
    """Return repo-relative paths changed between diff_base and HEAD/working tree."""
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", diff_base],
            capture_output=True,
            text=True,
        )
    except Exception:
        return set()
    if result.returncode != 0:
        return set()
    stdout = getattr(result, "stdout", "") or ""
    if not isinstance(stdout, str):
        return set()
    return {line.strip() for line in stdout.splitlines() if line.strip()}


def _numstat_line_counts(args: List[str]) -> Optional[Tuple[int, int]]:
    """Run `git diff --numstat <args>` and return (added, deleted) totals."""
    try:
        cmd = ["git", "diff", "--numstat", *args]
        result = subprocess.run(cmd, capture_output=True, text=True)
    except Exception:
        return None
    if result.returncode != 0:
        return None
    stdout = getattr(result, "stdout", "") or ""
    if not isinstance(stdout, str):
        return None
    added = 0
    deleted = 0
    for line in stdout.splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        try:
            a = int(parts[0]) if parts[0] != "-" else 0
            d = int(parts[1]) if parts[1] != "-" else 0
        except ValueError:
            continue
        added += a
        deleted += d
    return (added, deleted)


def _git_show_prompt_at_head(prompt_path: Any) -> Optional[str]:
    """Return the HEAD version of prompt_path, or None if unavailable."""
    if not prompt_path:
        return None
    try:
        path_str = str(prompt_path)
        # Normalize absolute paths to repo-relative for git show.
        repo = _repo_root()
        rel = path_str
        try:
            p = Path(path_str)
            if p.is_absolute():
                rel = p.relative_to(repo).as_posix()
        except Exception:
            pass
        result = subprocess.run(
            ["git", "show", f"HEAD:{rel}"],
            capture_output=True,
            text=True,
        )
    except Exception:
        return None
    if result.returncode != 0:
        return None
    stdout = getattr(result, "stdout", None)
    if not isinstance(stdout, str):
        return None
    return stdout


# ---------------------------------------------------------------------------
# Module discovery / identity (lazy import)
# ---------------------------------------------------------------------------


def _discover_modules() -> List[Tuple[str, str, Any]]:
    """Discover (basename, language, prompt_path) tuples."""
    try:
        from pdd.user_story_tests import discover_prompt_files
    except ImportError:
        return []
    try:
        prompt_files = discover_prompt_files()
    except Exception:
        return []

    try:
        from pdd.operation_log import infer_module_identity
    except ImportError:
        return []

    out: List[Tuple[str, str, Any]] = []
    for entry in prompt_files:
        try:
            basename, language = infer_module_identity(str(entry))
        except Exception:
            continue
        out.append((basename, language, entry))
    return out


def _resolve_paths(basename: str, language: str) -> Dict[str, Optional[Any]]:
    """Resolve canonical paths via `get_pdd_file_paths`."""
    try:
        from pdd.sync_determine_operation import get_pdd_file_paths
    except ImportError:
        return {}
    try:
        raw = get_pdd_file_paths(basename, language)
    except Exception:
        return {}
    if isinstance(raw, dict):
        return raw
    return {}


# ---------------------------------------------------------------------------
# Drift detection
# ---------------------------------------------------------------------------


def _parse_modules_arg(modules: Optional[List[str]]) -> Optional[List[str]]:
    """Accept comma- and space-separated module lists."""
    if modules is None:
        return None
    out: List[str] = []
    for m in modules:
        for piece in m.replace(",", " ").split():
            piece = piece.strip()
            if piece:
                out.append(piece)
    return out or None


def _extract_op(decision: Any) -> Optional[str]:
    if decision is None:
        return None
    if isinstance(decision, str):
        return decision
    v = getattr(decision, "operation", None)
    if isinstance(v, str):
        return v
    if isinstance(decision, dict):
        v = decision.get("operation")
        if isinstance(v, str):
            return v
    return None


def _extract_reason(decision: Any) -> Optional[str]:
    if isinstance(decision, dict):
        return decision.get("reason")
    v = getattr(decision, "reason", None)
    if isinstance(v, str):
        return v
    return None


def detect_drift(
    modules: Optional[List[str]] = None,
    diff_base: Optional[str] = None,
) -> Tuple[List[DriftInfo], List[DriftInfo]]:
    """Detect drift across modules.

    Returns (prompt_drifts, example_drifts):
      - prompt_drifts: modules with operation == 'update'
      - example_drifts: everything else (example/auto-deps/verify/generate/test/crash)
    """
    parsed = _parse_modules_arg(modules)

    # Single git query if diff_base given.
    changed_files: Set[str] = set()
    if diff_base:
        changed_files = _get_git_changed_files(diff_base)

    discovered = _discover_modules()
    if parsed is not None:
        wanted = set(parsed)
        discovered = [t for t in discovered if t[0] in wanted]

    try:
        from pdd.sync_determine_operation import sync_determine_operation
    except ImportError:
        return [], []

    prompt_drifts: List[DriftInfo] = []
    example_drifts: List[DriftInfo] = []
    repo_root = _repo_root()

    for basename, language, prompt_path in discovered:
        try:
            decision = sync_determine_operation(
                basename, language, target_coverage=90.0, log_mode=True
            )
        except Exception:
            continue

        op = _extract_op(decision)
        if not op or op in ("nothing", "synced"):
            continue

        reason = _extract_reason(decision) or "drift detected"
        paths = _resolve_paths(basename, language)
        code_path_raw = paths.get("code")
        prompt_from_paths = paths.get("prompt") or prompt_path
        example_raw = paths.get("example")

        original_op = op

        # Git-based reclassification (clean-CI fingerprintless flows).
        # Only run when we successfully resolved canonical paths.
        if diff_base and code_path_raw is not None:
            code_in_changes = False
            for c in _git_relative_path_candidates(code_path_raw, repo_root):
                if c in changed_files:
                    code_in_changes = True
                    break
            prompt_in_changes = False
            if prompt_from_paths is not None:
                for c in _git_relative_path_candidates(prompt_from_paths, repo_root):
                    if c in changed_files:
                        prompt_in_changes = True
                        break

            if op != "update":
                if code_in_changes and not prompt_in_changes:
                    op = "update"
                    reason = "Code changed without prompt changes (git diff vs base)"

            if original_op in ("auto-deps", "generate"):
                if code_in_changes and prompt_in_changes:
                    op = "example"
                    reason = "Code and prompt changed together; only example refresh remains"
                elif prompt_in_changes and not code_in_changes:
                    op = "example"
                    reason = "Prompt changed without code changes; only example refresh remains"
                elif not code_in_changes and not prompt_in_changes:
                    continue

        drift = DriftInfo(
            basename=basename,
            language=language,
            operation=op,
            reason=reason,
            prompt_path=str(prompt_from_paths) if prompt_from_paths is not None else None,
            code_path=str(code_path_raw) if code_path_raw is not None else None,
            example_path=str(example_raw) if example_raw is not None else None,
            dependency_dir=str(paths.get("dependency_dir")) if paths.get("dependency_dir") else None,
            diff_base=diff_base,
            original_operation=original_op,
        )
        if op == "update":
            prompt_drifts.append(drift)
        else:
            example_drifts.append(drift)

    return prompt_drifts, example_drifts


# ---------------------------------------------------------------------------
# Subprocess invocation with protected-paths rollback
# ---------------------------------------------------------------------------


def _capture_rollback_state(cmd: List[str], env: Dict[str, str]) -> Optional[bool]:
    """Capture pre-subprocess clean-state for protected paths.

    Returns:
        None if rollback isn't applicable (env disabled, non-pdd command,
            or pdd subcommand not in {update, sync}).
        True if protected paths are clean (eligible to restore on failure).
        False if dirty (preserve user edits).
    """
    if env.get("PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE") != "1":
        return None
    if not cmd or cmd[0] != "pdd":
        return None
    # Skip top-level flags before the subcommand.
    i = 1
    while i < len(cmd):
        tok = cmd[i]
        if tok == "--force":
            i += 1
            continue
        if tok.startswith("--strength"):
            if "=" in tok:
                i += 1
            else:
                i += 2
            continue
        if tok.startswith("-"):
            # Generic value-taking flag.
            i += 2
            continue
        break
    if i >= len(cmd):
        return None
    subcommand = cmd[i]
    if subcommand not in ("update", "sync"):
        return None
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "--", *_PROTECTED_PATHS],
            capture_output=True,
            text=True,
        )
    except Exception:
        return False
    if result.returncode != 0:
        return False
    stdout = getattr(result, "stdout", "") or ""
    if not isinstance(stdout, str):
        return False
    return not stdout.strip()


def _restore_protected_paths() -> None:
    """Restore protected paths from HEAD."""
    try:
        subprocess.run(
            ["git", "restore", "--source=HEAD", "--", *_PROTECTED_PATHS],
            capture_output=True,
            text=True,
        )
    except Exception:
        pass


def _run_pdd_command(cmd: List[str], env: Dict[str, str], label: str) -> bool:
    """Run a `pdd ...` subprocess with protected-paths rollback on failure."""
    rollback_eligible = _capture_rollback_state(cmd, env)

    try:
        result = subprocess.run(
            cmd,
            env=env,
            capture_output=True,
            text=True,
            timeout=_HEAL_SUBPROCESS_TIMEOUT,
        )
        success = result.returncode == 0
        stderr = getattr(result, "stderr", "") or ""
    except subprocess.TimeoutExpired:
        success = False
        stderr = f"timeout after {_HEAL_SUBPROCESS_TIMEOUT}s"
    except FileNotFoundError:
        return False
    except Exception as exc:
        success = False
        stderr = str(exc)

    if not success:
        if rollback_eligible is True:
            _restore_protected_paths()
        if isinstance(stderr, str) and stderr:
            console.print(f"[red]{label} failed: {stderr.strip()[:300]}[/red]")
    return success


# ---------------------------------------------------------------------------
# Cost / environment helpers
# ---------------------------------------------------------------------------


def _parse_cost_from_csv(path: str) -> float:
    """Sum the per-operation cost column (or total_cost fallback)."""
    if not path:
        return 0.0
    p = Path(path)
    if not p.exists():
        return 0.0
    try:
        with p.open("r", encoding="utf-8", newline="") as f:
            reader = csv.DictReader(f)
            if reader.fieldnames is None:
                return 0.0
            field = "cost" if "cost" in reader.fieldnames else (
                "total_cost" if "total_cost" in reader.fieldnames else None
            )
            if field is None:
                return 0.0
            total = 0.0
            for row in reader:
                value = row.get(field, "")
                if value in (None, ""):
                    continue
                try:
                    total += float(value)
                except (TypeError, ValueError):
                    continue
            return total
    except Exception:
        return 0.0


def _build_ci_env(cost_path: str) -> Dict[str, str]:
    """Build the env dict for `pdd` subprocesses."""
    env = os.environ.copy()
    env["PDD_FORCE"] = "1"
    env["CI"] = "1"
    env["PDD_NO_INTERACTIVE"] = "1"
    env["NO_COLOR"] = "1"
    env["PDD_OUTPUT_COST_PATH"] = cost_path
    env["PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE"] = "1"
    env.setdefault("PDD_FORCE_LOCAL", "1")
    env.setdefault("PDD_SKIP_LOCAL_MODELS", "1")
    env.setdefault("PDD_HEAL_SKIP_EXISTING_EXAMPLE_DRIFT", "1")
    env.setdefault("PDD_HEAL_SKIP_REVIEW_ONLY_EXAMPLE_DRIFT", "1")
    return env


# ---------------------------------------------------------------------------
# Module-scoped metadata snapshot/restore
# ---------------------------------------------------------------------------


def _metadata_snapshot_paths(basename: str, language: str) -> Tuple[str, str, str]:
    """Return repo-relative (architecture, fingerprint, run_report) paths."""
    safe = _safe_basename(basename)
    fingerprint = f".pdd/meta/{safe}_{language}.json"
    run_report = f".pdd/meta/{safe}_{language}_run.json"
    return ("architecture.json", fingerprint, run_report)


def _snapshot_metadata_state_for(drift: Any) -> Dict[str, Optional[bytes]]:
    """Capture per-module bytes of architecture.json + fingerprint + run-report.

    Returns a dict keyed by repo-relative path; None values mean the file
    did not exist at snapshot time.
    """
    repo_root = _repo_root()
    basename = getattr(drift, "basename", "")
    language = getattr(drift, "language", "python")
    arch_rel, fp_rel, rr_rel = _metadata_snapshot_paths(basename, language)

    snapshot: Dict[str, Optional[bytes]] = {}
    for rel in (arch_rel, fp_rel, rr_rel):
        full = repo_root / rel
        if full.exists():
            try:
                snapshot[rel] = full.read_bytes()
            except Exception:
                snapshot[rel] = None
        else:
            snapshot[rel] = None
    return snapshot


def _restore_metadata_state_for(snapshot: Dict[str, Optional[bytes]]) -> None:
    """Restore the per-module bytes captured by `_snapshot_metadata_state_for`."""
    if not isinstance(snapshot, dict):
        return
    repo_root = _repo_root()
    for rel, content in snapshot.items():
        full = repo_root / rel
        if content is None:
            if full.exists():
                try:
                    full.unlink()
                except Exception:
                    pass
        else:
            try:
                full.parent.mkdir(parents=True, exist_ok=True)
                full.write_bytes(content)
            except Exception:
                pass


def _cleanup_metadata_artifacts(*_args: Any, **_kwargs: Any) -> None:
    """Legacy no-op shim retained for backward import compatibility."""
    return None


# ---------------------------------------------------------------------------
# Metadata finalization wrapper
# ---------------------------------------------------------------------------


def _run_metadata_sync_safe(
    prompt_path: Optional[str],
    code_path: Optional[str],
) -> bool:
    """Invoke the shared metadata-sync orchestrator. Returns True iff result.ok."""
    if not prompt_path:
        print("metadata finalization failed: prompt_path is unset")
        return False
    p = Path(prompt_path)
    if not p.exists():
        print(f"metadata finalization failed: prompt path {prompt_path} does not exist")
        return False

    try:
        from pdd.metadata_sync import run_metadata_sync
    except ImportError as exc:
        print(f"metadata finalization failed: metadata_sync unavailable ({exc})")
        return False

    code_p = Path(code_path) if code_path else None
    try:
        result = run_metadata_sync(p, code_p)
    except Exception as exc:
        print(f"metadata finalization failed: orchestrator raised: {exc}")
        return False

    ok = bool(getattr(result, "ok", False))
    if ok:
        try:
            basename = p.stem
        except Exception:
            basename = str(prompt_path)
        meta_rel = f".pdd/meta/{basename}.json"
        print(f"metadata finalized for {basename}: {meta_rel}")
        return True

    failing = getattr(result, "failing_stage", None) or "unknown"
    detail = ""
    stages = getattr(result, "stages", None)
    if isinstance(stages, dict) and failing in stages:
        s = stages[failing]
        detail = (getattr(s, "reason", None) or getattr(s, "detail", None) or "")
    print(f"metadata finalization failed: stage={failing} {detail}".strip())
    return False


# ---------------------------------------------------------------------------
# Prompt-content gates
# ---------------------------------------------------------------------------


def _revert_prompt_file(drift: Any) -> None:
    """Restore prompt to HEAD via git checkout."""
    prompt_path = getattr(drift, "prompt_path", None)
    basename = getattr(drift, "basename", "<unknown>")
    if not prompt_path:
        raise PromptRevertError(f"{basename}: prompt_path is None")
    repo_root = _repo_root()
    # Compute repo-relative path.
    try:
        p = Path(prompt_path)
        if p.is_absolute():
            rel = p.relative_to(repo_root).as_posix()
        else:
            rel = p.as_posix()
    except Exception:
        rel = str(prompt_path)

    try:
        r = subprocess.run(
            ["git", "checkout", "HEAD", "--", rel],
            capture_output=True,
            text=True,
        )
    except Exception as exc:
        raise PromptRevertError(f"{basename}: git checkout failed: {exc}")
    if r.returncode != 0:
        stderr = getattr(r, "stderr", "") or ""
        raise PromptRevertError(f"{basename}: git checkout failed: {stderr}")
    try:
        s = subprocess.run(
            ["git", "status", "--porcelain", "--", rel],
            capture_output=True,
            text=True,
        )
    except Exception as exc:
        raise PromptRevertError(f"{basename}: git status failed: {exc}")
    if s.returncode != 0:
        raise PromptRevertError(f"{basename}: git status failed")
    stdout = getattr(s, "stdout", "") or ""
    if isinstance(stdout, str) and stdout.strip():
        raise PromptRevertError(f"{basename}: prompt still dirty after revert: {stdout.strip()}")


def _enforce_prompt_churn_gate(drift: Any) -> bool:
    """Return True (gate passed/permissive) or False (gate violated, reverted)."""
    prompt_path = getattr(drift, "prompt_path", None)
    code_path = getattr(drift, "code_path", None)
    diff_base = getattr(drift, "diff_base", None)

    if not prompt_path or diff_base is None:
        return True

    try:
        ratio_max = float(os.environ.get(
            "PDD_HEAL_PROMPT_CHURN_MAX_RATIO",
            _HEAL_PROMPT_CHURN_MAX_RATIO_DEFAULT,
        ))
    except (TypeError, ValueError):
        ratio_max = _HEAL_PROMPT_CHURN_MAX_RATIO_DEFAULT

    prompt_counts = _numstat_line_counts(["HEAD", "--", str(prompt_path)])
    if prompt_counts is None:
        return True
    prompt_total = prompt_counts[0] + prompt_counts[1]
    if prompt_total == 0:
        return True

    if not code_path:
        return True
    code_counts = _numstat_line_counts([diff_base, "--", str(code_path)])
    if code_counts is None:
        return True
    code_total = code_counts[0] + code_counts[1]
    if code_total == 0:
        return True

    ratio = prompt_total / code_total
    if ratio > ratio_max:
        try:
            _revert_prompt_file(drift)
        except PromptRevertError:
            pass
        return False
    return True


def _enforce_structural_invariants(drift: Any) -> bool:
    """Return True if invariants hold; False (and revert) on violation."""
    prompt_path = getattr(drift, "prompt_path", None)
    if not prompt_path:
        return True

    pre = _git_show_prompt_at_head(prompt_path)
    if not isinstance(pre, str):
        return True

    try:
        post = Path(prompt_path).read_text(encoding="utf-8")
    except Exception:
        return True
    if not isinstance(post, str):
        return True

    skip_env = os.environ.get("PDD_HEAL_INVARIANTS_SKIP", "") or ""
    skip = {s.strip() for s in skip_env.split(",") if s.strip()} & _INVARIANT_KEYS

    violation = False

    if "include" not in skip:
        orig_inc = len(re.findall(r"<include(?:-many)?\b", pre))
        cur_inc = len(re.findall(r"<include(?:-many)?\b", post))
        if cur_inc < orig_inc:
            violation = True

    if not violation and "pdd_tags" not in skip:
        orig_tags = set(re.findall(r"<(pdd\.[A-Za-z0-9_]+)\b", pre))
        cur_tags = set(re.findall(r"<(pdd\.[A-Za-z0-9_]+)\b", post))
        if orig_tags - cur_tags:
            violation = True

    if not violation and "percent_markers" not in skip:
        orig_pct = len(re.findall(r"^\s*%", pre, flags=re.MULTILINE))
        cur_pct = len(re.findall(r"^\s*%", post, flags=re.MULTILINE))
        threshold = max(1, math.ceil(orig_pct / 2)) if orig_pct > 0 else 0
        if orig_pct > 0 and cur_pct < threshold:
            violation = True

    if not violation and "fenced_blocks" not in skip:
        orig_blocks = re.findall(r"```.*?```", pre, flags=re.DOTALL)
        for blk in orig_blocks:
            if blk not in post:
                violation = True
                break

    if violation:
        try:
            _revert_prompt_file(drift)
        except PromptRevertError:
            pass
        return False
    return True


# ---------------------------------------------------------------------------
# Heal dispatch
# ---------------------------------------------------------------------------


def _heal_skip_modules() -> Set[str]:
    raw = os.environ.get("PDD_HEAL_SYNC_SKIP_MODULES", "")
    return {p.strip() for p in raw.split(",") if p.strip()}


def _auto_deps_directory(drift: Any) -> str:
    """Resolve the directory passed to `pdd auto-deps`."""
    dep_dir = getattr(drift, "dependency_dir", None)
    if dep_dir:
        return str(dep_dir)
    return "context"


def _heal_update(drift: DriftInfo, env: Dict[str, str], skip_set: Set[str]) -> Optional[bool]:
    code_path = getattr(drift, "code_path", None)
    if not code_path:
        console.print(f"[red]heal failed for {drift.basename}: code_path unresolved[/red]")
        return False

    if not _run_pdd_command(
        ["pdd", "--force", "--strength", "0.5", "update", str(code_path)],
        env=env,
        label=f"pdd update {drift.basename}",
    ):
        return False

    # Lazy prompt_path resolution post-update (Requirement 8: only when prompt_path is None,
    # i.e. the code-without-prompt flow where `pdd update` just created the prompt).
    prompt_path = getattr(drift, "prompt_path", None)
    if not prompt_path:
        paths = _resolve_paths(drift.basename, drift.language)
        candidate = paths.get("prompt")
        # Use candidate.exists() directly so callers can hand back either a
        # real Path or a test double; converting to Path() first would lose
        # any test-injected .exists() override.
        try:
            candidate_exists = bool(candidate is not None and candidate.exists())
        except Exception:
            candidate_exists = False
        if not candidate_exists:
            console.print(
                f"[red]heal failed for {drift.basename}: prompt_path unresolvable post-update[/red]"
            )
            return False
        drift.prompt_path = str(candidate)
        prompt_path = drift.prompt_path

    # Gates.
    if not _enforce_prompt_churn_gate(drift):
        return False
    if not _enforce_structural_invariants(drift):
        return False

    # Snapshot + metadata orchestrator (only when prompt file exists on disk).
    snapshot: Optional[Dict[str, Optional[bytes]]] = None
    try:
        prompt_exists = Path(str(prompt_path)).exists()
    except Exception:
        prompt_exists = False
    if prompt_exists:
        snapshot = _snapshot_metadata_state_for(drift)
        meta_ok = _run_metadata_sync_safe(str(prompt_path), str(code_path) if code_path else None)
        if not meta_ok:
            try:
                _revert_prompt_file(drift)
            except PromptRevertError:
                raise
            if snapshot is not None:
                _restore_metadata_state_for(snapshot)
            # Metadata finalization is a hard requirement (Issue #1006): a
            # successful auto-heal commit must include the updated fingerprint,
            # so this failure must surface distinctly from advisory subprocess
            # failures and fail the run loudly in every mode.
            drift.metadata_finalization_failed = True
            drift.metadata_finalization_error = "metadata sync returned false"
            return False
        drift.metadata_finalized = True

    # Optional follow-up: skip when module bypassed via env.
    if drift.basename in skip_set:
        console.print(
            f"[dim]skipping follow-up pdd example for {drift.basename} "
            f"(PDD_HEAL_SYNC_SKIP_MODULES)[/dim]"
        )
        return True

    ok_ex = _run_pdd_command(
        [
            "pdd", "--force", "--strength", "0.5", "example",
            str(prompt_path), str(code_path),
        ],
        env=env,
        label=f"pdd example {drift.basename}",
    )
    if not ok_ex:
        try:
            _revert_prompt_file(drift)
        except PromptRevertError:
            raise
        if snapshot is not None:
            _restore_metadata_state_for(snapshot)
        return False
    return True


def _heal_example(drift: DriftInfo, env: Dict[str, str]) -> Optional[bool]:
    prompt_path = getattr(drift, "prompt_path", None)
    code_path = getattr(drift, "code_path", None)
    if not prompt_path or not code_path:
        console.print(f"[red]heal failed for {drift.basename}: paths unresolved[/red]")
        return False

    # CI bypass: review-only drift with an existing example.
    if env.get("PDD_HEAL_SKIP_REVIEW_ONLY_EXAMPLE_DRIFT") == "1":
        review_markers = (
            "Code and prompt changed together",
            "Prompt changed without code changes",
        )
        if any(m in (drift.reason or "") for m in review_markers):
            ex = getattr(drift, "example_path", None)
            if ex and Path(str(ex)).exists():
                return None

    # Broader bypass: any existing example.
    if env.get("PDD_HEAL_SKIP_EXISTING_EXAMPLE_DRIFT") == "1":
        ex = getattr(drift, "example_path", None)
        if ex and Path(str(ex)).exists():
            return None

    ok = _run_pdd_command(
        [
            "pdd", "--force", "--strength", "0.5", "example",
            str(prompt_path), str(code_path),
        ],
        env=env,
        label=f"pdd example {drift.basename}",
    )
    return ok if ok else False


def _heal_auto_deps(drift: DriftInfo, env: Dict[str, str]) -> Optional[bool]:
    prompt_path = getattr(drift, "prompt_path", None)
    if not prompt_path:
        console.print(f"[red]heal failed for {drift.basename}: prompt_path unresolved[/red]")
        return False
    dep_dir = _auto_deps_directory(drift)
    ok = _run_pdd_command(
        [
            "pdd", "--force", "--strength", "0.5", "auto-deps",
            str(prompt_path), str(dep_dir),
            "--output", str(prompt_path),
            "--csv", "project_dependencies.csv",
        ],
        env=env,
        label=f"pdd auto-deps {drift.basename}",
    )
    return ok if ok else False


def heal_module(drift: DriftInfo, env: Dict[str, str]) -> Optional[bool]:
    """Heal a single module. Returns True/False/None (skipped)."""
    skip_set = _heal_skip_modules()
    op = getattr(drift, "operation", "")

    # Modules explicitly skipped take precedence for non-update operations.
    if op != "update" and drift.basename in skip_set:
        return None

    if op == "update":
        return _heal_update(drift, env, skip_set)
    if op == "example":
        return _heal_example(drift, env)
    if op == "auto-deps":
        return _heal_auto_deps(drift, env)
    if op in ("verify", "generate", "test", "crash"):
        ok = _run_pdd_command(
            ["pdd", "--force", "--strength", "0.5", "sync", drift.basename],
            env=env,
            label=f"pdd sync {drift.basename}",
        )
        return ok if ok else False

    console.print(f"[red]unknown operation '{op}' for {drift.basename}[/red]")
    return False


# ---------------------------------------------------------------------------
# Commit + push
# ---------------------------------------------------------------------------


def commit_and_push(
    healed_modules: List[str],
    skip_ci: bool = False,
    checkpoint: bool = False,
    finalized_modules: Optional[List[Tuple[str, str]]] = None,
) -> bool:
    """Stage, commit, and push healed changes. Returns True on success.

    `finalized_modules` is a list of (basename, language) for modules that
    successfully finalized metadata. Their expected fingerprint paths must
    appear in the staged set or the commit aborts (Issue #1006).
    """
    if not healed_modules:
        return True

    try:
        r = subprocess.run(["git", "add", "-A"], capture_output=True, text=True)
    except Exception as exc:
        console.print(f"[red]git add failed: {exc}[/red]")
        return False
    if r.returncode != 0:
        console.print(f"[red]git add failed: {getattr(r, 'stderr', '')}[/red]")
        return False

    # Detect whether there's anything staged.
    try:
        diff = subprocess.run(
            ["git", "diff", "--cached", "--quiet"],
            capture_output=True,
            text=True,
        )
    except Exception as exc:
        console.print(f"[red]git diff --cached failed: {exc}[/red]")
        return False
    if diff.returncode == 0:
        # Nothing staged.
        return True

    # Metadata staging verification: every module that reported a successful
    # finalization must have its fingerprint file present in the staged set,
    # otherwise the commit could ship without the updated fingerprint
    # (Issue #1006). The fingerprint JSON includes a fresh timestamp on every
    # write, so a real finalization always produces a staged change.
    if finalized_modules:
        try:
            names = subprocess.run(
                ["git", "diff", "--cached", "--name-only"],
                capture_output=True,
                text=True,
            )
        except Exception as exc:
            console.print(f"[red]git diff --cached --name-only failed: {exc}[/red]")
            return False
        if names.returncode != 0:
            console.print(
                f"[red]git diff --cached --name-only failed: "
                f"{getattr(names, 'stderr', '')}[/red]"
            )
            return False
        stdout = getattr(names, "stdout", "") or ""
        staged_paths = {line.strip() for line in stdout.splitlines() if line.strip()}
        missing: List[str] = []
        for basename, language in finalized_modules:
            expected = f".pdd/meta/{_safe_basename(basename)}_{language}.json"
            if expected not in staged_paths:
                missing.append(expected)
        if missing:
            for path in missing:
                console.print(f"[red]metadata staging verification failed: missing {path}[/red]")
            return False

    module_str = ", ".join(healed_modules)
    headline = f"chore: auto-heal prompt/example drift for {module_str}"
    if skip_ci:
        headline = f"[skip ci] {headline}"

    msg_args = ["git", "commit", "-m", headline]
    if checkpoint:
        msg_args.extend(["-m", _AUTO_HEAL_SUCCESS_TRAILER])

    try:
        r = subprocess.run(msg_args, capture_output=True, text=True)
    except Exception as exc:
        console.print(f"[red]git commit failed: {exc}[/red]")
        return False
    if r.returncode != 0:
        text = (getattr(r, "stdout", "") or "") + (getattr(r, "stderr", "") or "")
        if "nothing to commit" in text.lower():
            return True
        console.print(f"[red]git commit failed: {getattr(r, 'stderr', '')}[/red]")
        return False

    try:
        r = subprocess.run(["git", "push"], capture_output=True, text=True)
    except Exception as exc:
        console.print(f"[red]git push failed: {exc}[/red]")
        return False
    if r.returncode != 0:
        console.print(f"[red]git push failed: {getattr(r, 'stderr', '')}[/red]")
        return False
    return True


# ---------------------------------------------------------------------------
# CLI argument parser
# ---------------------------------------------------------------------------


def _parse_args(argv: List[str]) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        prog="python -m pdd.ci_drift_heal",
        description="CI script for detecting and auto-healing prompt/example drift.",
    )
    parser.add_argument("--modules", nargs="*", default=None)
    parser.add_argument("--budget-cap", type=float, default=None)
    parser.add_argument("--skip-ci", action="store_true")
    parser.add_argument("--diff-base", default=None)

    ns = parser.parse_args(argv)
    if ns.modules is not None:
        ns.modules = _parse_modules_arg(ns.modules)
    return ns


# ---------------------------------------------------------------------------
# main entry point
# ---------------------------------------------------------------------------


def main(
    modules: Optional[List[str]] = None,
    budget_cap: Optional[float] = None,
    skip_ci: bool = False,
    diff_base: Optional[str] = None,
) -> int:
    """Detect drift, heal modules, and commit healed changes."""
    try:
        prompt_drifts, example_drifts = detect_drift(modules, diff_base=diff_base)
    except Exception as exc:
        console.print(f"[red]detect_drift failed: {exc}[/red]")
        return 1

    all_drifts: List[DriftInfo] = list(prompt_drifts) + list(example_drifts)
    if not all_drifts:
        return 0

    # Create per-run cost CSV.
    fd, cost_path = tempfile.mkstemp(prefix="pdd_ci_drift_heal_cost_", suffix=".csv")
    os.close(fd)
    Path(cost_path).write_text("operation,cost\n", encoding="utf-8")

    env = _build_ci_env(cost_path)

    healed: List[str] = []
    failed: List[str] = []
    skipped: List[str] = []
    finalized_modules: List[Tuple[str, str]] = []
    meta_failed: List[str] = []
    revert_blocks_commit = False
    skip_set = _heal_skip_modules()

    # Budget tracking: once cumulative cost (read from CSV after a heal) exceeds
    # the cap, all remaining modules are skipped as warnings. The cap is checked
    # AFTER each heal so the module that pushes us over the limit still runs;
    # remaining modules are then skipped without invoking heal_module. The CSV
    # path is fresh per run (mkstemp), so we use the absolute reading rather
    # than subtracting a baseline.
    budget_exceeded = False

    try:
        for drift in all_drifts:
            if budget_exceeded:
                skipped.append(drift.basename)
                continue

            try:
                result = heal_module(drift, env)
            except PromptRevertError:
                failed.append(drift.basename)
                revert_blocks_commit = True
                continue
            except Exception as exc:
                console.print(f"[red]heal_module raised for {drift.basename}: {exc}[/red]")
                failed.append(drift.basename)
                continue

            if result is None:
                skipped.append(drift.basename)
            elif result is True:
                healed.append(drift.basename)
                if drift.operation == "update" and drift.basename in skip_set:
                    skipped.append(drift.basename)
                if getattr(drift, "metadata_finalized", False):
                    finalized_modules.append((drift.basename, drift.language))
            else:
                failed.append(drift.basename)
                if getattr(drift, "metadata_finalization_failed", False):
                    reason = getattr(
                        drift,
                        "metadata_finalization_error",
                        "metadata sync returned false",
                    ) or "metadata sync returned false"
                    console.print(
                        f"[red]metadata finalization failed for {drift.basename}: {reason}[/red]"
                    )
                    meta_failed.append(drift.basename)

            # Post-heal budget check: if cumulative cost exceeds cap, latch the
            # flag so subsequent modules are skipped without invoking heal.
            if budget_cap is not None:
                current = _parse_cost_from_csv(cost_path)
                if current > budget_cap:
                    budget_exceeded = True
    finally:
        try:
            os.unlink(cost_path)
        except Exception:
            pass

    has_failures = bool(failed)
    has_healed = bool(healed)
    has_skipped = bool(skipped)
    is_pr_mode = not skip_ci

    if revert_blocks_commit:
        return 1

    # Metadata finalization is a hard requirement (Issue #1006): if it failed
    # for any module, fail loudly in every mode (PR and push-to-main/preflight)
    # without committing partial state from earlier modules.
    if meta_failed:
        return 1

    if is_pr_mode and has_failures:
        return 1

    # PR mode: partial success (any failed or skipped alongside healed)
    # skips the commit to avoid creating a bad checkpoint (Req 15).
    pr_partial_success = is_pr_mode and has_healed and (has_failures or has_skipped)
    if has_healed and not pr_partial_success:
        checkpoint = is_pr_mode and not has_failures and not has_skipped
        committed = commit_and_push(
            healed,
            skip_ci,
            checkpoint=checkpoint,
            finalized_modules=finalized_modules,
        )
        if not committed:
            return 1

    if has_failures and not is_pr_mode:
        # Push-to-main mode treats subprocess failures as advisory (exit 0).
        return 0
    return 0


if __name__ == "__main__":
    ns = _parse_args(sys.argv[1:])
    sys.exit(main(
        modules=ns.modules,
        budget_cap=ns.budget_cap,
        skip_ci=ns.skip_ci,
        diff_base=ns.diff_base,
    ))
