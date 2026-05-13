"""pdd/ci_drift_heal.py — Standalone CI script for drift detection and auto-healing.

Detects prompt/example drift across PDD modules and auto-heals via subprocess
calls to `pdd update`, `pdd example`, `pdd auto-deps`, and `pdd sync`. Designed
for use in CI pipelines (GitHub Actions etc.) with budget caps, git-based
reclassification of drift, and automatic commit/push.
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
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

from rich.console import Console
from rich.table import Table

console = Console()

# --------------------------------------------------------------------------- #
# Constants                                                                    #
# --------------------------------------------------------------------------- #

_HEAL_PROMPT_CHURN_MAX_RATIO_DEFAULT = 5.0
_SUBPROCESS_TIMEOUT_S = 1200
_AUTO_HEAL_SUCCESS_TRAILER = "PDD-Auto-Heal-Checkpoint: success"
_PROTECTED_PATHS: Tuple[str, ...] = (".pdd/meta", "project_dependencies.csv")
_HEAL_STRENGTH = "0.5"


# --------------------------------------------------------------------------- #
# Data classes / errors                                                        #
# --------------------------------------------------------------------------- #


@dataclass
class DriftInfo:
    """Information about one drifted module."""

    basename: str
    language: str
    operation: str
    reason: str
    code_path: Optional[str] = None
    prompt_path: Optional[str] = None
    example_path: Optional[str] = None
    test_path: Optional[str] = None
    diff_base: Optional[str] = None
    estimated_cost: float = 0.0
    extras: Dict[str, object] = field(default_factory=dict)


@dataclass
class HealResult:
    """Result of one heal attempt."""

    basename: str
    success: bool
    cost: float = 0.0
    error: str = ""


class PromptRevertError(RuntimeError):
    """Raised when a prompt cannot be safely reverted to HEAD."""


# --------------------------------------------------------------------------- #
# Generic helpers                                                              #
# --------------------------------------------------------------------------- #


def _env_truthy(name: str) -> bool:
    return os.environ.get(name, "").strip().lower() in {"1", "true", "yes", "on"}


def _env_skip_modules() -> Set[str]:
    raw = os.environ.get("PDD_HEAL_SYNC_SKIP_MODULES", "")
    return {tok.strip() for tok in raw.replace(",", " ").split() if tok.strip()}


def _env_invariant_skips() -> Set[str]:
    raw = os.environ.get("PDD_HEAL_INVARIANTS_SKIP", "")
    return {tok.strip().lower() for tok in raw.replace(",", " ").split() if tok.strip()}


def _repo_root() -> Path:
    """Return the git repository root, falling back to CWD."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            check=False,
            capture_output=True,
            text=True,
            timeout=15,
        )
        if result.returncode == 0 and result.stdout and result.stdout.strip():
            return Path(result.stdout.strip()).resolve()
    except (subprocess.SubprocessError, FileNotFoundError):
        pass
    return Path.cwd().resolve()


def _git_relative_path_candidates(path, repo_root) -> List[str]:
    """Return candidate repo-relative forms for ``path`` (incl. symlink target)."""
    if path is None:
        return []
    candidates: List[str] = []
    seen: Set[str] = set()
    p = Path(str(path))
    root = Path(str(repo_root))

    def _add(s: str) -> None:
        if s and s not in seen:
            seen.add(s)
            candidates.append(s)

    if not p.is_absolute():
        _add(p.as_posix())

    try:
        absolute = p if p.is_absolute() else (root / p)
        _add(absolute.relative_to(root).as_posix())
    except (ValueError, OSError):
        pass

    try:
        resolved = Path(os.path.realpath(str(p if p.is_absolute() else (root / p))))
        root_resolved = Path(os.path.realpath(str(root)))
        _add(resolved.relative_to(root_resolved).as_posix())
    except (ValueError, OSError):
        pass

    return candidates


def _to_repo_relative(path, repo_root) -> str:
    """Best-effort single repo-relative form for ``path``."""
    cands = _git_relative_path_candidates(path, repo_root)
    return cands[0] if cands else str(path)


# --------------------------------------------------------------------------- #
# Git change-set + cost CSV parsing                                            #
# --------------------------------------------------------------------------- #


def _get_git_changed_files(diff_base: str) -> Set[str]:
    """Return repo-relative paths reported as changed by ``git diff --name-only``."""
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", diff_base],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (subprocess.SubprocessError, FileNotFoundError):
        return set()
    if getattr(result, "returncode", 1) != 0:
        return set()
    return {line.strip() for line in (result.stdout or "").splitlines() if line.strip()}


def _parse_cost_from_csv(path) -> float:
    """Sum the ``cost`` (or ``total_cost``) column of a PDD cost CSV.

    Returns 0.0 on missing/empty/malformed input.
    """
    if path is None:
        return 0.0
    p = Path(str(path))
    if not p.exists():
        return 0.0
    total = 0.0
    try:
        with p.open("r", encoding="utf-8", newline="") as fh:
            content = fh.read()
            if not content.strip():
                return 0.0
            reader = csv.DictReader(content.splitlines())
            for row in reader:
                if not row:
                    continue
                value = row.get("cost") or row.get("Cost") or row.get("total_cost") or "0"
                try:
                    total += float(value)
                except (TypeError, ValueError):
                    continue
    except OSError:
        return 0.0
    return total


# --------------------------------------------------------------------------- #
# Environment construction                                                     #
# --------------------------------------------------------------------------- #


def _build_ci_env(cost_csv_path: str) -> Dict[str, str]:
    """Build the subprocess environment dict for CI heal commands."""
    env = os.environ.copy()
    env["PDD_FORCE"] = "1"
    env["CI"] = "1"
    env["PDD_NO_INTERACTIVE"] = "1"
    env["NO_COLOR"] = "1"
    env["PDD_OUTPUT_COST_PATH"] = str(cost_csv_path)
    env.setdefault("PDD_FORCE_LOCAL", "1")
    env.setdefault("PDD_SKIP_LOCAL_MODELS", "1")
    env["PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE"] = "1"
    env.setdefault("PDD_HEAL_SKIP_EXISTING_EXAMPLE_DRIFT", "1")
    env.setdefault("PDD_HEAL_SKIP_REVIEW_ONLY_EXAMPLE_DRIFT", "1")
    return env


# --------------------------------------------------------------------------- #
# Protected-paths rollback                                                     #
# --------------------------------------------------------------------------- #


def _is_pdd_subcommand(cmd: Sequence[str], subcommand: str) -> bool:
    """Detect ``pdd ... <subcommand> ...`` allowing top-level flags before it."""
    if not cmd or cmd[0] != "pdd":
        return False
    i = 1
    while i < len(cmd):
        token = cmd[i]
        if token == subcommand:
            return True
        if token.startswith("--"):
            if token in {"--force", "--quiet", "--verbose", "--no-color"}:
                i += 1
                continue
            i += 2
            continue
        return False
    return False


def _env_truthy_in_env(env: Dict[str, str], name: str) -> bool:
    return str(env.get(name, "")).strip().lower() in {"1", "true", "yes", "on"}


def _capture_rollback_state(cmd: Sequence[str], env: Dict[str, str]) -> Optional[bool]:
    """Return True/False (clean/dirty) when ``cmd`` is rollback-tracked; None otherwise."""
    if not (_is_pdd_subcommand(cmd, "update") or _is_pdd_subcommand(cmd, "sync")):
        return None
    if not _env_truthy_in_env(env, "PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE"):
        return None
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "--", *_PROTECTED_PATHS],
            capture_output=True,
            text=True,
            timeout=20,
        )
    except (subprocess.SubprocessError, FileNotFoundError):
        return False
    if getattr(result, "returncode", 1) != 0:
        return False
    return (result.stdout or "").strip() == ""


def _restore_protected_paths() -> None:
    """Restore protected paths from HEAD, falling back to ``git checkout``."""
    try:
        rc = subprocess.run(
            ["git", "restore", "--source=HEAD", "--", *_PROTECTED_PATHS],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if getattr(rc, "returncode", 1) == 0:
            return
    except (subprocess.SubprocessError, FileNotFoundError):
        pass
    try:
        subprocess.run(
            ["git", "checkout", "HEAD", "--", *_PROTECTED_PATHS],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (subprocess.SubprocessError, FileNotFoundError):
        pass


# --------------------------------------------------------------------------- #
# Subprocess runner                                                            #
# --------------------------------------------------------------------------- #


def _run_pdd_command(cmd: List[str], env: Dict[str, str], label: str) -> bool:
    """Run a ``pdd`` subprocess with optional protected-paths rollback."""
    rollback_eligible = _capture_rollback_state(cmd, env)
    console.print(f"[cyan]$ {' '.join(str(c) for c in cmd)}[/cyan]  [dim]({label})[/dim]")
    try:
        proc = subprocess.run(
            cmd,
            env=env,
            capture_output=True,
            text=True,
            timeout=_SUBPROCESS_TIMEOUT_S,
        )
    except subprocess.TimeoutExpired:
        console.print(f"[red]{label}: timed out after {_SUBPROCESS_TIMEOUT_S}s[/red]")
        if rollback_eligible:
            _restore_protected_paths()
        return False
    except (subprocess.SubprocessError, FileNotFoundError) as exc:
        console.print(f"[red]{label}: subprocess error: {exc}[/red]")
        if rollback_eligible:
            _restore_protected_paths()
        return False

    if getattr(proc, "returncode", 1) != 0:
        stderr = proc.stderr or ""
        console.print(
            f"[red]{label}: failed (rc={proc.returncode}): {stderr.strip()[-400:]}[/red]"
        )
        if rollback_eligible:
            _restore_protected_paths()
        return False
    return True


# --------------------------------------------------------------------------- #
# Prompt churn gate                                                            #
# --------------------------------------------------------------------------- #


def _numstat_line_counts(args: List[str]) -> Optional[Tuple[int, int]]:
    """Run ``git diff --numstat ARGS`` and aggregate (added, deleted)."""
    try:
        result = subprocess.run(
            ["git", "diff", "--numstat", *args],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (subprocess.SubprocessError, FileNotFoundError):
        return None
    if getattr(result, "returncode", 1) != 0:
        return None
    added = deleted = 0
    for line in (result.stdout or "").splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        try:
            added += int(parts[0]) if parts[0] != "-" else 0
            deleted += int(parts[1]) if parts[1] != "-" else 0
        except ValueError:
            continue
    return added, deleted


def _churn_max_ratio() -> float:
    raw = os.environ.get("PDD_HEAL_PROMPT_CHURN_MAX_RATIO", "").strip()
    if not raw:
        return _HEAL_PROMPT_CHURN_MAX_RATIO_DEFAULT
    try:
        return float(raw)
    except ValueError:
        return _HEAL_PROMPT_CHURN_MAX_RATIO_DEFAULT


def _enforce_prompt_churn_gate(drift: DriftInfo) -> bool:
    """Compare prompt churn (vs HEAD) against code churn (vs diff_base).

    Returns True when the gate passes or is permissively skipped. Returns
    False after reverting the prompt when the prompt-to-code ratio exceeds cap.
    """
    if not drift.prompt_path or not drift.code_path:
        return True

    prompt_counts = _numstat_line_counts(["HEAD", "--", str(drift.prompt_path)])
    if prompt_counts is None:
        return True
    prompt_churn = prompt_counts[0] + prompt_counts[1]
    if prompt_churn == 0:
        return True

    if not drift.diff_base:
        return True
    code_counts = _numstat_line_counts([drift.diff_base, "--", str(drift.code_path)])
    if code_counts is None:
        return True
    code_churn = code_counts[0] + code_counts[1]
    if code_churn <= 0:
        return True

    cap = _churn_max_ratio()
    ratio = prompt_churn / float(code_churn)
    if ratio > cap:
        console.print(
            f"[red]prompt churn gate tripped: {prompt_churn} prompt-lines / "
            f"{code_churn} code-lines = {ratio:.2f} > {cap:.2f}[/red]"
        )
        try:
            _revert_prompt_file(drift)
        except PromptRevertError as exc:
            console.print(f"[red]revert failed after churn gate: {exc}[/red]")
        return False
    return True


# --------------------------------------------------------------------------- #
# Structural invariants gate                                                   #
# --------------------------------------------------------------------------- #


_INCLUDE_TAG_RE = re.compile(r"<include(?:-many)?\b", re.IGNORECASE)
_PDD_OPEN_TAG_RE = re.compile(r"<pdd\.([A-Za-z0-9_\-\.]+)\b", re.IGNORECASE)
_PERCENT_MARKER_RE = re.compile(r"^\s*%\s+\S", re.MULTILINE)
_FENCED_BLOCK_RE = re.compile(r"```[\s\S]*?```", re.MULTILINE)
_KNOWN_INVARIANT_KEYS = {"include", "pdd_tags", "percent_markers", "fenced_blocks"}


def _git_show_prompt_at_head(prompt_path) -> Optional[str]:
    """Return prompt content at HEAD, or None on git failure."""
    if not prompt_path:
        return None
    repo_root = _repo_root()
    candidates = _git_relative_path_candidates(prompt_path, repo_root)
    if not candidates:
        candidates = [str(prompt_path)]
    for rel in candidates:
        try:
            result = subprocess.run(
                ["git", "show", f"HEAD:{rel}"],
                capture_output=True,
                text=True,
                timeout=20,
            )
        except (subprocess.SubprocessError, FileNotFoundError):
            return None
        if getattr(result, "returncode", 1) == 0:
            return result.stdout
    return None


def _enforce_structural_invariants(drift: DriftInfo) -> bool:
    """Compare on-disk prompt against HEAD; enforce four invariants.

    Returns True on pass / unavailable inputs. Returns False (after reverting)
    on any violation.
    """
    if not drift.prompt_path:
        return True
    pre = _git_show_prompt_at_head(drift.prompt_path)
    if pre is None:
        return True
    try:
        post = Path(str(drift.prompt_path)).read_text(encoding="utf-8")
    except OSError:
        return True

    raw_skips = _env_invariant_skips()
    skips = {s for s in raw_skips if s in _KNOWN_INVARIANT_KEYS}
    unknown = raw_skips - _KNOWN_INVARIANT_KEYS
    if unknown:
        console.print(
            f"[yellow]Unknown PDD_HEAL_INVARIANTS_SKIP entries ignored: "
            f"{sorted(unknown)}[/yellow]"
        )

    def _revert_and_fail(reason: str) -> bool:
        console.print(f"[red]structural invariants tripped: {reason}[/red]")
        try:
            _revert_prompt_file(drift)
        except PromptRevertError as exc:
            console.print(f"[red]revert failed after invariants: {exc}[/red]")
        return False

    if "include" not in skips:
        orig_includes = len(_INCLUDE_TAG_RE.findall(pre))
        new_includes = len(_INCLUDE_TAG_RE.findall(post))
        if new_includes < orig_includes:
            return _revert_and_fail(
                f"<include> tag count decreased {orig_includes} -> {new_includes}"
            )

    if "pdd_tags" not in skips:
        orig_tags = set(_PDD_OPEN_TAG_RE.findall(pre))
        new_tags = set(_PDD_OPEN_TAG_RE.findall(post))
        missing = orig_tags - new_tags
        if missing:
            return _revert_and_fail(f"missing <pdd.*> tags: {sorted(missing)[:5]}")

    if "percent_markers" not in skips:
        orig_markers = len(_PERCENT_MARKER_RE.findall(pre))
        if orig_markers:
            required = max(1, math.ceil(orig_markers / 2))
            new_markers = len(_PERCENT_MARKER_RE.findall(post))
            if new_markers < required:
                return _revert_and_fail(
                    f"% markers dropped {orig_markers} -> {new_markers} "
                    f"(need >= {required})"
                )

    if "fenced_blocks" not in skips:
        orig_blocks = _FENCED_BLOCK_RE.findall(pre)
        new_blocks = set(_FENCED_BLOCK_RE.findall(post))
        for block in orig_blocks:
            if block not in new_blocks:
                head_line = block.splitlines()[0] if block.splitlines() else block
                return _revert_and_fail(
                    f"fenced block missing/altered: {head_line[:60]!r}"
                )
    return True


# --------------------------------------------------------------------------- #
# Prompt revert                                                                #
# --------------------------------------------------------------------------- #


def _revert_prompt_file(drift: DriftInfo) -> None:
    """Restore ``drift.prompt_path`` to HEAD using git checkout."""
    if not drift.prompt_path:
        raise PromptRevertError("Cannot revert: prompt_path is None")
    repo_root = _repo_root()
    candidates = _git_relative_path_candidates(drift.prompt_path, repo_root)
    rel = candidates[0] if candidates else str(drift.prompt_path)

    try:
        rc = subprocess.run(
            ["git", "checkout", "HEAD", "--", rel],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (subprocess.SubprocessError, FileNotFoundError) as exc:
        raise PromptRevertError(f"git checkout failed for {rel}: {exc}") from exc
    if getattr(rc, "returncode", 1) != 0:
        raise PromptRevertError(
            f"git checkout failed for {rel}: rc={rc.returncode} stderr={(rc.stderr or '').strip()}"
        )

    try:
        status = subprocess.run(
            ["git", "status", "--porcelain", "--", rel],
            capture_output=True,
            text=True,
            timeout=20,
        )
    except (subprocess.SubprocessError, FileNotFoundError) as exc:
        raise PromptRevertError(f"git status failed for {rel}: {exc}") from exc
    if getattr(status, "returncode", 1) != 0 or (status.stdout or "").strip():
        raise PromptRevertError(
            f"prompt {rel} still dirty after revert: {(status.stdout or '').strip()}"
        )


def _operation_log_metadata_relpaths(basename: str, language: str) -> List[str]:
    """Return repo-relative metadata paths using operation_log naming."""
    from pdd.operation_log import _safe_basename

    safe_basename = _safe_basename(str(basename))
    language = str(language)
    return [
        f".pdd/meta/{safe_basename}_{language}.json",
        f".pdd/meta/{safe_basename}_{language}_run.json",
    ]


def _snapshot_metadata_state_for(drift: "DriftInfo") -> Dict[str, Optional[bytes]]:
    """Capture pre-heal bytes of files that ``run_metadata_sync`` may
    modify for THIS module — module-scoped so a failed module's rollback
    cannot wipe another module's successful writes during a multi-module
    push-to-main run.

    Files captured:
    - ``architecture.json`` (shared across modules; full-file snapshot
      because the orchestrator rewrites the whole file). At snapshot
      time this contains any earlier modules' successful writes from
      this run; restoring it on a later module's failure preserves
      those.
    - ``.pdd/meta/<safe_basename>_<language>.json`` (per-module
      fingerprint) and ``..._run.json`` (per-module run report), using
      the same subdirectory-safe basename semantics as
      :mod:`pdd.operation_log`. ``None`` value indicates the file did
      not exist pre-heal, so restore should remove the file rather than
      restore old bytes.

    Returns a dict mapping repo-relative POSIX path → file bytes
    (``None`` ⇒ file absent pre-heal). Used together with
    :func:`_restore_metadata_state_for`.
    """
    repo_root = _repo_root()
    snapshot: Dict[str, Optional[bytes]] = {}

    arch_path = repo_root / "architecture.json"
    try:
        snapshot["architecture.json"] = (
            arch_path.read_bytes() if arch_path.exists() else None
        )
    except OSError:
        snapshot["architecture.json"] = None

    basename = getattr(drift, "basename", None)
    language = getattr(drift, "language", None)
    if basename and language:
        for rel in _operation_log_metadata_relpaths(basename, language):
            metadata_path = repo_root / rel
            try:
                snapshot[rel] = (
                    metadata_path.read_bytes() if metadata_path.exists() else None
                )
            except OSError:
                snapshot[rel] = None

    return snapshot


def _restore_metadata_state_for(snapshot: Dict[str, Optional[bytes]]) -> None:
    """Restore files captured by :func:`_snapshot_metadata_state_for` to
    their pre-sync bytes. Module-scoped — never touches other modules'
    fingerprints or unrelated ``.pdd/meta`` entries. Best-effort: I/O
    failures during restore are swallowed because the caller has already
    decided to fail this module and additional exceptions here would
    mask the real reason.

    Empty/``None`` snapshot values mean "file did not exist pre-heal";
    restore removes the file in that case so that, e.g., a fingerprint
    finalize that ran before a later stage failed does not survive the
    rollback.
    """
    repo_root = _repo_root()
    for rel, data in snapshot.items():
        path = repo_root / rel
        try:
            if data is None:
                if path.exists():
                    path.unlink()
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
        except OSError:
            pass


def _cleanup_metadata_artifacts() -> None:
    """DEPRECATED — kept only so existing callers/tests that import this
    name keep resolving. The previous implementation did
    ``git restore .pdd`` and ``git restore architecture.json``, which is
    repository-scoped: in a multi-module push-to-main heal, restoring
    those paths to HEAD also wipes earlier modules' successful writes
    from this run. Use :func:`_snapshot_metadata_state_for` paired with
    :func:`_restore_metadata_state_for` instead — they capture the
    bytes for THIS module's protected paths so rollback is scoped.

    No-ops are safer than the old global restore: leaving the working
    tree as-is is the right default for callers that haven't yet been
    migrated to the snapshot/restore pattern.
    """
    return None


# --------------------------------------------------------------------------- #
# Module-identity helpers (used by detect_drift)                               #
# --------------------------------------------------------------------------- #


def _discover_prompt_files() -> List[Path]:
    """Discover prompt files via pdd.user_story_tests.discover_prompt_files."""
    try:
        from pdd.user_story_tests import discover_prompt_files  # type: ignore
    except Exception:
        return []
    try:
        result = discover_prompt_files()
    except Exception:
        return []
    return [Path(p) for p in result] if result else []


def _infer_module_identity(path: Path) -> Tuple[Optional[str], Optional[str]]:
    try:
        from pdd.operation_log import infer_module_identity  # type: ignore
    except Exception:
        return None, None
    try:
        basename, language = infer_module_identity(str(path))
        return basename, language
    except Exception:
        return None, None


def _sync_determine_operation(basename: str, language: str):
    """Call sync_determine_operation."""
    from pdd.sync_determine_operation import sync_determine_operation  # type: ignore

    return sync_determine_operation(
        basename, language, target_coverage=90.0, log_mode=True
    )


def _get_pdd_file_paths_safe(basename: str, language: str) -> Dict[str, object]:
    from pdd.sync_determine_operation import get_pdd_file_paths  # type: ignore

    result = get_pdd_file_paths(basename, language) or {}
    return result if isinstance(result, dict) else {}


def _decision_operation(decision: object) -> str:
    if isinstance(decision, dict):
        op = decision.get("operation") or decision.get("decision_type") or ""
    else:
        op = (
            getattr(decision, "operation", None)
            or getattr(decision, "decision_type", "")
            or ""
        )
    return str(op).strip().lower() if op else ""


def _decision_reason(decision: object) -> str:
    if isinstance(decision, dict):
        return str(decision.get("reason") or "")
    return str(getattr(decision, "reason", "") or "")


# --------------------------------------------------------------------------- #
# Detection                                                                    #
# --------------------------------------------------------------------------- #


def _path_in_changed(path, changed_files: Set[str], repo_root: Path) -> bool:
    if path is None:
        return False
    for cand in _git_relative_path_candidates(path, repo_root):
        if cand in changed_files:
            return True
    raw = str(path).replace(os.sep, "/")
    return raw in changed_files


def detect_drift(
    modules: Optional[List[str]] = None,
    diff_base: Optional[str] = None,
) -> Tuple[List[DriftInfo], List[DriftInfo]]:
    """Detect drift across PDD modules.

    Returns ``(prompt_drifts, example_drifts)`` where prompt_drifts contains
    modules with ``operation == 'update'`` and example_drifts contains
    everything else actionable (example / auto-deps / verify / generate /
    test / crash).
    """
    prompt_drifts: List[DriftInfo] = []
    example_drifts: List[DriftInfo] = []
    repo_root = _repo_root()

    prompt_files = _discover_prompt_files()

    selected_basenames = set(modules) if modules else None

    changed_files: Set[str] = set()
    if diff_base:
        changed_files = _get_git_changed_files(diff_base)

    visited: Set[Tuple[str, str]] = set()

    for prompt_file in prompt_files:
        basename, language = _infer_module_identity(prompt_file)
        if not basename or not language:
            continue
        if selected_basenames is not None and basename not in selected_basenames:
            continue

        try:
            decision = _sync_determine_operation(basename, language)
        except Exception as exc:
            console.print(
                f"[yellow]sync_determine_operation failed for {basename}: {exc}[/yellow]"
            )
            continue

        op = _decision_operation(decision)
        reason = _decision_reason(decision)
        if op in {"", "nothing", "noop", "none", "synced", "skip"}:
            continue

        paths_lookup: Dict[str, object] = {}
        path_lookup_failed = False
        try:
            paths_lookup = _get_pdd_file_paths_safe(basename, language)
        except Exception:
            path_lookup_failed = True

        def _pick(key: str) -> Optional[str]:
            value = paths_lookup.get(key) if isinstance(paths_lookup, dict) else None
            return str(value) if value is not None else None

        prompt_path = _pick("prompt") or str(prompt_file)
        code_path = _pick("code")
        example_path = _pick("example")
        test_path = _pick("test")

        drift = DriftInfo(
            basename=basename,
            language=language,
            operation=op,
            reason=reason,
            code_path=code_path,
            prompt_path=prompt_path,
            example_path=example_path,
            test_path=test_path,
            diff_base=diff_base,
        )

        if diff_base and not path_lookup_failed:
            code_changed = _path_in_changed(code_path, changed_files, repo_root)
            prompt_changed = _path_in_changed(prompt_path, changed_files, repo_root)

            if op != "update":
                if code_changed and not prompt_changed:
                    drift.operation = "update"
                    drift.reason = (
                        f"{reason} | git-reclassified to update: "
                        "code changed without prompt changes"
                    )
                elif op in {"auto-deps", "generate"}:
                    if code_changed and prompt_changed:
                        drift.operation = "example"
                        drift.reason = (
                            f"{reason} | git-reclassified to example: "
                            "Code and prompt changed together; refresh or skip example."
                        )
                    elif prompt_changed and not code_changed:
                        drift.operation = "example"
                        drift.reason = (
                            f"{reason} | git-reclassified to example: "
                            "Prompt changed without code changes; refresh or skip example."
                        )
                    elif not code_changed and not prompt_changed:
                        continue

        if drift.operation == "update":
            prompt_drifts.append(drift)
        else:
            example_drifts.append(drift)

        visited.add((basename, language))

    # Code-without-prompt scan (only when --modules specified).
    if modules:
        repo_pdd = repo_root / "pdd"
        if repo_pdd.exists():
            for basename in modules:
                if any(bn == basename for bn, _ in visited):
                    continue
                code_file = repo_pdd / f"{basename}.py"
                if not code_file.exists():
                    continue
                prompt_dir = repo_root / "prompts"
                if prompt_dir.exists() and list(prompt_dir.glob(f"{basename}_*.prompt")):
                    continue
                prompt_drifts.append(
                    DriftInfo(
                        basename=basename,
                        language="python",
                        operation="update",
                        reason="Code exists without prompt — needs pdd update",
                        code_path=str(code_file),
                        prompt_path=None,
                    )
                )

    return prompt_drifts, example_drifts


# --------------------------------------------------------------------------- #
# Healing                                                                      #
# --------------------------------------------------------------------------- #


def _strength_args() -> List[str]:
    return ["--force", "--strength", _HEAL_STRENGTH]


def _is_review_only_reason(reason: str) -> bool:
    needles = (
        "Code and prompt changed together",
        "Prompt changed without code changes",
    )
    return any(n in (reason or "") for n in needles)


def _auto_deps_directory() -> str:
    repo_root = _repo_root()
    if (repo_root / "context").exists():
        return "context"
    return "pdd"


def _run_metadata_sync_safe(prompt_path: Optional[str], code_path: Optional[str]) -> bool:
    """Invoke the metadata-sync orchestrator. Returns True only when every
    stage reports `ok`/`dry_run`/`skipped`.

    Fails closed on infrastructure errors:
    - missing prompt_path or non-existent prompt file → treated as a heal
      misconfiguration (False), so auto-heal does not silently checkpoint a
      module whose metadata was never finalized.
    - ImportError on `pdd.metadata_sync` → False with a logged reason; a
      missing orchestrator must not be confused with a successful no-op
      (that's exactly the bug-class #871 was wired up to prevent).
    """
    if not prompt_path:
        console.print(
            "[red]metadata_sync skipped: prompt_path is unset; refusing to "
            "checkpoint without finalization[/red]",
            soft_wrap=True,
        )
        return False
    try:
        from pdd.metadata_sync import run_metadata_sync  # type: ignore
    except Exception as exc:
        console.print(
            f"[red]metadata_sync unavailable (ImportError: {exc}); refusing "
            f"to checkpoint without finalization[/red]",
            soft_wrap=True,
        )
        return False
    p = Path(str(prompt_path))
    if not p.exists():
        console.print(
            f"[red]metadata_sync skipped: prompt file {p} does not exist; "
            f"refusing to checkpoint without finalization[/red]",
            soft_wrap=True,
        )
        return False
    try:
        result = run_metadata_sync(
            p, code_path=Path(str(code_path)) if code_path else None
        )
    except Exception as exc:
        console.print(f"[red]metadata_sync raised: {exc}[/red]")
        return False
    ok = bool(getattr(result, "ok", False))
    if not ok:
        failing = getattr(result, "failing_stage", "unknown")
        console.print(f"[red]metadata_sync failing stage: {failing}[/red]")
    return ok


def _resolve_prompt_path_after_update(drift: DriftInfo) -> Optional[str]:
    """Lazily resolve prompt_path after pdd update."""
    if drift.prompt_path:
        return drift.prompt_path
    try:
        paths = _get_pdd_file_paths_safe(drift.basename, drift.language)
    except Exception:
        return None
    p = paths.get("prompt") if isinstance(paths, dict) else None
    if p is None:
        return None
    try:
        exists = bool(p.exists()) if hasattr(p, "exists") else Path(str(p)).exists()
    except Exception:
        exists = False
    if not exists:
        return None
    return str(p)


def heal_module(drift: DriftInfo, env: Dict[str, str]) -> Optional[bool]:
    """Heal a single drifted module.

    Returns:
        True on success, False on failure, None when fully skipped via env policy.
    """
    skip_modules = _env_skip_modules()
    in_skip_set = drift.basename in skip_modules
    op = drift.operation

    console.print(f"[bold]Healing {drift.basename} ({op})[/bold] — {drift.reason}")

    # ------------------------------------------------------------------ #
    # update                                                              #
    # ------------------------------------------------------------------ #
    if op == "update":
        if not drift.code_path:
            console.print(
                f"[red]update heal aborted: code_path unresolved for {drift.basename}[/red]"
            )
            return False

        update_cmd = ["pdd", *_strength_args(), "update", str(drift.code_path)]
        if not _run_pdd_command(update_cmd, env, f"update {drift.basename}"):
            return False

        resolved_prompt = _resolve_prompt_path_after_update(drift)
        if not resolved_prompt:
            console.print(
                f"[red]update heal aborted: prompt_path still unresolved for "
                f"{drift.basename}[/red]"
            )
            return False
        drift.prompt_path = resolved_prompt

        prompt_exists = False
        try:
            prompt_exists = Path(str(resolved_prompt)).exists()
        except OSError:
            prompt_exists = False

        # Carries the pre-sync snapshot across both failure branches
        # below (sync-fail AND example-regen fail). None when prompt did
        # not exist (no sync ran) or when prompt_exists was False — in
        # which case _restore_metadata_state_for is simply skipped.
        metadata_snapshot: Optional[Dict[str, Optional[bytes]]] = None

        if prompt_exists:
            if not _enforce_prompt_churn_gate(drift):
                return False
            if not _enforce_structural_invariants(drift):
                return False
            # Snapshot architecture.json + this module's fingerprint BEFORE
            # invoking run_metadata_sync so a failure can be rolled back
            # without touching other modules' state. A repo-scoped restore
            # (the previous approach) would, in a multi-module
            # push-to-main heal, wipe earlier successful modules' writes
            # from this run when a later module's sync failed.
            metadata_snapshot = _snapshot_metadata_state_for(drift)
            if not _run_metadata_sync_safe(resolved_prompt, drift.code_path):
                _revert_prompt_file(drift)
                _restore_metadata_state_for(metadata_snapshot)
                return False

        if in_skip_set:
            console.print(
                f"[yellow]Skipping follow-up example for {drift.basename} "
                f"(PDD_HEAL_SYNC_SKIP_MODULES)[/yellow]"
            )
            drift.extras["update_followup_skipped"] = True
            return True

        example_cmd = [
            "pdd",
            *_strength_args(),
            "example",
            str(resolved_prompt),
            str(drift.code_path),
        ]
        if not _run_pdd_command(example_cmd, env, f"example {drift.basename}"):
            # Roll back BOTH the prompt and the per-module metadata
            # writes that landed before the example regen failed. Use
            # the module-scoped snapshot taken pre-sync so we don't
            # erase other modules' state on a multi-module push-to-main
            # heal (see _snapshot_metadata_state_for for the scope
            # contract). metadata_snapshot is None when prompt_exists
            # was False — in that case run_metadata_sync never ran and
            # there is nothing module-scoped to roll back.
            _revert_prompt_file(drift)
            if metadata_snapshot is not None:
                _restore_metadata_state_for(metadata_snapshot)
            return False
        return True

    # ------------------------------------------------------------------ #
    # example                                                             #
    # ------------------------------------------------------------------ #
    if op == "example":
        if not drift.prompt_path or not drift.code_path:
            console.print(
                f"[red]example heal aborted: prompt={drift.prompt_path} "
                f"code={drift.code_path}[/red]"
            )
            return False

        review_only_skip = _env_truthy_in_env(env, "PDD_HEAL_SKIP_REVIEW_ONLY_EXAMPLE_DRIFT")
        existing_skip = _env_truthy_in_env(env, "PDD_HEAL_SKIP_EXISTING_EXAMPLE_DRIFT")

        example_exists = False
        if drift.example_path:
            try:
                example_exists = Path(str(drift.example_path)).exists()
            except OSError:
                example_exists = False

        if in_skip_set:
            console.print(
                f"[yellow]Skipping example heal for {drift.basename} "
                f"(PDD_HEAL_SYNC_SKIP_MODULES)[/yellow]"
            )
            return None

        if review_only_skip and _is_review_only_reason(drift.reason) and example_exists:
            console.print(
                f"[yellow]Skipping example heal for {drift.basename}: "
                "reviewed PR artifact already present.[/yellow]"
            )
            return None
        if existing_skip and example_exists:
            console.print(
                f"[yellow]Skipping example heal for {drift.basename}: "
                "example already exists.[/yellow]"
            )
            return None

        cmd = [
            "pdd",
            *_strength_args(),
            "example",
            str(drift.prompt_path),
            str(drift.code_path),
        ]
        if not _run_pdd_command(cmd, env, f"example {drift.basename}"):
            return False
        return True

    # ------------------------------------------------------------------ #
    # auto-deps                                                           #
    # ------------------------------------------------------------------ #
    if op == "auto-deps":
        if not drift.prompt_path:
            console.print(
                f"[red]auto-deps heal aborted: prompt_path unresolved for "
                f"{drift.basename}[/red]"
            )
            return False
        dep_dir = _auto_deps_directory()
        cmd = [
            "pdd",
            *_strength_args(),
            "auto-deps",
            str(drift.prompt_path),
            dep_dir,
            "--output",
            str(drift.prompt_path),
            "--csv",
            "project_dependencies.csv",
        ]
        if not _run_pdd_command(cmd, env, f"auto-deps {drift.basename}"):
            return False
        return True

    # ------------------------------------------------------------------ #
    # verify / generate / test / crash → pdd sync                          #
    # ------------------------------------------------------------------ #
    if op in {"verify", "generate", "test", "crash"}:
        if in_skip_set:
            console.print(
                f"[yellow]Skipping pdd sync for {drift.basename} "
                f"(PDD_HEAL_SYNC_SKIP_MODULES)[/yellow]"
            )
            return None
        cmd = ["pdd", *_strength_args(), "sync", drift.basename]
        if not _run_pdd_command(cmd, env, f"sync {drift.basename}"):
            return False
        return True

    console.print(f"[yellow]Unknown operation '{op}' for {drift.basename}[/yellow]")
    return False


# --------------------------------------------------------------------------- #
# Commit + push                                                                #
# --------------------------------------------------------------------------- #


def _current_branch() -> Optional[str]:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            capture_output=True,
            text=True,
            timeout=15,
        )
        if getattr(result, "returncode", 1) == 0:
            branch = (result.stdout or "").strip()
            if branch and branch != "HEAD":
                return branch
    except (subprocess.SubprocessError, FileNotFoundError):
        pass
    return None


def commit_and_push(
    healed_modules: List[str],
    skip_ci: bool = False,
    checkpoint: bool = False,
) -> bool:
    """git add -A, commit (optionally with checkpoint trailer), push."""
    if not healed_modules:
        console.print("[yellow]Nothing to commit (no modules healed).[/yellow]")
        return True

    try:
        rc_add = subprocess.run(
            ["git", "add", "-A"],
            capture_output=True,
            text=True,
            timeout=60,
        )
        if getattr(rc_add, "returncode", 1) != 0:
            console.print(f"[red]git add failed: {(rc_add.stderr or '').strip()}[/red]")
            return False

        rc_stat = subprocess.run(
            ["git", "diff", "--cached", "--quiet"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if getattr(rc_stat, "returncode", 1) == 0:
            console.print("[yellow]No staged changes; skipping commit.[/yellow]")
            return True

        modules_str = ", ".join(healed_modules)
        subject = f"chore: auto-heal prompt/example drift for {modules_str}"
        if skip_ci:
            subject = f"[skip ci] {subject}"

        commit_cmd = ["git", "commit", "-m", subject]
        if checkpoint:
            commit_cmd += ["-m", _AUTO_HEAL_SUCCESS_TRAILER]

        rc_commit = subprocess.run(
            commit_cmd,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if getattr(rc_commit, "returncode", 1) != 0:
            console.print(
                f"[red]git commit failed: {(rc_commit.stderr or '').strip()}[/red]"
            )
            return False
        console.print(f"[green]Committed: {subject}[/green]")

        push_cmd = ["git", "push"]
        rc_push = subprocess.run(
            push_cmd,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if getattr(rc_push, "returncode", 1) != 0:
            console.print(f"[red]git push failed: {(rc_push.stderr or '').strip()}[/red]")
            return False
        console.print("[green]Pushed to remote.[/green]")
        return True
    except subprocess.TimeoutExpired as exc:
        console.print(f"[red]git operation timed out: {exc}[/red]")
        return False
    except (subprocess.SubprocessError, FileNotFoundError) as exc:
        console.print(f"[red]git operation failed: {exc}[/red]")
        return False


# --------------------------------------------------------------------------- #
# Output                                                                       #
# --------------------------------------------------------------------------- #


def _print_drift_table(
    prompt_drifts: Sequence[DriftInfo],
    example_drifts: Sequence[DriftInfo],
) -> None:
    drifts: List[DriftInfo] = list(prompt_drifts) + list(example_drifts)
    if not drifts:
        return
    table = Table(title="Detected Drift", show_lines=False)
    table.add_column("Module", style="cyan")
    table.add_column("Op", style="magenta")
    table.add_column("Reason", overflow="fold")
    for d in drifts:
        table.add_row(d.basename, d.operation, d.reason or "")
    console.print(table)


# --------------------------------------------------------------------------- #
# Main                                                                         #
# --------------------------------------------------------------------------- #


def main(
    modules: Optional[List[str]] = None,
    budget_cap: Optional[float] = None,
    skip_ci: bool = False,
    diff_base: Optional[str] = None,
) -> int:
    """Entry point. Returns 0 on success, 1 on failure (PR mode)."""
    console.print("[bold cyan]PDD CI Drift Heal[/bold cyan]")
    console.print(
        f"modules={modules or 'ALL'}  budget_cap={budget_cap}  "
        f"skip_ci={skip_ci}  diff_base={diff_base or '-'}"
    )

    try:
        prompt_drifts, example_drifts = detect_drift(modules, diff_base=diff_base)
    except Exception as exc:
        console.print(f"[red]Drift detection failed: {exc}[/red]")
        return 1

    all_drifts: List[DriftInfo] = list(prompt_drifts) + list(example_drifts)
    if not all_drifts:
        console.print("[green]No drift detected. Nothing to heal.[/green]")
        return 0

    _print_drift_table(prompt_drifts, example_drifts)

    fd, cost_path = tempfile.mkstemp(prefix="pdd_heal_cost_", suffix=".csv")
    try:
        os.close(fd)
    except Exception:
        pass
    try:
        Path(cost_path).write_text("", encoding="utf-8")
    except Exception:
        pass

    env = _build_ci_env(cost_path)

    for d in all_drifts:
        if d.diff_base is None:
            d.diff_base = diff_base

    healed: List[str] = []
    failed: List[Tuple[str, str]] = []
    skipped: List[str] = []
    revert_failure = False

    try:
        budget_exceeded = False
        for drift in all_drifts:
            if budget_exceeded:
                console.print(
                    f"[yellow]Budget cap ${budget_cap:.2f} reached. "
                    f"Skipping {drift.basename}.[/yellow]"
                )
                skipped.append(drift.basename)
                continue

            try:
                result = heal_module(drift, env)
            except PromptRevertError as exc:
                console.print(
                    f"[red]Prompt revert error for {drift.basename}: {exc}[/red]"
                )
                revert_failure = True
                failed.append((drift.basename, f"PromptRevertError: {exc}"))
                continue
            except Exception as exc:
                console.print(
                    f"[red]Unexpected exception healing {drift.basename}: {exc}[/red]"
                )
                failed.append((drift.basename, str(exc)))
                continue

            if result is True:
                healed.append(drift.basename)
                skip_modules = _env_skip_modules()
                if drift.operation == "update" and drift.basename in skip_modules:
                    drift.extras["update_followup_skipped"] = True
                if drift.extras.get("update_followup_skipped"):
                    skipped.append(drift.basename)
            elif result is False:
                failed.append((drift.basename, drift.reason))
            else:
                skipped.append(drift.basename)

            if budget_cap is not None:
                cumulative_cost = _parse_cost_from_csv(cost_path)
                if cumulative_cost >= budget_cap:
                    console.print(
                        f"[yellow]Budget cap ${budget_cap:.2f} reached "
                        f"(cumulative=${cumulative_cost:.4f}).[/yellow]"
                    )
                    budget_exceeded = True
    finally:
        try:
            os.unlink(cost_path)
        except Exception:
            pass

    console.print()
    console.print(
        f"[green]Healed: {len(healed)}[/green]  "
        f"[red]Failed: {len(failed)}[/red]  "
        f"[yellow]Skipped: {len(skipped)}[/yellow]"
    )

    pr_mode = not skip_ci
    has_failures = bool(failed) or revert_failure
    has_skips = bool(skipped)

    if revert_failure:
        console.print(
            "[red]PromptRevertError(s) detected — refusing to commit.[/red]"
        )
        return 1

    if not healed:
        return 1 if has_failures else 0

    if pr_mode:
        if has_failures:
            console.print(
                "[red]PR mode + failures present: not committing partial heal.[/red]"
            )
            return 1
        if has_skips:
            console.print(
                "[yellow]PR mode + skipped modules: not creating success checkpoint.[/yellow]"
            )
            return 0
        ok = commit_and_push(healed, False, checkpoint=True)
        return 0 if ok else 1

    ok = commit_and_push(healed, True, checkpoint=False)
    return 0 if ok else 1


# --------------------------------------------------------------------------- #
# CLI                                                                          #
# --------------------------------------------------------------------------- #


def _expand_modules(values: Optional[Iterable[str]]) -> Optional[List[str]]:
    if not values:
        return None
    out: List[str] = []
    for v in values:
        for piece in str(v).replace(",", " ").split():
            piece = piece.strip()
            if piece:
                out.append(piece)
    return out or None


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="pdd.ci_drift_heal",
        description="Detect and auto-heal PDD prompt/example drift in CI.",
    )
    parser.add_argument(
        "--modules",
        nargs="*",
        default=None,
        help="Module basenames (space- or comma-separated). Default: all.",
    )
    parser.add_argument(
        "--budget-cap",
        type=float,
        default=None,
        help="Cumulative LLM cost cap in dollars.",
    )
    parser.add_argument(
        "--skip-ci",
        action="store_true",
        help="Push-to-main mode: prepend [skip ci]; failures advisory.",
    )
    parser.add_argument(
        "--diff-base",
        type=str,
        default=None,
        help="Git ref for git-based drift reclassification.",
    )
    ns = parser.parse_args(list(argv))
    ns.modules = _expand_modules(ns.modules)
    return ns


def _cli(argv: Optional[Sequence[str]] = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    return main(
        modules=args.modules,
        budget_cap=args.budget_cap,
        skip_ci=bool(args.skip_ci),
        diff_base=args.diff_base,
    )


if __name__ == "__main__":
    sys.exit(_cli())
