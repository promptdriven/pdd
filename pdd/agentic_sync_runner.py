"""
Async sync runner: parallel module sync with dependency-aware scheduling.

Manages concurrent `pdd sync` subprocesses, respects dependency ordering,
updates a live GitHub issue comment with progress, and pauses on failure.
"""
from __future__ import annotations

import csv as _csv
import datetime
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections import defaultdict
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, NamedTuple, Optional, Set, Tuple

from rich.console import Console

from .agentic_common import (
    DEFAULT_SYNC_COMPANION_ALLOWLIST,
    PDD_INTERNAL_PATH_ALLOWLIST,
    _is_valid_companion_pattern,
    _matches_companion_pattern_anchored,
    _revert_out_of_scope_changes,
)
from .agentic_common_worktree import revert_out_of_scope_changes_with_dirs
from .construct_paths import _is_known_language

console = Console()

# ---------------------------------------------------------------------------
# Module-level constants and helpers
# ---------------------------------------------------------------------------

# Maximum concurrent syncs
MAX_WORKERS = 4

# Heartbeat interval for printing progress hints during long-running modules
HEARTBEAT_INTERVAL = 60

# Architecture-conformance retry cap
MAX_CONFORMANCE_ATTEMPTS = 3

# GitHub accepts comments up to 65,536 characters. Keep a buffer for CLI/API
# encoding overhead and future footer text.
GITHUB_COMMENT_BODY_LIMIT = 60000
GITHUB_FAILED_DETAIL_PER_MODULE_LIMIT = 8000
GITHUB_FAILED_DETAIL_MIN_CHARS = 600

# Per-module timeout in seconds. Default 45 min, override via env.
try:
    MODULE_TIMEOUT = int(os.environ.get("PDD_MODULE_TIMEOUT_SECONDS", "2700"))
except ValueError:
    MODULE_TIMEOUT = 2700

# State file for resumability (relative to project root)
STATE_FILE_PATH = Path(".pdd/agentic_sync_state.json")

# Regex matching lines composed entirely of box-drawing / table characters
# (Rich Panel borders, table separators, etc.) — used to skip them in heartbeat.
_BOX_CHARS_RE = re.compile(r'^[\s╭╮╰╯─│┌┐└┘├┤┬┴┼═║╔╗╚╝╠╣╦╩╬\-|+]*$')

# Substrings that mark a child stdout/stderr line as a known nonfatal warning.
_NONFATAL_WARNING_SUBSTRINGS: Tuple[str, ...] = (
    "ContentSelector failed",
)


def _is_nonfatal_warning(line: str) -> bool:
    """Return True if `line` matches a known nonfatal-warning substring."""
    return any(s in line for s in _NONFATAL_WARNING_SUBSTRINGS)


def _cap_github_comment_body(body: str) -> str:
    """Return a GitHub issue-comment body that cannot exceed GitHub's limit."""
    if len(body) <= GITHUB_COMMENT_BODY_LIMIT:
        return body
    suffix = (
        "\n\n_Comment truncated to fit GitHub's size limit. "
        "See workflow logs for full output._"
    )
    keep = max(GITHUB_COMMENT_BODY_LIMIT - len(suffix), 0)
    return body[:keep].rstrip() + suffix


def _run_gh_command(args: List[str], timeout: int = 30) -> Tuple[bool, str]:
    """
    Execute a gh CLI command at module scope so tests can patch this symbol.

    Returns:
        Tuple of (success, output). Output is stdout on success, stderr on failure.
    """
    try:
        result = subprocess.run(
            ["gh"] + list(args),
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout,
        )
        if result.returncode != 0:
            return False, (result.stderr or "").strip()
        return True, (result.stdout or "").strip()
    except subprocess.TimeoutExpired:
        return False, f"gh command timed out after {timeout}s"
    except Exception as exc:  # pragma: no cover - defensive
        return False, str(exc)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------


@dataclass
class ModuleState:
    """Tracks the execution state of a single module sync."""

    status: str = "pending"  # pending, running, success, failed
    start_time: Optional[float] = None
    end_time: Optional[float] = None
    cost: float = 0.0
    error: Optional[str] = None
    current_phase: Optional[str] = None
    completed_phases: List[str] = field(default_factory=list)


class DepGraphFromArchitectureResult(NamedTuple):
    """Dependency subgraph from architecture.json plus validation warnings."""

    graph: Dict[str, List[str]]
    warnings: List[str]


def _normalize_repo_path(path: str) -> str:
    """Normalize a repository-relative path for contract comparisons.

    Strip a single leading ``./`` segment only. Do NOT use ``str.lstrip("./")``
    which strips arbitrary leading ``.`` and ``/`` characters and would mangle
    legitimate paths whose first segment starts with a dot (e.g.
    ``.pdd/meta/foo.json`` would become ``pdd/meta/foo.json`` and miss the
    ``.pdd/meta/*.json`` companion glob — Issue #1013 F5 regression).
    """
    cleaned = str(path or "").replace("\\", "/").strip()
    if cleaned.startswith("./"):
        cleaned = cleaned[2:]
    return cleaned


def _git_changed_paths(project_root: Path) -> Optional[set[str]]:
    """Return changed paths from git status, or ``None`` on scan failure.

    Iter-38 M-1 (fail-closed baseline acquisition): previously returned an
    empty set on any subprocess failure or non-zero return, indistinguishable
    from "scan succeeded but worktree was clean." That ambiguity let a
    transient git failure at runner/orchestrator init time produce an empty
    baseline that the scope guard later treats as "user had nothing dirty,"
    so any pre-existing user file is falsely flagged as out-of-scope and
    reverted/deleted.

    A successful scan that finds no changes returns an empty set; only
    failures (OSError, ``subprocess.SubprocessError``, non-zero return code)
    return ``None``. Init-time callers MUST treat ``None`` as a fail-closed
    abort signal (see :class:`AsyncSyncRunner.__init__` and
    :func:`pdd.agentic_sync.run_agentic_sync`). Enforcement-time callers
    that already have a separate ``<git-status-failed>`` policy (see
    :meth:`_remaining_out_of_scope_paths`) treat ``None`` as the empty set
    via ``or set()``.
    """
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=project_root,
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None

    paths: set[str] = set()
    for line in result.stdout.splitlines():
        if len(line) < 4:
            continue
        payload = line[3:].strip()
        if not payload:
            continue
        if " -> " in payload:
            old_path, new_path = payload.split(" -> ", 1)
            paths.add(_normalize_repo_path(old_path.strip('"')))
            paths.add(_normalize_repo_path(new_path.strip('"')))
        else:
            paths.add(_normalize_repo_path(payload.strip('"')))
    return {p for p in paths if p}


def _git_ignored_paths(project_root: Path) -> Optional[set[str]]:
    """Return repo-relative POSIX paths of git-ignored files (Issue #1013 iter-20).

    Uses ``git ls-files --others --ignored --exclude-standard`` to enumerate
    every individual ignored file (no directory entries, no status prefix).
    May be slow on repos with large ignored trees (``node_modules/``,
    ``build/``, etc.) — callers MUST gate the call on
    ``scope_guard_enabled AND allowed_write_paths is not None`` so non-contract
    runs do not pay the cost.

    Iter-38 M-1 (fail-closed baseline acquisition): returns ``None`` on any
    subprocess failure or non-zero return, NOT an empty set. The init-time
    callers that snapshot the baseline (see :class:`AsyncSyncRunner.__init__`
    and :func:`pdd.agentic_sync.run_agentic_sync`) MUST treat ``None`` as a
    fail-closed abort signal — otherwise a transient git failure at init
    silently produces an empty baseline that the scope guard later treats as
    "no pre-existing files," so any pre-existing user WIP is falsely flagged
    as out-of-scope and reverted/deleted.

    Enforcement-time callers (post-revert re-scan in
    :meth:`_remaining_out_of_scope_paths`) handle ignored-scan failures with
    the separate ``<git-status-failed>`` sentinel; those sites treat ``None``
    as the empty set via ``or set()``.
    """
    try:
        result = subprocess.run(
            ["git", "ls-files", "--others", "--ignored", "--exclude-standard"],
            cwd=project_root,
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None

    paths: set[str] = set()
    for line in result.stdout.splitlines():
        rel = _normalize_repo_path(line.strip().strip('"'))
        if rel:
            paths.add(rel)
    return paths


def _hash_file(project_root: Path, rel_posix: str) -> Optional[str]:
    """Return the SHA-1 of *rel_posix* under *project_root*, or None.

    Issue #1013 iter-24 (M-1) baseline-clobber fix: the scope guard preserves
    pre-existing dirty/untracked paths (iter-6 B1) so the sync run does not
    delete unrelated user WIP. The original implementation matched paths by
    NAME only, which let a buggy LLM SILENTLY OVERWRITE an out-of-scope
    baseline file with different content — the post-revert re-scan saw the
    name in the baseline and skipped the contract check.

    This hash is captured per baseline path at runner init and re-computed
    at scope-guard time; only an unchanged SHA (same bytes on disk) is
    treated as pre-existing user WIP and auto-allowed. A divergent SHA
    falls through to the contract check, surfacing the clobber.

    SHA-1 is sufficient — this is clobber detection, not adversarial
    collision resistance. Returns ``None`` when the file cannot be read
    (missing, permission denied, etc.); callers MUST treat ``None`` as
    "no fingerprint available" and decide policy explicitly.
    """
    try:
        path = (project_root / rel_posix).resolve()
        with open(path, "rb") as handle:
            data = handle.read()
    except (OSError, FileNotFoundError):
        return None
    return hashlib.sha1(data).hexdigest()


def _hash_baseline_paths(
    project_root: Path, paths: Iterable[str]
) -> Dict[str, Optional[str]]:
    """Map each repo-relative path under *project_root* to its SHA-1.

    Iter-30: extracted helper. Previously this was an inline dict
    comprehension in :class:`AsyncSyncRunner.__init__` (mirrored twice for
    the changed-paths and ignored-paths baselines). The orchestrator scope
    guard now reuses it to snapshot baseline before any pre-dispatch LLM
    call or shell command runs in :func:`pdd.agentic_sync.run_agentic_sync`.

    Returns:
        Dict from repo-relative POSIX path to SHA-1 hex string. ``None`` is
        recorded when the file cannot be read at snapshot time — callers
        (the scope guard) must treat ``None`` as "no fingerprint available"
        and decide preservation policy explicitly. See :func:`_hash_file`.
    """
    return {rel: _hash_file(project_root, rel) for rel in paths}


# ---------------------------------------------------------------------------
# Helper functions
# ---------------------------------------------------------------------------


def _find_pdd_executable() -> Optional[str]:
    """Find the pdd executable path."""
    candidate = shutil.which("pdd")
    if candidate:
        return candidate

    py_dir = Path(sys.executable).parent
    for name in ("pdd", "pdd.exe"):
        p = py_dir / name
        if p.exists():
            return str(p)
    return None


def _parse_cost_from_csv(csv_path: str) -> float:
    """Parse total cost from a PDD_OUTPUT_COST_PATH CSV file."""
    total = 0.0
    try:
        if not os.path.exists(csv_path):
            return 0.0
        with open(csv_path, "r", encoding="utf-8", errors="replace") as f:
            reader = _csv.DictReader(f)
            for row in reader:
                cost_val = row.get("cost") or row.get("Cost") or ""
                if not cost_val:
                    continue
                try:
                    total += float(cost_val)
                except (ValueError, TypeError):
                    continue
        return total
    except (OSError, _csv.Error):
        return 0.0


def _format_duration(start: Optional[float], end: Optional[float]) -> str:
    """Format a duration from start/end timestamps."""
    if start is None or end is None:
        return "-"
    seconds = int(end - start)
    if seconds < 60:
        return f"{seconds}s"
    minutes = seconds // 60
    remaining = seconds % 60
    return f"{minutes}m {remaining}s"


_CONFORMANCE_PREFIX = "Architecture conformance error for "
_MISSING_DECLARED_MARKER = "declared symbols missing from generated code"
_MISSING_CAMELCASE_MARKER = "Python code uses camelCase names"
_MISSING_PDD_INTERFACE_PARAMS_MARKER = (
    "declares parameter(s) missing from the generated code"
)
_MISSING_PDD_INTERFACE_FUNCS_MARKER = (
    "declares function(s)/method(s) missing from the generated code"
)
_PDD_INTERFACE_DRIFT_MARKER = (
    "declares parameter(s) whose signature drifted in the generated code"
)


def _parse_conformance_failure(
    stdout: str, stderr: str
) -> Optional[Tuple[str, Tuple[str, ...]]]:
    """
    Detect an architecture-conformance failure in subprocess output.

    Returns (repair_directive, missing_symbols_sorted_tuple) when a conformance
    error is detected, or None otherwise.

    Three inline output shapes are supported, plus a bullet fallback:

    * Default form emitted by ``ArchitectureConformanceError.__init__`` —
      ``... declared symbols missing from generated code: A, B.c, D. Expected: ...``
      The missing symbols are a comma-separated list on the same line, ending
      at the next sentence-terminating period (followed by space/EOL or
      ``Expected:``).
    * camelCase variant — parenthesised:
      ``... Python code uses camelCase names (foo, barBaz) but ...``
    * ``<pdd-interface>`` signature variant emitted by
      ``code_generator_main._verify_pdd_interface_signatures`` —
      ``... declares parameter(s) missing from the generated code:
       foo.bar, baz.qux. Output: ...``
    * Bullet form from a richer multi-line message (kept for forward
      compatibility), where bullets follow any of the marker lines.
    """
    combined = (stdout or "") + "\n" + (stderr or "")
    if _CONFORMANCE_PREFIX not in combined:
        return None

    # Track which shape each symbol came from so we can build a directive
    # that actually matches the failure mode: legacy export-missing vs. the
    # new pdd-interface parameter-missing vs. pdd-interface function/method-
    # missing emitted by ``_verify_pdd_interface_signatures``. Mixing them
    # under a single "Required missing exports" header tells the model to
    # add an export named ``update_main.sync_metadata`` instead of a
    # parameter — which is exactly the misdirection the previous directive
    # caused. Bare dotted method names (``ContentSelector.select``) MUST
    # route to ``iface_missing_funcs`` rather than ``iface_missing_params``
    # so the parser does not split them into ("ContentSelector", "select").
    export_missing: List[str] = []
    iface_missing_params: List[str] = []
    iface_missing_funcs: List[str] = []
    # ``iface_drift`` carries the full parenthesised diagnostic for each
    # drifted parameter so the directive can tell the model what kind of
    # drift (annotation vs. default) and what value to restore.
    iface_drift: List[str] = []

    def _split_symbols(blob: str) -> List[str]:
        out: List[str] = []
        for tok in blob.split(","):
            sym = tok.strip().rstrip(".").strip()
            # Drop trailing punctuation/quoting and any embedded whitespace.
            sym = sym.strip("`'\"")
            if sym and " " not in sym and "\t" not in sym:
                out.append(sym)
        return out

    # 1) Inline declared-missing form:
    #    "... declared symbols missing from generated code: A, B.c. Output: ..."
    # Capture symbols until a known field boundary. Dotted names
    # (Class.method) are safe because boundaries require ". " followed by a
    # field label.
    inline_re = re.compile(
        r"declared symbols missing from generated code:\s*(.+?)"
        r"(?=\.\s+(?:Output|Expected|Found|the\s+prompt)\b|\.\s*$|\.\s*\n|$)",
        re.MULTILINE,
    )
    for m in inline_re.finditer(combined):
        export_missing.extend(_split_symbols(m.group(1)))

    # 2) Inline camelCase form:
    #    "... Python code uses camelCase names (foo, barBaz) but ..."
    camel_re = re.compile(
        r"Python code uses camelCase names\s*\(([^)]*)\)"
    )
    for m in camel_re.finditer(combined):
        export_missing.extend(_split_symbols(m.group(1)))

    # 3) Inline <pdd-interface> parameter-conformance form:
    #    "... <pdd-interface> declares parameter(s) missing from the
    #     generated code: foo.bar, baz.qux. Output: ..."
    # Emitted by code_generator_main._verify_pdd_interface_signatures.
    pdd_iface_params_re = re.compile(
        r"declares parameter\(s\) missing from the generated code:\s*(.+?)"
        r"(?=\.\s+(?:Output|Expected|Found|the\s+prompt)\b|\.\s*$|\.\s*\n|$)",
        re.MULTILINE,
    )
    for m in pdd_iface_params_re.finditer(combined):
        iface_missing_params.extend(_split_symbols(m.group(1)))

    # 4) Inline <pdd-interface> function/method-conformance form:
    #    "... <pdd-interface> declares function(s)/method(s) missing from
    #     the generated code: ContentSelector.select. Output: ..."
    # Emitted alongside (3) when the prompt declares a function/method that
    # is absent from the generated code; routed to the missing-function
    # directive section so we don't tell the model to add ``select`` as a
    # parameter of ``ContentSelector``.
    pdd_iface_funcs_re = re.compile(
        r"declares function\(s\)/method\(s\) missing from the generated "
        r"code:\s*(.+?)"
        r"(?=\.\s+(?:Output|Expected|Found|the\s+prompt)\b|\.\s*$|\.\s*\n|$)",
        re.MULTILINE,
    )
    for m in pdd_iface_funcs_re.finditer(combined):
        iface_missing_funcs.extend(_split_symbols(m.group(1)))

    # 5) Inline <pdd-interface> signature-drift form:
    #    "... <pdd-interface> declares parameter(s) whose signature drifted
    #     in the generated code: foo.bar (annotation: declared `bool`,
    #     found `str`), baz.qux (default: declared `None`, found `0`).
    #     Output: ..."
    # The diagnostic is preserved verbatim per-entry so the directive can
    # emit "update parameter X annotation to `bool`" rather than asking the
    # model to add a missing parameter.
    pdd_iface_drift_re = re.compile(
        r"declares parameter\(s\) whose signature drifted in the generated "
        r"code:\s*(.+?)"
        r"(?=\.\s+(?:Output|Expected|Found|the\s+prompt)\b|\.\s*$|\.\s*\n|$)",
        re.MULTILINE | re.DOTALL,
    )
    for m in pdd_iface_drift_re.finditer(combined):
        # Split on ", " between entries — each entry contains a parenthesised
        # diagnostic so a simple comma split would shred them. Walk the
        # string and track parenthesis depth instead.
        blob = m.group(1).strip()
        entries: List[str] = []
        depth = 0
        current = ""
        i = 0
        while i < len(blob):
            ch = blob[i]
            if ch == "(":
                depth += 1
                current += ch
            elif ch == ")":
                depth = max(0, depth - 1)
                current += ch
            elif ch == "," and depth == 0:
                if current.strip():
                    entries.append(current.strip())
                current = ""
            else:
                current += ch
            i += 1
        if current.strip():
            entries.append(current.strip())
        iface_drift.extend(entries)

    # 6) Bullet form: capture bullet lines following the marker. The marker
    # text we matched dictates which bucket the bullets belong to.
    capture_bucket: Optional[List[str]] = None
    for line in combined.splitlines():
        stripped = line.strip()
        if _MISSING_PDD_INTERFACE_FUNCS_MARKER in stripped:
            capture_bucket = iface_missing_funcs
            continue
        if _MISSING_PDD_INTERFACE_PARAMS_MARKER in stripped:
            capture_bucket = iface_missing_params
            continue
        if (
            _MISSING_DECLARED_MARKER in stripped
            or _MISSING_CAMELCASE_MARKER in stripped
        ):
            capture_bucket = export_missing
            continue
        if capture_bucket is not None:
            m = re.match(r"^[-*]\s+(\S+)", stripped)
            if m:
                capture_bucket.append(m.group(1).rstrip(".,"))
                continue
            if stripped == "":
                continue
            capture_bucket = None

    # The drift bucket carries parenthesised diagnostics; strip them when
    # contributing to ``missing_sorted`` so the short-circuit comparison on
    # the canonical dotted symbol still works across retries.
    drift_symbols = []
    for entry in iface_drift:
        head = entry.split("(", 1)[0].strip()
        if head:
            drift_symbols.append(head)

    missing_sorted = tuple(
        sorted(
            set(export_missing)
            | set(iface_missing_params)
            | set(iface_missing_funcs)
            | set(drift_symbols)
        )
    )
    if not missing_sorted:
        return None

    directive_lines: List[str] = ["Architecture conformance repair required."]

    if export_missing:
        directive_lines.append("Required missing exports:")
        for sym in sorted(set(export_missing)):
            directive_lines.append(f"- {sym}")
        directive_lines.append(
            "Add these exact exports. Do not modify architecture.json. "
            "Do not remove existing valid exports."
        )

    if iface_missing_params or iface_missing_funcs or iface_drift:
        # The pdd-interface check emits dotted method/param names via two
        # distinct error sentences so we can route them correctly here.
        # Missing-function entries (possibly dotted, e.g.
        # ``ContentSelector.select``) MUST stay grouped under "add the
        # following missing function(s)/method(s)" — splitting on the dot
        # would misdirect the model into adding a parameter named
        # ``select`` to ``ContentSelector``.
        if export_missing:
            directive_lines.append("")
        directive_lines.append(
            "The prompt's <pdd-interface> declares function(s)/parameter(s) "
            "missing from the generated code:"
        )
        if iface_missing_funcs:
            directive_lines.append(
                "- Add the following missing function(s)/method(s) declared "
                f"in the prompt: `{', '.join(sorted(set(iface_missing_funcs)))}`."
            )
        # Parameter entries are dotted ``func[.qual].param``: rpartition so
        # ``ContentSelector.select.mode`` groups as ("ContentSelector.select",
        # "mode") rather than misattributing the parameter to the class.
        params_by_func: Dict[str, List[str]] = {}
        for sym in sorted(set(iface_missing_params)):
            if "." in sym:
                func, _, param = sym.rpartition(".")
                params_by_func.setdefault(func, []).append(param)
            else:
                # Defensive: a bare entry under the parameter shape would be
                # malformed, but route it to the missing-function section so
                # we never tell the model to add a nameless parameter.
                directive_lines.append(
                    "- Add the following missing function(s)/method(s) declared "
                    f"in the prompt: `{sym}`."
                )
        for func, params in params_by_func.items():
            directive_lines.append(
                f"- On `{func}`, add the following missing parameter(s) to "
                f"the signature and corresponding code paths: "
                f"`{', '.join(params)}`."
            )
        # Signature drift entries: pass them through with a clarifying
        # prefix. They already contain the symbol and the diagnostic that
        # ``_verify_pdd_interface_signatures`` produced.
        for entry in sorted(set(iface_drift)):
            directive_lines.append(
                f"- Update the generated code so parameter {entry} "
                f"matches the prompt."
            )
        directive_lines.append(
            "Do not remove the declared parameters from the prompt's "
            "<pdd-interface>. The prompt is the source of truth — update "
            "the generated code to match it."
        )

    repair_directive = "\n".join(directive_lines)
    return repair_directive, missing_sorted


def build_conformance_hard_failure_from_error(
    error: Any,
    basename: str,
) -> str:
    """Format a structured architecture-conformance hard-failure block.

    Mirrors :meth:`AsyncSyncRunner._build_conformance_hard_failure` but takes
    a typed :class:`ArchitectureConformanceError` instance directly, so the
    in-process ``pdd sync <module>`` paths in ``sync_main.py`` and
    ``sync_orchestration.py`` can emit the same diagnostic without scraping
    subprocess streams (#866).
    """
    missing = list(getattr(error, "missing_symbols", []) or [])
    expected = list(getattr(error, "expected_symbols", []) or [])
    found = list(getattr(error, "found_symbols", []) or [])
    output = getattr(error, "output_path", "") or "<unknown>"
    prompt = getattr(error, "prompt_name", "") or "<unknown>"

    block_lines = [
        str(error),
        "",
        "=== architecture conformance failure ===",
        f"prompt: {prompt}",
        f"output: {output}",
        f"expected: {', '.join(expected) if expected else '<unknown>'}",
        f"found: {', '.join(found) if found else '<unknown>'}",
        f"missing: {', '.join(missing) if missing else '<none>'}",
        "",
        f"Reproduce locally: pdd sync {basename}",
        "",
        _env_fingerprint(),
    ]
    return "\n".join(block_lines)


def _env_fingerprint() -> str:
    """Best-effort environment fingerprint for diagnostic blocks."""
    lines = ["--- env ---"]

    pdd_file = "<unimportable>"
    try:
        import pdd as _pdd_mod  # type: ignore

        pdd_file = getattr(_pdd_mod, "__file__", "<unknown>") or "<unknown>"
    except Exception:
        pdd_file = "<unimportable>"
    lines.append(f"pdd.__file__: {pdd_file}")

    pdd_version = "<unavailable>"
    try:
        result = subprocess.run(
            ["pdd", "--version"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        if result.returncode == 0:
            first = (result.stdout or "").splitlines()
            pdd_version = first[0].strip() if first else "<unavailable>"
    except Exception:
        pdd_version = "<unavailable>"
    lines.append(f"pdd --version: {pdd_version}")

    git_sha = "<no-git>"
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        if result.returncode == 0:
            git_sha = (result.stdout or "").strip() or "<no-git>"
    except Exception:
        git_sha = "<no-git>"
    lines.append(f"git SHA: {git_sha}")

    git_status = "<unknown>"
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        if result.returncode == 0:
            git_status = "dirty" if (result.stdout or "").strip() else "clean"
    except Exception:
        git_status = "<unknown>"
    lines.append(f"git status: {git_status}")

    source = "unknown"
    try:
        cwd = str(Path.cwd().resolve())
        if pdd_file and pdd_file not in ("<unimportable>", "<unknown>"):
            real = str(Path(pdd_file).resolve())
            if "site-packages" in real:
                source = "site-packages"
            elif real.startswith(cwd + os.sep) or real == cwd:
                source = "repo"
    except Exception:
        source = "unknown"
    lines.append(f"source: {source}")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Architecture parsing helpers
# ---------------------------------------------------------------------------

def _strip_known_language_suffix(name: str) -> str:
    """Strip a final ``_<language>`` suffix using PDD's language catalog."""
    match = re.search(r"_([a-zA-Z0-9]+)$", name)
    if not match:
        return name
    suffix = match.group(1)
    if suffix.lower() in {"llm", "prompt"}:
        return name
    if not _is_known_language(suffix):
        return name
    return name[: match.start()]


def _basename_from_architecture_filename(filename: str) -> Optional[str]:
    """Return a sync basename from an architecture filename, preserving folders."""
    if not filename:
        return None
    name = filename.strip()
    if name.endswith(".prompt"):
        name = name[: -len(".prompt")]
    if not name:
        return None
    # Skip LLM-only entries
    base = Path(name).name
    if base.startswith("_LLM") or base.endswith("_LLM") or base.endswith("_llm"):
        return None
    # Strip language suffix from final component, preserving directories
    parent = Path(name).parent
    base = Path(name).name
    stripped = _strip_known_language_suffix(base)
    if not stripped:
        return None
    if str(parent) in (".", ""):
        return stripped
    return f"{parent.as_posix()}/{stripped}"


def _basename_from_architecture_filepath(filepath: str) -> Optional[str]:
    """Return a sync basename from an architecture filepath."""
    if not filepath:
        return None
    p = Path(filepath)
    if not p.name:
        return None
    stem = p.stem
    if not stem:
        return None
    parent = p.parent
    if str(parent) in (".", ""):
        return stem
    return f"{parent.as_posix()}/{stem}"


def _architecture_entry_aliases(entry: Dict[str, Any]) -> set:
    """Return all sync basenames that may identify an architecture entry."""
    aliases: set = set()
    fn = entry.get("filename")
    if isinstance(fn, str):
        a = _basename_from_architecture_filename(fn)
        if a:
            aliases.add(a)
    fp = entry.get("filepath")
    if isinstance(fp, str):
        a = _basename_from_architecture_filepath(fp)
        if a:
            aliases.add(a)
    return aliases


def _target_basename_aliases(target_basename: str) -> set:
    """Return aliases that should match a requested sync target."""
    aliases = {target_basename}
    p = Path(target_basename)
    base = p.name
    stripped = _strip_known_language_suffix(base)
    if stripped and stripped != base:
        if str(p.parent) in (".", ""):
            aliases.add(stripped)
        else:
            aliases.add(f"{p.parent.as_posix()}/{stripped}")
    return aliases


def build_dep_graph_from_architecture_data(
    architecture: Any,
    target_basenames: List[str],
    *,
    source_name: str = "architecture.json",
) -> DepGraphFromArchitectureResult:
    """Build dependency subgraph from already-loaded architecture data."""
    warnings: List[str] = []
    graph: Dict[str, List[str]] = {b: [] for b in target_basenames}

    # Extract entries: list, or dict with files/modules/entries
    entries: List[Dict[str, Any]] = []
    if isinstance(architecture, list):
        entries = [e for e in architecture if isinstance(e, dict)]
    elif isinstance(architecture, dict):
        for key in ("files", "modules", "entries"):
            value = architecture.get(key)
            if isinstance(value, list):
                entries = [e for e in value if isinstance(e, dict)]
                break

    if not entries:
        return DepGraphFromArchitectureResult(graph=graph, warnings=warnings)

    # Map every alias of every entry -> the entry itself
    alias_to_entry: Dict[str, Dict[str, Any]] = {}
    # Map filename -> aliases set (used for orphan detection)
    filename_to_aliases: Dict[str, set] = {}
    for entry in entries:
        aliases = _architecture_entry_aliases(entry)
        fn = entry.get("filename")
        if isinstance(fn, str) and fn:
            filename_to_aliases[fn] = aliases
        for a in aliases:
            alias_to_entry.setdefault(a, entry)

    # Map every alias of every target -> target_basename
    target_alias_map: Dict[str, str] = {}
    for tb in target_basenames:
        for alias in _target_basename_aliases(tb):
            target_alias_map.setdefault(alias, tb)

    for tb in target_basenames:
        # Locate architecture entry for this target
        entry: Optional[Dict[str, Any]] = None
        for alias in _target_basename_aliases(tb):
            if alias in alias_to_entry:
                entry = alias_to_entry[alias]
                break
        if entry is None:
            continue

        deps_field = entry.get("dependencies") or []
        if not isinstance(deps_field, list):
            continue

        resolved: List[str] = []
        for dep in deps_field:
            if not isinstance(dep, str):
                continue
            # Try both filename and filepath interpretations
            dep_basename = _basename_from_architecture_filename(dep)
            if dep_basename is None:
                dep_basename = _basename_from_architecture_filepath(dep)

            # Try to resolve dep to an architecture entry to learn its aliases
            dep_entry = filename_to_aliases.get(dep)
            if dep_entry is None and dep_basename is not None:
                # Try by alias lookup
                dep_aliases_set: set = set()
                if dep_basename in alias_to_entry:
                    dep_aliases_set = _architecture_entry_aliases(
                        alias_to_entry[dep_basename]
                    )
                else:
                    dep_aliases_set = {dep_basename} if dep_basename else set()
                dep_aliases = dep_aliases_set
                resolved_via_entry = bool(dep_aliases_set & set(alias_to_entry.keys()))
            else:
                dep_aliases = dep_entry if dep_entry is not None else set()
                resolved_via_entry = dep_entry is not None

            # Find matching target via aliases
            matched: Optional[str] = None
            for da in dep_aliases:
                if da in target_alias_map:
                    matched = target_alias_map[da]
                    break

            if matched is None:
                if not resolved_via_entry:
                    # Orphan: the dep filename has no matching architecture entry
                    warnings.append(
                        f"{source_name}: module '{tb}' lists orphan dependency "
                        f"'{dep}' (no matching architecture entry)"
                    )
                else:
                    # Outside the target sync set
                    display = sorted(dep_aliases)[0] if dep_aliases else dep
                    warnings.append(
                        f"{source_name}: module '{tb}' depends on '{display}' "
                        f"(via '{dep}'), which is not in the sync target set; "
                        "edge omitted from schedule"
                    )
                continue

            if matched == tb:
                continue  # skip self-deps
            if matched not in resolved:
                resolved.append(matched)

        graph[tb] = resolved

    return DepGraphFromArchitectureResult(graph=graph, warnings=warnings)


def build_dep_graph_from_architecture(
    arch_path: Path, target_basenames: List[str]
) -> DepGraphFromArchitectureResult:
    """Build dependency subgraph for target basenames from architecture.json."""
    if not arch_path.exists():
        return DepGraphFromArchitectureResult(
            graph={b: [] for b in target_basenames}, warnings=[]
        )
    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            arch = json.load(f)
    except (OSError, json.JSONDecodeError):
        return DepGraphFromArchitectureResult(
            graph={b: [] for b in target_basenames}, warnings=[]
        )
    return build_dep_graph_from_architecture_data(
        arch, target_basenames, source_name=str(arch_path)
    )


# ---------------------------------------------------------------------------
# AsyncSyncRunner
# ---------------------------------------------------------------------------


class AsyncSyncRunner:
    """
    Parallel sync engine that runs `pdd sync` for multiple modules concurrently,
    respecting dependency order and posting live progress to GitHub.
    """

    def __init__(
        self,
        basenames: List[str],
        dep_graph: Dict[str, List[str]],
        sync_options: Dict[str, Any],
        github_info: Optional[Dict[str, Any]],
        quiet: bool = False,
        *,
        verbose: bool = False,
        issue_url: Optional[str] = None,
        module_cwds: Optional[Dict[str, Any]] = None,
        module_targets: Optional[Dict[str, str]] = None,
        initial_cost: float = 0.0,
        allowed_write_set: Optional[Iterable[str]] = None,
        companion_allowlist: Optional[Iterable[str]] = None,
        scope_guard_enabled: bool = True,
        contract_source: Optional[str] = None,
        project_root: Optional[Path] = None,
    ):
        self.basenames: List[str] = list(basenames)
        self.dep_graph: Dict[str, List[str]] = {
            b: list(dep_graph.get(b, [])) for b in self.basenames
        }
        self.sync_options: Dict[str, Any] = dict(sync_options or {})
        self.github_info = github_info
        self.quiet = quiet
        self.verbose = verbose
        self.issue_url = issue_url
        # Issue #1013 iter-18 M-1 (durable baseline-paths bug): allow callers
        # (notably ``DurableSyncRunner``) to pin ``project_root`` to a known
        # repo root BEFORE the baseline-changed-paths snapshot is taken
        # below. Without this kwarg the snapshot would always read
        # ``git status`` from the caller's current working directory, so a
        # dirty file in the user's main checkout would be auto-allowed in
        # the durable worktree's scope guard.
        self.project_root: Path = (
            Path(project_root).resolve() if project_root is not None else Path.cwd()
        )
        self.module_cwds: Dict[str, Any] = dict(module_cwds or {})
        self.module_targets: Dict[str, str] = dict(module_targets or {})
        self.initial_cost = float(initial_cost or 0.0)

        # Issue #1013 — split-contract scope guard (F5, F9, F14, F4, F6):
        # Track contract presence separately from set truthiness. ``None``
        # means "no contract → permissive fallback"; an explicit empty
        # iterable means "contract present but empty → reject everything"
        # (degenerate but legal). The single accepted kwarg name is
        # ``allowed_write_set``; the legacy ``allowed_write_paths`` alias is
        # gone per F14.
        #
        # F6: the parsed contract is recorded for diagnostics *regardless* of
        # whether scope-guard enforcement is enabled. ``_enforce_scope_guard``
        # short-circuits on ``scope_guard_enabled=False``, so storing the
        # contract in opt-out mode is safe and matches the spec requirement
        # that disabled runners still see the parsed contract.
        self.scope_guard_enabled: bool = bool(scope_guard_enabled)
        self.contract_source: Optional[str] = contract_source
        if allowed_write_set is not None:
            self.allowed_write_paths: Optional[Set[str]] = {
                _normalize_repo_path(path)
                for path in allowed_write_set
                if isinstance(path, str) and path.strip()
            }
        else:
            self.allowed_write_paths = None
        # F4: the effective companion allowlist is *always* the caller-provided
        # patterns unioned with DEFAULT_SYNC_COMPANION_ALLOWLIST. Order is
        # preserved (caller patterns first, defaults appended) and duplicates
        # are removed deterministically. Passing an empty iterable still
        # produces at least the default; passing ``None`` is identical to
        # passing an empty iterable.
        provided: Tuple[str, ...] = tuple(
            p for p in (companion_allowlist or ())
            if isinstance(p, str) and p
        )
        self.companion_allowlist: Tuple[str, ...] = tuple(
            dict.fromkeys(provided + tuple(DEFAULT_SYNC_COMPANION_ALLOWLIST))
        )

        # Per-`git toplevel` locks for scope-guard git operations (F12).
        # Modules may share a repo root (shared-worktree non-durable sync) so
        # the lock key MUST resolve to the actual git toplevel, not the raw
        # module_cwd path — otherwise two modules in the same repo get
        # separate locks and the race we're trying to prevent reappears.
        self._scope_guard_locks: Dict[str, threading.Lock] = defaultdict(threading.Lock)
        self._scope_guard_locks_lock = threading.Lock()

        # Iter-6 B1 (data-loss bug): snapshot the working-tree changed/untracked
        # set BEFORE any module sync runs. Pre-existing untracked files
        # (e.g. user's ``scratch.txt``) are not the sync run's responsibility
        # and MUST be preserved by the scope guard.
        #
        # Iter-24 M-1 (baseline-clobber bug): the snapshot is now a DICT
        # mapping repo-relative POSIX path → init-time SHA-1 instead of a
        # bare set. ``_enforce_scope_guard`` re-hashes each baseline path at
        # check time; ONLY paths whose content is byte-identical to the init
        # snapshot are auto-allowed. Name-based preservation let a buggy LLM
        # silently OVERWRITE pre-existing dirty files outside the contract
        # (the iter-23 codex repro). Empty dict — never bare set — when the
        # gate (``scope_guard_enabled AND allowed_write_paths is not None``)
        # is off, so the dict.items() loops in the enforcement path are
        # safe no-ops.
        #
        # Iter-20 M-1 (gitignored fail-open): also snapshot pre-existing
        # gitignored files (e.g. user-side ``build/cache.bin`` under a
        # repo-wide ``.gitignore: build/``). ``git status`` does not show
        # ignored files by default, so without this baseline a sync that
        # writes to a gitignored path outside the allowed write set would be
        # invisible to the post-revert re-scan and the module would be
        # marked successful with the contract violated on disk.
        #
        # Iter-24 M-1: same dict-with-SHA shape as ``_baseline_changed_paths``.
        #
        # Iter-38 M-1 (fail-closed baseline acquisition): the helpers now
        # return ``None`` on scan failure (transient git lock contention,
        # missing binary, OSError) instead of an empty set. Without this
        # discrimination an init-time scan failure would silently produce
        # an empty baseline that the scope guard later treats as "no
        # pre-existing files," so any pre-existing user WIP is falsely
        # flagged as out-of-scope and reverted/deleted. When EITHER scan
        # returns ``None`` we record ``_baseline_acquisition_failed = True``
        # and :meth:`run` aborts before any write-capable work. The flag
        # is internal — public signatures are unchanged.
        if self.scope_guard_enabled and self.allowed_write_paths is not None:
            _raw_changed = _git_changed_paths(self.project_root)
            _raw_ignored = _git_ignored_paths(self.project_root)
            if _raw_changed is None or _raw_ignored is None:
                self._baseline_acquisition_failed: bool = True
                self._baseline_changed_paths: Dict[str, Optional[str]] = {}
                self._baseline_ignored_paths: Dict[str, Optional[str]] = {}
            else:
                self._baseline_acquisition_failed = False
                self._baseline_changed_paths = _hash_baseline_paths(
                    self.project_root, _raw_changed
                )
                self._baseline_ignored_paths = _hash_baseline_paths(
                    self.project_root, _raw_ignored
                )
        else:
            self._baseline_acquisition_failed = False
            self._baseline_changed_paths = {}
            self._baseline_ignored_paths = {}

        self.total_budget = self.sync_options.get("total_budget")
        self.max_workers = 1 if self.total_budget is not None else MAX_WORKERS
        # When a contract narrows writes AND scope-guard enforcement is
        # active, serialise across modules so the per-cwd lock isn't fighting
        # parallel git status / git checkout calls. With ``--no-scope-guard``
        # the contract is recorded for diagnostics only — no enforcement runs
        # — so parallelism is preserved (F6).
        if self.scope_guard_enabled and self.allowed_write_paths is not None:
            self.max_workers = 1

        self.module_states: Dict[str, ModuleState] = {
            b: ModuleState() for b in self.basenames
        }
        self.failed: bool = False
        self.budget_exhausted: bool = False
        self.comment_id: Optional[int] = None
        self.lock = threading.Lock()

        # Track child process groups for cleanup on interrupt
        self._child_pgids: set = set()

        # Rate-limit GitHub comment updates
        self._last_comment_update: float = 0.0
        self._comment_update_interval: float = 15.0

        # Modules whose state was restored to "success" from disk
        self._resumed_modules: List[str] = []
        self._load_state()

    # ------------------------------------------------------------------
    # State persistence
    # ------------------------------------------------------------------
    def _state_file_path(self) -> Path:
        """Return the path to the state file."""
        return self.project_root / STATE_FILE_PATH

    def _load_state(self) -> None:
        """Load previously saved state if it matches the current run."""
        if not self.issue_url:
            return

        state_path = self._state_file_path()
        if not state_path.exists():
            return

        try:
            with open(state_path, "r", encoding="utf-8") as f:
                saved = json.load(f)
        except (OSError, json.JSONDecodeError):
            return

        if saved.get("issue_url") != self.issue_url:
            return

        saved_modules = saved.get("modules", {})
        for basename, info in saved_modules.items():
            if basename in self.module_states and info.get("status") == "success":
                state = self.module_states[basename]
                state.status = "success"
                state.cost = float(info.get("cost", 0.0) or 0.0)
                phases = info.get("completed_phases") or []
                if isinstance(phases, list):
                    state.completed_phases = list(phases)
                state.start_time = info.get("start_time")
                state.end_time = info.get("end_time")
                if basename not in self._resumed_modules:
                    self._resumed_modules.append(basename)

        cid = saved.get("comment_id")
        if cid is not None:
            try:
                self.comment_id = int(cid)
            except (TypeError, ValueError):
                pass

    def _save_state(self) -> None:
        """Atomically persist current state to disk."""
        if not self.issue_url:
            return

        state_path = self._state_file_path()
        try:
            state_path.parent.mkdir(parents=True, exist_ok=True)
        except OSError:
            return

        modules_data: Dict[str, Dict[str, Any]] = {}
        with self.lock:
            for basename in self.basenames:
                state = self.module_states[basename]
                modules_data[basename] = {
                    "status": state.status,
                    "cost": state.cost,
                    "completed_phases": list(state.completed_phases),
                    "current_phase": state.current_phase,
                    "start_time": state.start_time,
                    "end_time": state.end_time,
                    "error": state.error,
                }

        data = {
            "issue_url": self.issue_url,
            "modules": modules_data,
            "total_cost": self.initial_cost
            + sum(m["cost"] for m in modules_data.values()),
            "comment_id": self.comment_id,
            "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        }

        tmp_path: Optional[str] = None
        try:
            fd, tmp_path = tempfile.mkstemp(
                dir=str(state_path.parent), suffix=".tmp"
            )
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            os.replace(tmp_path, str(state_path))
            tmp_path = None
        except OSError:
            pass
        finally:
            if tmp_path is not None:
                try:
                    os.unlink(tmp_path)
                except OSError:
                    pass

    def _delete_state(self) -> None:
        """Remove the state file (called on full success). Noop if missing."""
        try:
            self._state_file_path().unlink(missing_ok=True)
        except OSError:
            pass

    # ------------------------------------------------------------------
    # Signal handling
    # ------------------------------------------------------------------
    def _kill_children(self) -> None:
        """Kill all tracked child process groups."""
        for pgid in list(self._child_pgids):
            try:
                os.killpg(pgid, signal.SIGTERM)
            except OSError:
                pass
        time.sleep(1)
        for pgid in list(self._child_pgids):
            try:
                os.killpg(pgid, signal.SIGKILL)
            except OSError:
                pass
        self._child_pgids.clear()

    # ------------------------------------------------------------------
    # Scheduling helpers
    # ------------------------------------------------------------------
    def _all_terminal(self) -> bool:
        """All modules are in a terminal state (success/failed)."""
        with self.lock:
            return all(
                s.status in ("success", "failed")
                for s in self.module_states.values()
            )

    def _get_ready_modules(self) -> List[str]:
        """Pending modules whose deps are all satisfied."""
        ready: List[str] = []
        with self.lock:
            for basename in self.basenames:
                state = self.module_states[basename]
                if state.status != "pending":
                    continue
                deps = self.dep_graph.get(basename, [])
                deps_ok = True
                for d in deps:
                    dep_state = self.module_states.get(d)
                    if dep_state is None:
                        # Out-of-target deps assumed already synced
                        continue
                    if dep_state.status != "success":
                        deps_ok = False
                        break
                if deps_ok:
                    ready.append(basename)
        return ready

    def _get_blocked_modules(self) -> List[str]:
        """Pending modules transitively blocked by a failed dep."""
        blocked: List[str] = []
        with self.lock:
            cache: Dict[str, bool] = {}

            def is_blocked(module: str, visiting: set) -> bool:
                cached = cache.get(module)
                if cached is not None:
                    return cached
                if module in visiting:
                    cache[module] = False
                    return False
                visiting.add(module)
                try:
                    for dep in self.dep_graph.get(module, []):
                        dep_state = self.module_states.get(dep)
                        if dep_state is None:
                            continue
                        if dep_state.status == "failed":
                            cache[module] = True
                            return True
                        if dep_state.status == "pending" and is_blocked(
                            dep, visiting
                        ):
                            cache[module] = True
                            return True
                finally:
                    visiting.discard(module)
                cache[module] = False
                return False

            for basename in self.basenames:
                state = self.module_states[basename]
                if state.status != "pending":
                    continue
                if is_blocked(basename, set()):
                    blocked.append(basename)
        return blocked

    # ------------------------------------------------------------------
    # Budget
    # ------------------------------------------------------------------
    def _per_module_cost_so_far(self) -> float:
        """Sum of per-module costs spent so far (excludes initial_cost)."""
        with self.lock:
            return sum(s.cost for s in self.module_states.values())

    def _remaining_total_budget(self, in_flight_cost: float = 0.0) -> Optional[float]:
        """Remaining total budget (None if no total budget set)."""
        if self.total_budget is None:
            return None
        spent = float(self.initial_cost) + self._per_module_cost_so_far()
        spent += max(float(in_flight_cost or 0.0), 0.0)
        return max(float(self.total_budget) - spent, 0.0)

    def _budget_exhausted(self) -> bool:
        """True when the configured total budget is fully spent."""
        remaining = self._remaining_total_budget()
        return remaining is not None and remaining <= 0.0

    # ------------------------------------------------------------------
    # Phase handling
    # ------------------------------------------------------------------
    def _on_phase_change(self, basename: str, phase: str) -> None:
        """Handle a phase transition for a module."""
        with self.lock:
            state = self.module_states.get(basename)
            if state is None:
                return
            prev = state.current_phase
            if prev and prev != phase:
                if not prev.startswith("skip:") and prev not in state.completed_phases:
                    state.completed_phases.append(prev)
            state.current_phase = phase
        self._update_github_comment_throttled()

    # ------------------------------------------------------------------
    # GitHub comment
    # ------------------------------------------------------------------
    def _update_github_comment_throttled(self) -> None:
        """Update comment at most once per interval. First call always fires."""
        now = time.time()
        interval = self._comment_update_interval
        if self._last_comment_update == 0.0 or interval <= 0 or (
            now - self._last_comment_update
        ) >= interval:
            self._last_comment_update = now
            self._update_github_comment()

    def _update_github_comment(self, status_label: Optional[str] = None) -> None:
        """Create or update a GitHub issue comment with current progress."""
        if not self.github_info:
            return

        owner = self.github_info.get("owner")
        repo = self.github_info.get("repo")
        issue_number = self.github_info.get("issue_number")
        if not (owner and repo and issue_number is not None):
            return

        body = _cap_github_comment_body(self._build_comment_body(int(issue_number)))
        gh_timeout = 30

        try:
            if self.comment_id is None:
                self.comment_id = self._find_existing_progress_comment_id(
                    owner, repo, int(issue_number), timeout=gh_timeout
                )

            if self.comment_id is None:
                ok, response = _run_gh_command(
                    [
                        "api",
                        f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                        "-X",
                        "POST",
                        "-f",
                        f"body={body}",
                    ],
                    timeout=gh_timeout,
                )
                if ok:
                    try:
                        data = json.loads(response)
                        if isinstance(data, dict) and "id" in data:
                            self.comment_id = int(data["id"])
                    except (json.JSONDecodeError, TypeError, ValueError):
                        pass
            else:
                ok, _ = _run_gh_command(
                    [
                        "api",
                        f"repos/{owner}/{repo}/issues/comments/{self.comment_id}",
                        "-X",
                        "PATCH",
                        "-f",
                        f"body={body}",
                    ],
                    timeout=gh_timeout,
                )
                if not ok:
                    self.comment_id = None
        except Exception:
            pass

    def _find_existing_progress_comment_id(
        self,
        owner: str,
        repo: str,
        issue_number: int,
        *,
        timeout: int,
    ) -> Optional[int]:
        """Return the newest existing PDD sync progress comment id for this issue."""
        ok, response = _run_gh_command(
            [
                "api",
                f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                "--paginate",
                "--slurp",
            ],
            timeout=timeout,
        )
        if not ok:
            return None

        try:
            payload = json.loads(response)
        except json.JSONDecodeError:
            return None

        comments: List[Dict[str, Any]] = []
        if isinstance(payload, list):
            for item in payload:
                if isinstance(item, list):
                    for c in item:
                        if isinstance(c, dict):
                            comments.append(c)
                elif isinstance(item, dict):
                    comments.append(item)

        marker = f"## PDD Agentic Sync Progress\nIssue: #{issue_number}"
        for comment in reversed(comments):
            body = comment.get("body")
            cid = comment.get("id")
            if isinstance(body, str) and body.startswith(marker) and cid is not None:
                try:
                    return int(cid)
                except (TypeError, ValueError):
                    continue
        return None

    def _build_comment_body(self, issue_number: int) -> str:
        """Build the markdown comment body showing sync progress."""
        lines = [
            "## PDD Agentic Sync Progress",
            f"Issue: #{issue_number}",
            "",
            "| Module | Status | Phase | Duration | Cost |",
            "|--------|--------|-------|----------|------|",
        ]

        total_cost = self.initial_cost

        with self.lock:
            states_snapshot = {
                b: ModuleState(
                    status=s.status,
                    start_time=s.start_time,
                    end_time=s.end_time,
                    cost=s.cost,
                    error=s.error,
                    current_phase=s.current_phase,
                    completed_phases=list(s.completed_phases),
                )
                for b, s in self.module_states.items()
            }

        for basename in self.basenames:
            state = states_snapshot[basename]
            total_cost += state.cost

            if state.status == "success":
                status_str = "Success"
                duration = _format_duration(state.start_time, state.end_time)
                cost_str = f"${state.cost:.2f}"
                n = len(state.completed_phases)
                phase_str = f"{n} phases" if n else "-"
            elif state.status == "failed":
                status_str = "Failed"
                duration = _format_duration(state.start_time, state.end_time)
                cost_str = f"${state.cost:.2f}"
                n = len(state.completed_phases)
                phase_str = f"{n} phases" if n else "-"
            elif state.status == "running":
                status_str = "Running"
                duration = _format_duration(state.start_time, time.time())
                cost_str = "-"
                if state.current_phase:
                    phase_name = state.current_phase
                    if phase_name.startswith("skip:"):
                        phase_name = "~" + phase_name[len("skip:"):]
                    n = len(state.completed_phases)
                    phase_str = f"`{phase_name}` ({n} done)"
                else:
                    phase_str = "-"
            else:
                status_str = "Pending"
                duration = "-"
                cost_str = "-"
                phase_str = "-"

            lines.append(
                f"| {basename} | {status_str} | {phase_str} | {duration} | {cost_str} |"
            )

        lines.append("")
        lines.append(f"**Total cost:** ${total_cost:.2f}")

        # Status footer
        failed_modules = [
            b for b in self.basenames if states_snapshot[b].status == "failed"
        ]
        running_modules = [
            b for b in self.basenames if states_snapshot[b].status == "running"
        ]
        # Pending modules that are not transitively blocked are still "runnable"
        blocked_set = set(self._get_blocked_modules())
        runnable_pending = [
            b
            for b in self.basenames
            if states_snapshot[b].status == "pending" and b not in blocked_set
        ]
        all_terminal = all(
            states_snapshot[b].status in ("success", "failed")
            for b in self.basenames
        )

        if failed_modules and (running_modules or runnable_pending):
            failed_str = ", ".join(f"`{b}`" for b in failed_modules)
            lines.append(
                f"Continuing independent module(s) after {failed_str} failed"
            )
        elif failed_modules:
            failed_str = ", ".join(f"`{b}`" for b in failed_modules)
            lines.append(f"Paused: {failed_str} failed")
        elif all_terminal and not failed_modules:
            lines.append(
                f"All {len(self.basenames)} modules synced successfully"
            )
        else:
            successes = sum(
                1
                for b in self.basenames
                if states_snapshot[b].status == "success"
            )
            lines.append(
                f"In Progress ({successes}/{len(self.basenames)} complete)"
            )

        # Failed-module details (#865): render each failed module's structured
        # error (architecture-conformance block, "Reproduce locally:" line, and
        # env fingerprint) so the GitHub progress comment carries the same
        # diagnostics the local CLI prints. Each module is collapsed into a
        # <details> block and its error is fenced as a code block. The body is
        # truncated to keep the comment well under the 65 536-character GitHub
        # limit even when several modules fail with long stack traces.
        if failed_modules:
            lines.append("")
            lines.append("### Failed module details")
            omitted_details = 0
            truncated_details = 0
            for idx, basename in enumerate(failed_modules):
                remaining_modules = len(failed_modules) - idx
                current_body_len = len("\n".join(lines))
                reserved_footer = (
                    "\n\n_Additional failed module details omitted to keep "
                    "this GitHub comment under the size limit._"
                )
                remaining_budget = (
                    GITHUB_COMMENT_BODY_LIMIT
                    - current_body_len
                    - len(reserved_footer)
                )
                detail_overhead = 96 + len(basename)
                if remaining_budget <= detail_overhead + GITHUB_FAILED_DETAIL_MIN_CHARS:
                    omitted_details = remaining_modules
                    break

                err = states_snapshot[basename].error or ""
                err = err.rstrip()
                if not err:
                    err = "(no error captured)"
                per_module_limit = min(
                    GITHUB_FAILED_DETAIL_PER_MODULE_LIMIT,
                    max(
                        GITHUB_FAILED_DETAIL_MIN_CHARS,
                        (remaining_budget // max(remaining_modules, 1)) - detail_overhead,
                    ),
                )
                if len(err) > per_module_limit:
                    truncated_details += 1
                    err = (
                        err[:per_module_limit]
                        + f"\n... [truncated {len(err) - per_module_limit} chars]"
                    )
                # Escape any backtick fence inside the error so the markdown
                # code block stays well-formed.
                fence = "```"
                while fence in err:
                    fence += "`"
                lines.append("")
                lines.append(f"<details><summary><code>{basename}</code></summary>")
                lines.append("")
                lines.append(fence)
                lines.append(err)
                lines.append(fence)
                lines.append("")
                lines.append("</details>")
            if truncated_details or omitted_details:
                lines.append("")
                summary_parts = []
                if truncated_details:
                    summary_parts.append(
                        f"{truncated_details} failed detail block(s) truncated"
                    )
                if omitted_details:
                    summary_parts.append(
                        f"{omitted_details} failed detail block(s) omitted"
                    )
                lines.append(
                    "_"
                    + "; ".join(summary_parts)
                    + " to keep this GitHub comment under the size limit. "
                    + "See workflow logs for full output._"
                )

        return _cap_github_comment_body("\n".join(lines))

    # ------------------------------------------------------------------
    # Recording results
    # ------------------------------------------------------------------
    def _record_result(
        self, basename: str, success: bool, cost: float, error: str
    ) -> None:
        """Record the result of a module sync and persist state."""
        with self.lock:
            state = self.module_states[basename]
            if state.current_phase and not state.current_phase.startswith("skip:"):
                if state.current_phase not in state.completed_phases:
                    state.completed_phases.append(state.current_phase)
            state.current_phase = None
            state.status = "success" if success else "failed"
            state.end_time = time.time()
            state.cost = cost
            if not success:
                state.error = error
                self.failed = True
        self._save_state()

    # ------------------------------------------------------------------
    # Run loop
    # ------------------------------------------------------------------
    def run(self) -> Tuple[bool, str, float]:
        """Run all syncs respecting dependencies."""
        # Issue #1013 iter-18 m-1: scope-guard run-entry logging is owned by
        # the sync layer (`pdd/agentic_sync.py` ``run_agentic_sync``), which
        # emits a single user-facing line per invocation covering all three
        # states (disabled / contract loaded / no contract). The runner used
        # to log the permissive-fallback and opt-out states a second time
        # here, which produced a duplicate line for every sync. Removed so
        # the operator sees one authoritative status line.

        # Iter-38 M-1 (fail-closed baseline acquisition): the __init__
        # baseline-scan helpers (``_git_changed_paths`` / ``_git_ignored_paths``)
        # now return ``None`` on transient git failure (lock contention,
        # missing binary, OSError) rather than an empty set. An empty
        # baseline indistinguishable from "scan succeeded, worktree clean"
        # would later cause the scope guard to flag pre-existing user WIP
        # as out-of-scope and revert/delete it. When the init recorded a
        # failed acquisition, abort BEFORE any write-capable work runs.
        if getattr(self, "_baseline_acquisition_failed", False):
            return (
                False,
                (
                    "Scope guard fail-closed: could not snapshot working-tree "
                    "baseline at runner init (git scan failed). Aborting "
                    "before any write-capable work to prevent false-positive "
                    "reverts of pre-existing user files."
                ),
                self.initial_cost,
            )

        if not self.basenames:
            return True, "No modules to sync", self.initial_cost

        if self._resumed_modules and not self.quiet:
            resumed = sorted(self._resumed_modules)
            console.print(
                f"[green]Resuming: skipping {len(resumed)} already-succeeded "
                f"module(s): {resumed}[/green]"
            )

        self._update_github_comment()

        prev_sigint = signal.getsignal(signal.SIGINT)
        prev_sigterm = signal.getsignal(signal.SIGTERM)

        def _on_interrupt(signum, frame):
            self._kill_children()
            try:
                signal.signal(
                    signum,
                    prev_sigint if signum == signal.SIGINT else prev_sigterm,
                )
                os.kill(os.getpid(), signum)
            except Exception:
                pass

        try:
            signal.signal(signal.SIGINT, _on_interrupt)
            signal.signal(signal.SIGTERM, _on_interrupt)
        except (ValueError, OSError):
            pass

        try:
            return self._run_inner()
        finally:
            try:
                signal.signal(signal.SIGINT, prev_sigint)
                signal.signal(signal.SIGTERM, prev_sigterm)
            except (ValueError, OSError, TypeError):
                pass
            self._kill_children()

    def _run_inner(self) -> Tuple[bool, str, float]:
        """Inner run loop, separated so signal handlers wrap it."""
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures: Dict[Any, str] = {}

            while True:
                if self._all_terminal() and not futures:
                    break

                if not self.budget_exhausted and self._budget_exhausted():
                    self.budget_exhausted = True

                if self.budget_exhausted:
                    if not futures:
                        break
                else:
                    ready = self._get_ready_modules()
                    available = self.max_workers - len(futures)
                    for basename in ready[:available]:
                        with self.lock:
                            state = self.module_states[basename]
                            state.status = "running"
                            state.start_time = time.time()
                        self._update_github_comment()
                        future = executor.submit(self._sync_one_module, basename)
                        futures[future] = basename

                if not futures:
                    # Nothing to schedule, nothing running -> done
                    break

                done, _ = wait(futures, return_when=FIRST_COMPLETED)
                for future in done:
                    basename = futures.pop(future)
                    try:
                        success, cost, error = future.result()
                    except Exception as exc:
                        success, cost, error = False, 0.0, str(exc)
                    self._record_result(basename, success, cost, error)
                    self._update_github_comment()
                    if self._budget_exhausted():
                        self.budget_exhausted = True

        # Final update
        self._update_github_comment()

        with self.lock:
            total_cost = self.initial_cost + sum(
                s.cost for s in self.module_states.values()
            )
            succeeded = [
                b for b in self.basenames
                if self.module_states[b].status == "success"
            ]
            failed = [
                b for b in self.basenames
                if self.module_states[b].status == "failed"
            ]
            pending = [
                b for b in self.basenames
                if self.module_states[b].status == "pending"
            ]

        blocked = self._get_blocked_modules()
        blocked_set = set(blocked)
        not_run = [b for b in pending if b not in blocked_set]

        if self.budget_exhausted:
            try:
                budget = float(self.total_budget) if self.total_budget is not None else total_cost
            except (TypeError, ValueError):
                budget = total_cost
            msg = (
                f"Budget exhausted (${total_cost:.2f} of ${budget:.2f}). "
                f"Succeeded: {succeeded}."
            )
            if failed:
                msg += f" Failed: {failed}."
            if pending:
                msg += f" Skipped (budget): {pending}."
            self._save_state()
            return False, msg, total_cost

        if failed:
            msg = f"Failed: {failed}. Succeeded: {succeeded}."
            if blocked:
                msg += f" Skipped (blocked): {blocked}."
            if not_run:
                msg += f" Skipped (not run): {not_run}."
            for b in failed:
                err = self.module_states[b].error
                if err:
                    err_summary = err.strip()[:500]
                    msg += f"\n  {b}: {err_summary}"
            self._save_state()
            return False, msg, total_cost

        if pending:
            msg = f"Succeeded: {succeeded}."
            if blocked:
                msg += f" Skipped (blocked): {blocked}."
            if not_run:
                msg += f" Skipped (not run): {not_run}."
            self._save_state()
            return False, msg, total_cost

        self._delete_state()
        return (
            True,
            f"All {len(succeeded)} modules synced successfully",
            total_cost,
        )

    # ------------------------------------------------------------------
    # Subprocess execution
    # ------------------------------------------------------------------
    def _build_command(self, basename: str, in_flight_cost: float = 0.0) -> List[str]:
        """Build the pdd sync subprocess command for a basename."""
        pdd_exe = _find_pdd_executable()
        if pdd_exe:
            cmd = [pdd_exe, "--force"]
        else:
            cmd = [sys.executable, "-m", "pdd", "--force"]

        if self.sync_options.get("local"):
            cmd.append("--local")
        cmd.append("sync")

        # Module-specific flags
        if self.sync_options.get("agentic"):
            cmd.append("--agentic")
        if self.sync_options.get("no_steer"):
            cmd.append("--no-steer")

        target_coverage = self.sync_options.get("target_coverage")
        if target_coverage is not None:
            cmd.extend(["--target-coverage", str(target_coverage)])

        if self.sync_options.get("one_session"):
            cmd.append("--one-session")
        if self.sync_options.get("skip_verify"):
            cmd.append("--skip-verify")
        if self.sync_options.get("skip_tests"):
            cmd.append("--skip-tests")

        max_attempts = self.sync_options.get("max_attempts")
        if max_attempts:
            cmd.extend(["--max-attempts", str(max_attempts)])

        # Budget handling: total_budget takes precedence
        if self.total_budget is not None:
            remaining = self._remaining_total_budget(in_flight_cost)
            if remaining is not None:
                cmd.extend(["--budget", str(remaining)])
        elif self.sync_options.get("budget") is not None:
            cmd.extend(["--budget", str(self.sync_options["budget"])])

        cmd.append(self.module_targets.get(basename, basename))
        return cmd

    def _build_env(
        self, cost_file_path: str, repair_directive: Optional[str] = None
    ) -> Dict[str, str]:
        """Build the env dict for subprocess Popen."""
        env = os.environ.copy()
        env["PDD_OUTPUT_COST_PATH"] = cost_file_path
        env["CI"] = "1"
        env["PDD_FORCE"] = "1"
        env["PDD_AUTO_UPDATE"] = "false"
        env["TERM"] = "dumb"
        env["PYTHONUNBUFFERED"] = "1"
        if repair_directive:
            env["PDD_REPAIR_DIRECTIVE"] = repair_directive
        else:
            env.pop("PDD_REPAIR_DIRECTIVE", None)
        return env

    def _sync_one_module(self, basename: str) -> Tuple[bool, float, str]:
        """
        Run pdd sync for a single module as one or more subprocess attempts.

        Returns:
            Tuple of (success, total_cost_across_attempts, error_message).
        """
        total_cost = 0.0
        last_missing: Optional[Tuple[str, ...]] = None
        last_error = ""
        last_stdout = ""
        last_stderr = ""
        repair_directive: Optional[str] = None
        module_cwd = Path(self.module_cwds.get(basename, self.project_root))

        def _apply_scope_guard(
            success: bool, total_cost: float, error: str
        ) -> Tuple[bool, float, str]:
            """
            Wrap the result of a per-module attempt with scope-guard
            enforcement (Issue #1013, F6, F7, F8). Runs after every attempt —
            success OR failure — before returning so out-of-scope artifacts
            are reverted even when ``pdd sync`` itself failed.
            """
            diagnostic = self._enforce_scope_guard(basename, module_cwd)
            if diagnostic is None:
                return success, total_cost, error
            scope_failure = (
                "Scope guard hard-fail: out-of-scope artifacts detected\n"
                + diagnostic
            )
            return False, total_cost, scope_failure

        for attempt in range(MAX_CONFORMANCE_ATTEMPTS):
            success, cost, error, stdout, stderr = self._run_attempt(
                basename,
                repair_directive=repair_directive,
                in_flight_cost=total_cost,
            )
            total_cost += cost
            last_error = error
            last_stdout = stdout
            last_stderr = stderr

            if success:
                return _apply_scope_guard(True, total_cost, "")

            conformance = _parse_conformance_failure(stdout, stderr)
            if conformance is None:
                # Not a conformance failure: do not retry
                return _apply_scope_guard(False, total_cost, error)

            new_directive, new_missing = conformance
            if last_missing is not None and new_missing == last_missing:
                # Stuck on identical symbol set — abort and emit hard-failure block
                break
            last_missing = new_missing
            repair_directive = new_directive

            if attempt + 1 >= MAX_CONFORMANCE_ATTEMPTS:
                break
            remaining_budget = self._remaining_total_budget(total_cost)
            if remaining_budget is not None and remaining_budget <= 0.0:
                last_error = (
                    f"Budget exhausted during architecture conformance repair "
                    f"(${total_cost:.2f} spent in {basename})."
                )
                break

        # Hard-failure path: include structured conformance block, then run
        # the scope guard so a failing conformance loop still cleans up
        # out-of-scope writes the LLM made on the way to the failure.
        hard_block = self._build_conformance_hard_failure(
            basename, last_error, last_stdout, last_stderr
        )
        return _apply_scope_guard(False, total_cost, hard_block)

    # ------------------------------------------------------------------
    # Issue #1013 — split-contract scope guard
    # ------------------------------------------------------------------

    def _resolve_repo_root(self, module_cwd: Path) -> Path:
        """
        Return the git toplevel for *module_cwd*, falling back to *module_cwd*
        when git is unavailable or the directory is not in a repo.
        """
        try:
            result = subprocess.run(
                ["git", "-C", str(module_cwd), "rev-parse", "--show-toplevel"],
                capture_output=True,
                text=True,
                timeout=10,
            )
        except (OSError, subprocess.SubprocessError):
            return module_cwd
        if result.returncode != 0:
            return module_cwd
        toplevel = result.stdout.strip()
        if not toplevel:
            return module_cwd
        return Path(toplevel)

    def _scope_guard_lock(self, repo_root: Path) -> threading.Lock:
        """Return a per-repo-root :class:`threading.Lock` (F12)."""
        key = str(repo_root.resolve())
        with self._scope_guard_locks_lock:
            return self._scope_guard_locks[key]

    def _matches_companion_allowlist(
        self, rel_posix_path: str, allowlist: Iterable[str]
    ) -> bool:
        """Return True if *rel_posix_path* matches any companion glob.

        Issue #1013 iter-14 M-1: uses
        :func:`_matches_companion_pattern_anchored` (segment-aware,
        anchored at the START of the path) rather than
        :meth:`pathlib.PurePosixPath.match`. The pathlib matcher is
        suffix-based when the pattern is relative, so
        ``.pdd/meta/*.json`` falsely matches ``subdir/.pdd/meta/foo.json``
        — letting a contract violator bypass the guard by writing
        fingerprint-shaped files nested under any directory.
        """
        for pattern in allowlist:
            if not pattern:
                continue
            # Issue #1013 iter-10 M-1 (defense-in-depth): even if a
            # wildcard-only / doublestar pattern slipped past the parser,
            # refuse to treat it as auto-allowing repo-wide writes.
            if not _is_valid_companion_pattern(pattern):
                continue
            if _matches_companion_pattern_anchored(rel_posix_path, pattern):
                return True
        return False

    def _remaining_out_of_scope_paths(
        self, repo_root: Path, allowed_files: Set[Path]
    ) -> List[str]:
        """
        Iter-9 M-1 (fail-closed boundary): re-scan the worktree after the
        revert helpers have run and return any repo-relative paths still NOT
        in *allowed_files*.

        This guards against silent fail-open when either revert helper
        cannot inspect / revert / remove an out-of-scope path (git timeout,
        permission error, restore failure). Those helpers log a warning and
        return ``[]``; without this re-scan ``_enforce_scope_guard`` would
        treat the empty list as "nothing was out of scope" and let the
        module succeed with the contract still violated on disk.

        Iter-20 M-1 (gitignored fail-open): the standard ``git status`` scan
        does NOT report gitignored files. A sync that writes outside the
        contract into a gitignored path (e.g. ``build/junk.txt`` under a
        repo-wide ``.gitignore: build/``) would be invisible. A SECOND scan
        via ``git ls-files --others --ignored --exclude-standard`` enumerates
        every individual ignored file; results not in ``allowed_files`` and
        not in ``self._baseline_ignored_paths`` (pre-existing ignored files
        the user owned BEFORE sync ran) are added to the ``remaining`` set.

        Returns:
            Sorted list of POSIX repo-relative paths still out of scope, OR
            the sentinel ``["<git-status-failed>"]`` when EITHER the
            ``git status`` scan OR the ``git ls-files --ignored`` scan
            cannot be executed (timeout / missing git / non-zero return).
            The sentinel is consistent with the warning-log + empty-list
            style used elsewhere in the scope guard, but still forces
            ``_enforce_scope_guard`` to hard-fail rather than treat the
            unobservable working tree as clean.
        """
        try:
            result = subprocess.run(
                ["git", "-C", str(repo_root), "status",
                 "--porcelain", "--untracked-files=all"],
                capture_output=True, text=True, timeout=30,
            )
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
            return ["<git-status-failed>"]
        if result.returncode != 0:
            return ["<git-status-failed>"]

        remaining: Set[str] = set()
        for line in result.stdout.splitlines():
            if len(line) < 4:
                continue
            payload = line[3:].strip()
            if not payload:
                continue
            # Renames: ``R  old -> new``. Both sides count.
            if " -> " in payload:
                old_raw, new_raw = payload.split(" -> ", 1)
                entry_paths = [old_raw.strip().strip('"'),
                               new_raw.strip().strip('"')]
            else:
                entry_paths = [payload.strip('"')]
            for rel in entry_paths:
                rel = _normalize_repo_path(rel)
                if not rel:
                    continue
                absolute = (repo_root / rel).resolve()
                if absolute in allowed_files:
                    continue
                remaining.add(rel)

        # Iter-20 M-1: scan for gitignored files that the standard
        # ``git status`` pass above cannot see. ``git ls-files
        # --others --ignored --exclude-standard`` lists every individual
        # ignored file (no directory rollup, no status prefix).
        try:
            ignored_result = subprocess.run(
                ["git", "-C", str(repo_root), "ls-files",
                 "--others", "--ignored", "--exclude-standard"],
                capture_output=True, text=True, timeout=30,
            )
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
            return ["<git-status-failed>"]
        if ignored_result.returncode != 0:
            return ["<git-status-failed>"]

        # Iter-24 M-1: ``_baseline_ignored_paths`` is now a Dict[path, SHA].
        # ``getattr`` fallback keeps the runtime robust against subclasses
        # that bypass __init__ (none in-tree today, but the iter-20 fallback
        # used ``set()`` for the same reason); we still expect a mapping.
        baseline_ignored = getattr(self, "_baseline_ignored_paths", {})
        for line in ignored_result.stdout.splitlines():
            rel = _normalize_repo_path(line.strip().strip('"'))
            if not rel:
                continue
            # Iter-6 B1 / iter-24 M-1: pre-existing ignored files snapshotted
            # at runner init are NOT the sync run's responsibility — but ONLY
            # if their content is byte-identical to the init snapshot. A
            # clobbered ignored baseline path must surface as out-of-scope.
            if rel in baseline_ignored:
                baseline_hash = baseline_ignored[rel]
                current_hash = _hash_file(repo_root, rel)
                # ``current_hash is None`` means the file disappeared from
                # disk between the init snapshot and now — but the ignored
                # scan still listed it, which is contradictory. Fall through
                # to surface it; the diagnostic is the safer direction.
                if (current_hash is not None
                        and (baseline_hash is None
                             or current_hash == baseline_hash)):
                    # Unchanged baseline (or unreadable at init → preserve
                    # by name, same conservative carve-out as the changed
                    # baseline branch in ``_enforce_scope_guard``).
                    continue
            absolute = (repo_root / rel).resolve()
            # Companion-allowlisted files (e.g. ``.pdd/meta/*.json`` when
            # the user has ``.pdd/`` in ``.gitignore``) are in
            # ``allowed_files`` via the rglob pass in ``_enforce_scope_guard``.
            if absolute in allowed_files:
                continue
            remaining.add(rel)

        return sorted(remaining)

    def _enforce_scope_guard(
        self, basename: str, module_cwd: Path
    ) -> Optional[str]:
        """
        Issue #1013 split-contract enforcement after each per-module sync.

        Returns:
            ``None`` when the module is in scope (or enforcement is disabled);
            a multi-line diagnostic string when out-of-scope artifacts were
            detected and reverted/removed.

        This is a no-op when ``self.scope_guard_enabled`` is False or
        ``self.allowed_write_paths is None`` (no parseable contract).
        """
        if not self.scope_guard_enabled:
            return None
        if self.allowed_write_paths is None:
            return None

        repo_root = self._resolve_repo_root(Path(module_cwd))
        lock = self._scope_guard_lock(repo_root)
        with lock:
            # Resolve contract paths to absolute paths under the repo root.
            allowed_files: Set[Path] = set()
            for rel in self.allowed_write_paths:
                if not rel:
                    continue
                allowed_files.add((repo_root / rel).resolve())

            # Auto-allow companion artifacts (e.g. ``.pdd/meta/*.json``) that
            # currently exist or are about to be created under the repo
            # root. We add them to the allowed-files set so the helpers in
            # ``agentic_common`` / ``agentic_common_worktree`` skip them.
            # ``self.companion_allowlist`` already includes DEFAULT_*
            # (unioned in __init__ per F4); no fallback needed here.
            # F1 (Issue #1013 iter-3): only files UNDER ``module_cwd`` count
            # as companion artifacts — never auto-allow a sibling module's
            # ``.pdd/meta/*.json`` just because it lives in the same repo.
            #
            # Iter-14 M-1: companion patterns are matched MODULE-RELATIVE,
            # not repo-relative. The pattern ``.pdd/meta/*.json`` describes
            # fingerprint metadata at the top of each module's working
            # directory; in a multi-module repo where ``module_cwd`` is a
            # subdirectory (e.g. ``mod_a/``), the file lives at
            # ``mod_a/.pdd/meta/x.json`` relative to the repo root but at
            # ``.pdd/meta/x.json`` relative to the module — and the latter
            # is what the segment-aware anchored matcher must see. (The old
            # ``PurePosixPath.match`` suffix-matching obscured this by
            # accidentally auto-allowing the repo-relative form, which also
            # auto-allowed any ``subdir/.pdd/meta/foo.json`` — the bug.)
            allowlist = tuple(self.companion_allowlist)
            cwd_path = Path(module_cwd).resolve()
            for path in cwd_path.rglob("*"):
                if not path.is_file():
                    continue
                try:
                    rel_posix = path.resolve().relative_to(cwd_path).as_posix()
                except ValueError:
                    continue
                if self._matches_companion_allowlist(rel_posix, allowlist):
                    allowed_files.add(path.resolve())

            # Iter-36 B-1/B-2: PDD-internal infrastructure paths
            # (``.pdd/agentic-logs/*``, ``.pdd/agentic_sync_state.json``,
            # etc.) are written by the tool itself during a guarded run
            # (audit logs from ``run_agentic_task``; runner state file
            # from ``_record_result`` after each module). They are
            # NEVER part of a contract. This pass is SEPARATE from the
            # user-facing companion pass above because internal patterns
            # are REPO-ROOT-anchored (the writes happen at the top of
            # the project regardless of which module is being synced) —
            # in the multi-module case ``module_cwd`` is a subdirectory
            # and the audit log under ``<repo_root>/.pdd/agentic-logs/``
            # would NOT match a module-rooted match pass.
            for path in repo_root.rglob("*"):
                if not path.is_file():
                    continue
                try:
                    repo_rel_posix = (
                        path.resolve().relative_to(repo_root).as_posix()
                    )
                except ValueError:
                    continue
                for pattern in PDD_INTERNAL_PATH_ALLOWLIST:
                    if _matches_companion_pattern_anchored(
                        repo_rel_posix, pattern
                    ):
                        allowed_files.add(path.resolve())
                        break

            # Iter-4 F1: rglob only sees files that still exist on disk. Sync
            # legitimately DELETES companion artifacts (e.g. ``.pdd/meta/foo_python.json``
            # when a module is renamed/removed); those deletions appear in
            # ``git status`` as tracked ``D ``. Without this pass the revert
            # helper would resurrect the deleted companion and hard-fail.
            #
            # Iter-14 M-1: ``_git_changed_paths`` returns repo-relative paths;
            # scope to ``cwd_path`` FIRST, then match the module-relative form
            # against the companion pattern (same semantics as the rglob loop
            # above).
            #
            # Iter-38 M-1: ``_git_changed_paths`` now returns ``None`` on
            # scan failure (was empty set). Enforcement-time scan failures
            # are already handled by the ``<git-status-failed>`` sentinel in
            # :meth:`_remaining_out_of_scope_paths`; here we just treat
            # ``None`` as the empty set so the iteration is a no-op rather
            # than crashing.
            for rel_posix in (_git_changed_paths(repo_root) or set()):
                absolute = (repo_root / rel_posix).resolve()
                # Iter-36 B-1/B-2: tracked deletion of a PDD-internal
                # artifact (e.g. ``.pdd/agentic_sync_state.json`` between
                # runs) must not be resurrected by the revert helper.
                # Match against the REPO-relative form before the
                # module-cwd scoping below.
                matched_internal = False
                for pattern in PDD_INTERNAL_PATH_ALLOWLIST:
                    if _matches_companion_pattern_anchored(rel_posix, pattern):
                        allowed_files.add(absolute)
                        matched_internal = True
                        break
                if matched_internal:
                    continue
                try:
                    module_rel_posix = absolute.relative_to(cwd_path).as_posix()
                except ValueError:
                    # Outside the module's cwd — scoped out by F1 iter-3.
                    continue
                if not self._matches_companion_allowlist(module_rel_posix, allowlist):
                    continue
                allowed_files.add(absolute)

            # Iter-6 B1 (data-loss bug): pre-existing untracked files
            # captured at runner __init__ are NEVER out-of-scope. Without
            # this pass, a user's ``scratch.txt`` or unrelated WIP under
            # the repo root would be removed by the revert helper.
            #
            # Iter-24 M-1 (baseline-clobber bug): preservation is now
            # CONTENT-AWARE. Re-hash each baseline path against the
            # init-time SHA. Only byte-identical content is auto-allowed;
            # divergent SHAs fall through to the contract check so a
            # sync-side clobber is surfaced. Note: the init hash uses
            # ``self.project_root`` and the enforcement hash uses
            # ``repo_root`` — in the non-durable async case those resolve
            # to the same path; the durable runner clears the baseline
            # entirely (iter-22) so this loop is a no-op there.
            #
            # Iter-34 M-3 (baseline-deletion blind spot, codex iter-33):
            # ``current_hash is None`` means the baseline file is GONE
            # from disk. For TRACKED baseline paths, ``git status`` will
            # surface this as ``D `` and ``_remaining_out_of_scope_paths``
            # picks it up; but for UNTRACKED baseline paths (the user's
            # local WIP captured at init) git has no record — the
            # deletion is invisible to every subsequent scan and the
            # module would succeed with the WIP silently lost. Collect
            # the deletions here and union them into the diagnostic's
            # ``remaining`` set below.
            baseline_deleted: Set[str] = set()
            for rel_posix, baseline_hash in self._baseline_changed_paths.items():
                current_hash = _hash_file(repo_root, rel_posix)
                if current_hash is None:
                    # Iter-34 M-3: baseline file is GONE. Surface it as
                    # unrecovered regardless of whether it was tracked
                    # or untracked at init — we can't distinguish the
                    # two from the baseline snapshot, and even the
                    # tracked-deletion case warrants a hard-fail (the
                    # user didn't expect their pre-existing file to be
                    # removed by sync).
                    baseline_deleted.add(rel_posix)
                    continue
                if baseline_hash is None:
                    # Couldn't hash at init (the file was unreadable
                    # then). Be conservative and preserve by name, the
                    # legacy iter-6 B1 behaviour — avoids false-positives
                    # on permission-flaky paths that pre-date the run.
                    allowed_files.add((repo_root / rel_posix).resolve())
                    continue
                if current_hash == baseline_hash:
                    # Unchanged user WIP — preserve.
                    allowed_files.add((repo_root / rel_posix).resolve())
                # else: sync (or some other writer) clobbered the file.
                # Do NOT add to allowed_files — let the contract check
                # flag it as out-of-scope.

            # Iter-34 M-3: symmetric pass for ignored baseline paths.
            # ``_remaining_out_of_scope_paths`` only sees files that
            # ``git ls-files --ignored`` currently lists, so a deleted
            # gitignored baseline file (e.g. user-side ``cache.bin``
            # erased by sync) leaves no trail in either scan. Iterate
            # the ignored baseline directly to catch the deletion.
            for rel_posix, baseline_hash in self._baseline_ignored_paths.items():
                current_hash = _hash_file(repo_root, rel_posix)
                if current_hash is None:
                    baseline_deleted.add(rel_posix)
                # Present-but-changed ignored baselines are already
                # surfaced by ``_remaining_out_of_scope_paths``'s
                # ignored loop (the hash comparison there falls through
                # to ``remaining.add`` on divergence). Don't duplicate
                # that work here.

            tracked_reverted = _revert_out_of_scope_changes(repo_root, allowed_files)
            untracked_reverted = revert_out_of_scope_changes_with_dirs(
                repo_root, allowed_dirs=set(), allowed_files=allowed_files
            )

            # Combine while preserving order and uniqueness for the diagnostic.
            seen: Set[str] = set()
            offending: List[str] = []
            for path in list(tracked_reverted) + list(untracked_reverted):
                try:
                    rel = Path(path).resolve().relative_to(repo_root).as_posix()
                except ValueError:
                    rel = str(path)
                if rel in seen:
                    continue
                # Filter out anything that ended up in the allowed set —
                # e.g. companion artifacts that the helpers do not revert
                # but that we still surface as no-ops.
                if (repo_root / rel).resolve() in allowed_files:
                    continue
                seen.add(rel)
                offending.append(rel)

            # Iter-9 M-1 (fail-closed boundary): re-scan the worktree after
            # the revert helpers have run. Either helper can fail silently
            # (git timeout, permission error, restore failure) and return
            # ``[]``. Without this re-scan we would conclude "nothing was
            # out of scope" and let the module succeed with the contract
            # still violated on disk.
            remaining_raw = self._remaining_out_of_scope_paths(
                repo_root, allowed_files
            )
            # Filter out paths already surfaced as ``offending`` so the
            # re-scan does not double-list. In practice when helpers succeed
            # the path is gone from ``git status``; when helpers fail with
            # ``reverted.clear()`` ``offending`` is empty. Defensive filter.
            #
            # Iter-34 M-3: union with ``baseline_deleted`` so a sync-side
            # deletion of a pre-existing untracked/ignored baseline path
            # hard-fails the module. For tracked baselines ``git status``
            # already surfaces the deletion as ``D ``, so the union just
            # dedups via set semantics.
            offending_set = set(offending)
            remaining = sorted(
                (set(remaining_raw) | baseline_deleted) - offending_set
            )

            if not offending and not remaining:
                return None

            source = self.contract_source or "<unknown>"
            allowed_lines = "\n".join(
                f"  - {p}" for p in sorted(self.allowed_write_paths)
            ) or "  - <empty>"
            companion_lines = "\n".join(
                f"  - {p}" for p in allowlist
            ) or "  - <empty>"

            # Header line shape depends on whether anything was actually
            # reverted. When ``offending`` is empty but ``remaining`` is
            # non-empty, emitting "reverted 0 out-of-scope file(s)" plus an
            # empty bullet list reads incorrectly; use a distinct header.
            if offending:
                offending_lines = "\n".join(f"  - {p}" for p in offending)
                header = (
                    f"Scope guard reverted {len(offending)} out-of-scope "
                    f"file(s) for module '{basename}' "
                    f"(contract source: {source}):\n"
                    f"{offending_lines}"
                )
            else:
                header = (
                    f"Scope guard detected out-of-scope artifacts for "
                    f"module '{basename}' (contract source: {source}) "
                    f"but the revert helpers reported no successful reverts."
                )

            parts = [header]
            if remaining:
                unrecovered_lines = "\n".join(f"  - {p}" for p in remaining)
                parts.append(
                    "Unrecovered (revert failed, manual cleanup required):\n"
                    f"{unrecovered_lines}"
                )
            parts.append(f"Allowed write set:\n{allowed_lines}")
            parts.append(f"Companion allowlist:\n{companion_lines}")
            diagnostic = "\n".join(parts)
            # F8 (Issue #1013): print the diagnostic to stderr immediately
            # after reverting. ``maintenance.py`` separately echoes the
            # assembled module-failure error at the end of the run — two
            # distinct events, so keep both.
            print(diagnostic, file=sys.stderr)
            return diagnostic

    def _build_conformance_hard_failure(
        self,
        basename: str,
        failure_summary: str,
        stdout: str,
        stderr: str,
    ) -> str:
        """Build the structured hard-failure error string after retries."""
        conformance = _parse_conformance_failure(stdout, stderr)
        missing_symbols: Tuple[str, ...] = (
            conformance[1] if conformance else tuple()
        )

        prompt_field = "<unknown>"
        combined = (stdout or "") + "\n" + (stderr or "")
        field_boundary = r"(?=\.\s+(?:Output|Expected|Found)\b|\.\s*$|\n|$)"

        def _extract_field(label: str, default: str = "<unknown>") -> str:
            pattern = re.compile(
                rf"{re.escape(label)}:\s*(.*?){field_boundary}",
                re.DOTALL,
            )
            match = pattern.search(combined)
            if not match:
                return default
            value = match.group(1).strip().rstrip(".").strip()
            return value or default

        for line in combined.splitlines():
            if _CONFORMANCE_PREFIX in line:
                tail = line.split(_CONFORMANCE_PREFIX, 1)[1].strip()
                prompt_field = tail.split(":", 1)[0].strip() if ":" in tail else tail
                break

        output_field = _extract_field("Output")
        expected_field = _extract_field("Expected")
        found_field = _extract_field("Found")

        block_lines = [
            failure_summary or "Architecture conformance failure",
            "",
            "=== architecture conformance failure ===",
            f"prompt: {prompt_field}",
            f"output: {output_field}",
            f"expected: {expected_field}",
            f"found: {found_field}",
            "missing: "
            + (", ".join(missing_symbols) if missing_symbols else "<none>"),
            "",
            f"Reproduce locally: pdd sync {basename}",
            "",
            _env_fingerprint(),
        ]
        return "\n".join(block_lines)

    def _run_attempt(
        self,
        basename: str,
        repair_directive: Optional[str] = None,
        in_flight_cost: float = 0.0,
    ) -> Tuple[bool, float, str, str, str]:
        """
        Execute a single subprocess attempt.

        Returns (success, cost, error, stdout, stderr).
        """
        cmd = self._build_command(basename, in_flight_cost=in_flight_cost)

        cost_file = tempfile.NamedTemporaryFile(suffix=".csv", delete=False)
        cost_file.close()

        env = self._build_env(cost_file.name, repair_directive=repair_directive)

        if not self.quiet:
            try:
                console.print(f"[blue]Starting sync: {basename}[/blue]")
            except Exception:
                pass

        stdout_lines: List[str] = []
        stderr_lines: List[str] = []
        verbose_print = self.verbose and not self.quiet
        line_lock = threading.Lock()

        def _read_stream(stream, lines_list: List[str], prefix: str = "") -> None:
            try:
                for line in iter(stream.readline, ''):
                    if not line:
                        break
                    with line_lock:
                        lines_list.append(line)
                    stripped = line.strip()
                    if stripped.startswith("PDD_PHASE: "):
                        phase = stripped[len("PDD_PHASE: "):]
                        try:
                            self._on_phase_change(basename, phase)
                        except Exception:
                            pass
                    if "Successfully submitted example" in stripped:
                        try:
                            print(f"[{basename}] Example submitted to cloud")
                        except Exception:
                            pass
                    if verbose_print:
                        try:
                            console.print(
                                f"[dim]{prefix}{basename}>[/dim] {line.rstrip()}"
                            )
                        except Exception:
                            pass
            except Exception:
                pass
            finally:
                try:
                    stream.close()
                except Exception:
                    pass

        cwd_value = self.module_cwds.get(basename, str(self.project_root))
        cwd_str = str(cwd_value)

        try:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                stdin=subprocess.DEVNULL,
                cwd=cwd_str,
                env=env,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
            try:
                self._child_pgids.add(process.pid)
            except Exception:
                pass
        except Exception as exc:
            try:
                cost = _parse_cost_from_csv(cost_file.name)
            except Exception:
                cost = 0.0
            try:
                os.unlink(cost_file.name)
            except OSError:
                pass
            return False, cost, str(exc), "", ""

        t_out = threading.Thread(
            target=_read_stream,
            args=(process.stdout, stdout_lines, ""),
            daemon=True,
        )
        t_err = threading.Thread(
            target=_read_stream,
            args=(process.stderr, stderr_lines, "err:"),
            daemon=True,
        )
        t_out.start()
        t_err.start()

        try:
            timeout_adder = float(self.sync_options.get("timeout_adder") or 0.0)
        except (TypeError, ValueError):
            timeout_adder = 0.0
        effective_timeout = MODULE_TIMEOUT + max(0.0, timeout_adder)

        exit_code: int = 1
        timed_out = False

        try:
            with self.lock:
                start_wall = (
                    self.module_states[basename].start_time or time.time()
                )
            last_heartbeat = time.time()
            while True:
                elapsed_total = time.time() - start_wall
                remaining = max(effective_timeout - elapsed_total, 0)
                wait_for = min(HEARTBEAT_INTERVAL, max(remaining, 1))
                try:
                    exit_code = process.wait(timeout=wait_for)
                    break
                except subprocess.TimeoutExpired:
                    elapsed_total = time.time() - start_wall
                    if elapsed_total >= effective_timeout:
                        timed_out = True
                        break
                    now = time.time()
                    if not self.quiet and (now - last_heartbeat) >= HEARTBEAT_INTERVAL:
                        mins = int(elapsed_total) // 60
                        secs = int(elapsed_total) % 60
                        with self.lock:
                            state = self.module_states[basename]
                            current_phase = state.current_phase
                            done_count = len(state.completed_phases)
                        if current_phase:
                            hint = (
                                f" — phase: {current_phase} "
                                f"({done_count} done)"
                            )
                        else:
                            last_line = ""
                            with line_lock:
                                for line in reversed(stdout_lines):
                                    stripped = line.strip()
                                    if stripped and not _BOX_CHARS_RE.match(
                                        stripped
                                    ):
                                        last_line = stripped
                                        break
                            hint = f" — {last_line[:80]}" if last_line else ""
                        try:
                            print(
                                f"  {basename}: still running "
                                f"({mins}m{secs}s){hint}"
                            )
                        except Exception:
                            pass
                        last_heartbeat = now
        finally:
            try:
                self._child_pgids.discard(process.pid)
            except Exception:
                pass

        if timed_out:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except OSError:
                try:
                    process.terminate()
                except Exception:
                    pass
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except OSError:
                    try:
                        process.kill()
                    except Exception:
                        pass
                try:
                    process.wait(timeout=5)
                except Exception:
                    pass

            t_out.join(timeout=2)
            t_err.join(timeout=2)
            cost = _parse_cost_from_csv(cost_file.name)
            try:
                os.unlink(cost_file.name)
            except OSError:
                pass
            stdout = "".join(stdout_lines)
            stderr = "".join(stderr_lines)
            return (
                False,
                cost,
                f"Timeout after {int(effective_timeout)}s waiting for sync",
                stdout,
                stderr,
            )

        t_out.join(timeout=5)
        t_err.join(timeout=5)

        cost = _parse_cost_from_csv(cost_file.name)
        try:
            os.unlink(cost_file.name)
        except OSError:
            pass

        stdout = "".join(stdout_lines)
        stderr = "".join(stderr_lines)

        success = exit_code == 0
        if success:
            for line in stdout.splitlines():
                if "Overall status:" in line and "Failed" in line:
                    success = False
                    break

        if not self.quiet:
            try:
                tag = "success" if success else "FAILED"
                color = "green" if success else "red"
                console.print(
                    f"[{color}]Sync {basename}: {tag}[/{color}]"
                )
            except Exception:
                pass

        if success:
            return True, cost, "", stdout, stderr

        # Build failure-summary
        failure_reason = f"Exit code {exit_code}"
        for line in stdout.splitlines():
            if "Overall status:" in line and "Failed" in line:
                failure_reason = line.strip()
                break

        all_output = (stderr or "") + "\n" + (stdout or "")
        info_debug_re = re.compile(
            r"^\d{4}-\d{2}-\d{2} .* - (INFO|DEBUG)( |-)"
        )
        candidate_lines: List[str] = []
        for line in all_output.splitlines():
            if not line.strip():
                continue
            if info_debug_re.match(line):
                continue
            if _is_nonfatal_warning(line):
                continue
            candidate_lines.append(line)

        keyword_lines = [
            line
            for line in candidate_lines
            if line.strip() != failure_reason
            and any(
                kw in line.lower()
                for kw in ("error", "failed", "traceback", "exception", "abort")
            )
        ]

        summary_parts: List[str] = [failure_reason]
        if keyword_lines:
            summary_parts.append("\n".join(keyword_lines[-20:]))
        else:
            stderr_tail = [
                line
                for line in (stderr or "").splitlines()
                if line.strip()
                and line.strip() != failure_reason
                and not _is_nonfatal_warning(line)
            ][-10:]
            stdout_tail = [
                line
                for line in (stdout or "").splitlines()
                if line.strip()
                and line.strip() != failure_reason
                and not _is_nonfatal_warning(line)
            ][-10:]
            if stderr_tail:
                summary_parts.append(
                    "--- stderr tail ---\n" + "\n".join(stderr_tail)
                )
            if stdout_tail:
                summary_parts.append(
                    "--- stdout tail ---\n" + "\n".join(stdout_tail)
                )

        error = "\n".join(p for p in summary_parts if p)
        if not self.quiet:
            try:
                console.print(
                    f"[red]  Error for {basename}:[/red] {error[:500]}"
                )
            except Exception:
                pass

        return False, cost, error, stdout, stderr
