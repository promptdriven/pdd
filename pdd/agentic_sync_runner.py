"""
Async sync runner: parallel module sync with dependency-aware scheduling.

Manages concurrent `pdd sync` subprocesses, respects dependency ordering,
updates a live GitHub issue comment with progress, and pauses on failure.
"""
from __future__ import annotations

import collections
import codecs
import csv as _csv
import datetime
import json
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Tuple

from rich.console import Console

from .agentic_common import (
    drain_step_steers,
    ensure_issue_steer_cursor_seeded,
    peek_agentic_progress_steer_metadata,
)
from .construct_paths import (
    _detect_context_from_basename,
    _find_pddrc_file,
    _is_known_language,
    _load_pddrc_config,
)
from .resolved_sync_unit import ResolvedSyncUnit
from .sync_order import compute_sccs

console = Console()

# ---------------------------------------------------------------------------
# Module-level constants and helpers
# ---------------------------------------------------------------------------

def _read_sync_max_workers() -> int:
    """Read PDD_SYNC_MAX_WORKERS, preserving default 4 and clamping 1-4."""
    try:
        return max(1, min(4, int(os.environ.get("PDD_SYNC_MAX_WORKERS", "4"))))
    except ValueError:
        return 4


# Backwards-compatible module constant; AsyncSyncRunner reads the env at init.
MAX_WORKERS = _read_sync_max_workers()

# Maximum output retained per stream when capturing child subprocess output.
# The line limit keeps parser work bounded; the byte limit protects against
# very long lines that would otherwise bypass a line-only cap.
STDOUT_CAPTURE_LINE_LIMIT = 5000
STDOUT_CAPTURE_BYTE_LIMIT = 1024 * 1024
OUTPUT_CAPTURE_READ_CHUNK_SIZE = 8192


class _BoundedTextCapture:
    """Tail capture with both line and UTF-8 byte caps."""

    def __init__(self, *, line_limit: int, byte_limit: int) -> None:
        self.line_limit = max(1, int(line_limit))
        self.byte_limit = max(1, int(byte_limit))
        self.lines: collections.deque[str] = collections.deque()
        self.byte_count = 0
        self.dropped_lines = 0
        self.dropped_bytes = 0
        self._partial = ""

    @staticmethod
    def _byte_len(text: str) -> int:
        return len(text.encode("utf-8", errors="replace"))

    def _trim_to_byte_limit(self, text: str) -> str:
        encoded = text.encode("utf-8", errors="replace")
        if len(encoded) <= self.byte_limit:
            return text
        tail = encoded[-self.byte_limit:].decode("utf-8", errors="ignore")
        self.dropped_bytes += len(encoded) - self._byte_len(tail)
        return tail

    def _drop_oldest(self) -> None:
        dropped = self.lines.popleft()
        dropped_len = self._byte_len(dropped)
        self.byte_count -= dropped_len
        self.dropped_lines += 1
        self.dropped_bytes += dropped_len

    def _append_line(self, line: str) -> None:
        line = self._trim_to_byte_limit(line)
        line_len = self._byte_len(line)
        while len(self.lines) >= self.line_limit:
            self._drop_oldest()
        while self.lines and self.byte_count + line_len > self.byte_limit:
            self._drop_oldest()
        self.lines.append(line)
        self.byte_count += line_len

    def _trim_partial(self) -> None:
        self._partial = self._trim_to_byte_limit(self._partial)

    def feed(self, text: str) -> List[str]:
        if not text:
            return []
        text = self._partial + text
        self._partial = ""
        parts = text.splitlines(keepends=True)
        if parts and not parts[-1].endswith(("\n", "\r")):
            self._partial = parts.pop()
            self._trim_partial()
        for line in parts:
            self._append_line(line)
        return parts

    def finish(self) -> List[str]:
        if not self._partial:
            return []
        line = self._partial
        self._partial = ""
        self._append_line(line)
        return [line]

    def text(self) -> str:
        return "".join(self.lines)

    def reversed_lines(self):
        return reversed(self.lines)

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
    # Issue #1903 §B.4: set when an unreconcilable adopted co-located test was
    # kept unchanged and flagged for review instead of hard-failing the
    # issue-driven workflow. The module still counts as ``success`` (the PR is
    # opened); this note surfaces in the progress comment / PR thread.
    needs_review: Optional[str] = None


class DepGraphFromArchitectureResult(NamedTuple):
    """Dependency subgraph from architecture.json plus validation warnings."""

    graph: Dict[str, List[str]]
    warnings: List[str]


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


def _resolve_issue_protected_base(root: Path) -> Optional[str]:
    """Pin immutable ownership authority before issue-driven children run."""
    repository = Path(root).resolve()
    configured = os.environ.get("PDD_PROTECTED_BASE_REF", "").strip()
    try:
        if configured:
            command = ["git", "rev-parse", "--verify", f"{configured}^{{commit}}"]
        else:
            symbolic = subprocess.run(
                ["git", "symbolic-ref", "--quiet", "refs/remotes/origin/HEAD"],
                cwd=repository,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            remote_ref = symbolic.stdout.strip() if symbolic.returncode == 0 else "origin/main"
            remote = subprocess.run(
                ["git", "rev-parse", "--verify", f"{remote_ref}^{{commit}}"],
                cwd=repository,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            command = (
                ["git", "merge-base", "HEAD", remote_ref]
                if remote.returncode == 0
                else ["git", "rev-parse", "--verify", "HEAD^{commit}"]
            )
        resolved = subprocess.run(
            command,
            cwd=repository,
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return resolved.stdout.strip() if resolved.returncode == 0 else None


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
_PROSE_OUTPUT_PREFIX = "Generation output extraction failure for "
_PROSE_OUTPUT_REPAIR_DIRECTIVE = (
    "The previous response contained no extractable code. Return the complete "
    "source file only, inside a single code block. Do not include any planning "
    "text, prose explanation, or partial snippets outside the code block."
)
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
_PUBLIC_SURFACE_PREFIX = "Public surface regression for "
_TEST_CHURN_PREFIX = "Test churn threshold exceeded for "
# Issue #1903 §B.4: emitted (stdout) when an unreconcilable adopted co-located
# test is kept and flagged for review instead of hard-failing the issue workflow.
_TEST_CHURN_NEEDS_REVIEW_MARKER = "PDD_TEST_CHURN_NEEDS_REVIEW"
_TEST_OUTPUT_NEEDS_REVIEW_MARKER = "PDD_TEST_OUTPUT_NEEDS_REVIEW"


def _extract_test_output_needs_review(stdout: str) -> Optional[str]:
    """Read a child-emitted opaque-runner non-write note, if present."""
    for line in (stdout or "").splitlines():
        if _TEST_OUTPUT_NEEDS_REVIEW_MARKER not in line:
            continue
        note = line.split(_TEST_OUTPUT_NEEDS_REVIEW_MARKER, 1)[1].lstrip(" :")
        if note:
            return note
    return None
# Env var naming the pipe FD the child reads the churn-provenance nonce from
# (issue #1903 §B.4 review round 8). MUST match code_generator_main._CHURN_NONCE_ENV.
_CHURN_NONCE_ENV = "PDD_CHURN_NONCE_FD"
# ``subprocess.Popen(pass_fds=...)`` is POSIX-only.  On platforms without it,
# omit the nonce channel and fail closed: churn blocks cannot authenticate, so
# the issue-driven never-block exception remains disabled while sync still runs.
_CHURN_NONCE_PASS_FDS_SUPPORTED = os.name == "posix"


_TEST_CHURN_HEADERS = (
    "=== test churn threshold exceeded ===",
    "Test churn threshold exceeded for ",
)


def _test_churn_block_regions(stdout: str, stderr: str) -> list[str]:
    """Every test-churn block region in the captured output.

    Each region runs from a churn header to the next header (or end). Field
    extraction is scoped to these regions so an UNRELATED ``output:``/``adopted:``
    diagnostic line OUTSIDE any churn block is ignored (round 3). But it scans
    ALL blocks — not just the last — so a forged churn block injected by
    untrusted test output cannot silently OVERRIDE the real one: the extractors
    require the fields to be UNANIMOUS across every block and otherwise fail
    closed, so an attacker who prints a conflicting block only causes a strict
    hard-fail, never a flipped never-block (issue #1903 review round 6, forgeable
    provenance). A fully in-band signal is not attacker-proof; this raises the
    bar and defaults to the safe outcome.
    """
    combined = (stdout or "") + "\n" + (stderr or "")
    starts = sorted(
        idx
        for header in _TEST_CHURN_HEADERS
        for idx in _all_indices(combined, header)
    )
    regions: list[str] = []
    for i, start in enumerate(starts):
        end = starts[i + 1] if i + 1 < len(starts) else len(combined)
        regions.append(combined[start:end])
    return regions


def _all_indices(text: str, sub: str) -> list[int]:
    out, start = [], 0
    while True:
        idx = text.find(sub, start)
        if idx < 0:
            break
        out.append(idx)
        start = idx + 1
    return out


def _region_has_valid_nonce(region: str, expected_nonce: Optional[str]) -> bool:
    """True when *region* carries a ``nonce:`` matching *expected_nonce* (round 8).

    The parent hands each child a secret nonce over a non-inherited pipe FD; a
    genuine PDD churn block echoes it, an untrusted project-test forgery cannot.
    Constant-time compare. When no nonce is expected (``None``/empty), no region
    can be authenticated so this is False.
    """
    if not expected_nonce:
        return False
    m = re.search(r"^nonce:\s*([0-9a-f]{8,128})\s*$", region, re.MULTILINE)
    return bool(m) and secrets.compare_digest(m.group(1), expected_nonce)


def _test_churn_block_regions_trusted(
    stdout: str, stderr: str, expected_nonce: Optional[str]
) -> list[str]:
    """Churn regions used for provenance. When *expected_nonce* is provided
    (the issue-driven never-block), ONLY regions bearing the matching nonce are
    trusted — a forged in-band block is dropped, not merely out-voted. When it is
    ``None`` (standalone/tests), all regions are considered (legacy behavior)."""
    regions = _test_churn_block_regions(stdout, stderr)
    if expected_nonce is None:
        return regions
    return [r for r in regions if _region_has_valid_nonce(r, expected_nonce)]


def _extract_test_churn_output_path(
    stdout: str, stderr: str, expected_nonce: Optional[str] = None
) -> Optional[str]:
    """The churned ``output: <test path>`` — UNANIMOUS across all TRUSTED churn
    blocks.

    Fails CLOSED to ``None`` when absent or when any two churn blocks disagree,
    so a forged/injected block cannot substitute a different path. With
    *expected_nonce* set, only nonce-authenticated blocks are consulted.

    Round 10: validated PER BLOCK, then unanimous across blocks — a trusted block
    MISSING the field (or carrying conflicting values WITHIN it) fails closed,
    honoring the "ANY conflict OR absence fails closed" contract rather than
    letting one complete block cover for an incomplete sibling.
    """
    regions = _test_churn_block_regions_trusted(stdout, stderr, expected_nonce)
    if not regions:
        return None
    per_block: set[str] = set()
    for region in regions:
        vals = {
            m.group(1).strip()
            for m in re.finditer(r"^output:\s*(.+)$", region, re.MULTILINE)
            if m.group(1).strip()
        }
        if len(vals) != 1:
            return None  # a trusted block missing/conflicting output -> fail closed
        per_block.add(next(iter(vals)))
    return next(iter(per_block)) if len(per_block) == 1 else None


def _extract_test_churn_adopted(
    stdout: str, stderr: str, expected_nonce: Optional[str] = None
) -> bool:
    """The ``adopted:`` provenance — True ONLY when UNANIMOUSLY ``true`` across
    every TRUSTED churn block. A missing marker, any ``false``, or a conflict →
    False (keep the strict hard-fail), so injecting an ``adopted: true`` cannot
    flip a real ``adopted: false`` churn (issue #1903 review round 6). With
    *expected_nonce* set (round 8), a block that does not carry the parent's
    secret nonce is not trusted at all — so a hostile project test that merely
    PRINTS ``adopted: true`` is ignored and the module keeps the strict hard-fail.
    Round 10: validated PER BLOCK — a trusted block MISSING the ``adopted:``
    marker (or carrying both values) fails closed, so an incomplete authenticated
    block cannot be covered for by a complete one.
    """
    regions = _test_churn_block_regions_trusted(stdout, stderr, expected_nonce)
    if not regions:
        return False
    per_block: set[str] = set()
    for region in regions:
        vals = {
            m.group(1).lower()
            for m in re.finditer(
                r"^adopted:\s*(true|false)\s*$", region, re.MULTILINE | re.IGNORECASE
            )
        }
        if len(vals) != 1:
            return False  # a trusted block missing/conflicting adopted -> fail closed
        per_block.add(next(iter(vals)))
    return per_block == {"true"}


def _is_adopted_collocated_test_path(
    test_path: Optional[str], *, project_root: Optional[Path] = None
) -> bool:
    """True only when *test_path* is an IN-REPO, co-located (adopted) test.

    The never-block relief exists to keep a co-located test PDD adopted — NOT to
    silently swallow coverage loss on a PDD-owned test or to act on a path
    outside the project. This is a NECESSARY (not sufficient) gate: pathname
    shape alone cannot prove human authorship, so it composes with the
    ``self.issue_url`` guard and the upstream coverage-preserving auto-accept.

    Production churn paths are typically ABSOLUTE (``construct_paths`` /
    ``resolve_test_output_path`` emit a canonical absolute path). Such a path is
    accepted only after canonical containment in *project_root* (the worktree
    root); it is then reduced to its repo-relative form for the shape checks. An
    absolute path with no root to validate against, an out-of-root path, or any
    ``..`` traversal (CWE-022) is rejected. PDD's derived shadow root (a
    top-level ``tests/`` directory — ``tests/test_foo.py`` OR ``tests/foo.test.ts``)
    is never "adopted". Accepts a runner co-location convention: a file under a
    ``__test__``/``__tests__`` directory, a basename containing ``.test.``/
    ``.spec.`` (JS/TS), or a Python sibling basename ``test_<stem>.py`` /
    ``<stem>_test.py`` OUTSIDE that top-level ``tests/`` shadow (issue #1903
    supports adopting an existing co-located Python sibling, whose churn must
    reach the same never-block — review round 8). Never raises.
    """
    if not test_path:
        return False
    normalized = test_path.replace("\\", "/").strip()
    if not normalized:
        return False
    is_absolute = normalized[0] in "/~\\" or bool(re.match(r"^[A-Za-z]:", normalized))
    # Canonicalize BOTH absolute and relative paths against the worktree root and
    # require containment (issue #1903 review round 6): a relative path whose
    # segment is a symlink escaping the root (`src/link/foo.test.ts`) must be
    # rejected, not merely lexically checked for ``..``. No trusted root -> fail
    # closed for absolute paths; a relative path with no root falls back to a
    # lexical-only check (best effort, still rejecting ``..``).
    if is_absolute or project_root is not None:
        if project_root is None:
            return False
        try:
            root_resolved = Path(project_root).resolve()
            raw = Path(test_path).expanduser()
            resolved = (raw if raw.is_absolute() else (root_resolved / normalized)).resolve()
            rel = resolved.relative_to(root_resolved)  # raises if outside root (incl. symlink escape)
        except (ValueError, OSError, RuntimeError):
            return False
        segments = [seg for seg in rel.as_posix().split("/") if seg]
    else:
        segments = [seg for seg in normalized.split("/") if seg]
        if any(seg == ".." for seg in segments):
            return False  # traversal escape
    if not segments:
        return False
    # PDD's derived shadow root (top-level ``tests/``) is never "adopted".
    if segments[0] == "tests":
        return False
    if "__test__" in segments or "__tests__" in segments:
        return True
    name = segments[-1].lower()
    if ".test." in name or ".spec." in name:
        return True
    # Python co-located sibling conventions (round 8): ``test_<stem>.py`` or
    # ``<stem>_test.py`` outside the top-level ``tests/`` shadow (already
    # excluded above). #1903 adopts an existing Python sibling test, whose churn
    # must reach the same never-block as JS ``.test.``/``.spec.`` siblings.
    if name.endswith(".py") and (name.startswith("test_") or name.endswith("_test.py")):
        return True
    return False


def _parse_prose_output_failure(
    stdout: str, stderr: str
) -> Optional[Tuple[str, Tuple[str, ...]]]:
    """Detect a prose/empty-output extraction failure in subprocess output."""
    combined = (stdout or "") + "\n" + (stderr or "")
    if _PROSE_OUTPUT_PREFIX not in combined:
        return None
    return _PROSE_OUTPUT_REPAIR_DIRECTIVE, ("prose",)


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


def build_prose_output_hard_failure_from_error(
    exc: Any,
    basename: str,
) -> str:
    """Format a structured generation-output extraction hard-failure block."""
    block_lines = [
        str(exc),
        "",
        "=== generation output extraction failure ===",
        f"prompt: {getattr(exc, 'prompt_name', '') or '<unknown>'}",
        f"output: {getattr(exc, 'output_path', '') or '<unknown>'}",
        f"language: {getattr(exc, 'language', '') or '<unknown>'}",
        f"model: {getattr(exc, 'model_name', '') or '<unknown>'}",
        f"extractor_result: {getattr(exc, 'extractor_result', '') or '<unknown>'}",
        f"raw_output_excerpt: {getattr(exc, 'raw_output_excerpt', '') or '<unknown>'}",
        (
            "note: The model returned no extractable code. Check that the "
            "provider/model is configured to return complete source files, not "
            "planning text or agentic responses."
        ),
        "",
        f"Reproduce locally: pdd sync {basename}",
        "",
        _env_fingerprint(),
    ]
    return "\n".join(block_lines)


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


def _parse_signature_detail_lines(combined: str) -> List[Tuple[str, str, str, str]]:
    """Parse ``signature_detail:`` lines into ``(symbol, expected, actual, source)``.

    A ``signature_detail:`` line carries the full expected-vs-actual contract for
    one declared signature mismatch (issue #1900). The subprocess path rebuilds
    the repair directive from stdout, so it must recover these lines to keep the
    DECLARED expected signature — the stable repair target — in the directive and
    the hard-failure block. Emitted by ``PublicSurfaceRegressionError`` and
    ``_build_public_surface_hard_failure`` as a JSON object:
      ``signature_detail: {"symbol": ..., "expected": ..., "actual": ..., "source": ...}``

    JSON is bulletproof against signatures/defaults that contain the old ` | ` /
    ``| actual: `` / ``| source: `` field delimiters (PEP-604 unions, string
    defaults) — a class of corruption that recurred across several review passes
    (codex round-8 finding 2). A line whose payload is not a well-formed JSON
    object with the four string fields is SKIPPED (never raises). De-duplicated,
    preserving first-seen order.
    """
    details: List[Tuple[str, str, str, str]] = []
    seen: set = set()
    for raw_line in combined.splitlines():
        line = raw_line.strip()
        if not line.startswith("signature_detail:"):
            continue
        payload = line[len("signature_detail:"):].strip()
        try:
            obj = json.loads(payload)
            detail = (
                str(obj["symbol"]),
                str(obj["expected"]),
                str(obj["actual"]),
                str(obj["source"]),
            )
        except (ValueError, TypeError, KeyError):
            # Not a well-formed JSON detail object -> malformed line, skip it.
            continue
        if detail in seen:
            continue
        seen.add(detail)
        details.append(detail)
    return details


def _parse_public_surface_failure_fields(
    stdout: str, stderr: str
) -> Optional[
    Tuple[
        str,
        Tuple[str, ...],
        Tuple[str, ...],
        Tuple[Tuple[str, str, str, str], ...],
    ]
]:
    """Detect a public-surface regression and keep removals/signatures separate."""
    combined = (stdout or "") + "\n" + (stderr or "")
    if _PUBLIC_SURFACE_PREFIX not in combined:
        return None
    match = re.search(r"^removed:\s*(.+)$", combined, re.MULTILINE)
    if not match:
        match = re.search(
            r"removed public symbols:\s*(.+?)"
            r"(?=\.\s+(?:Output|Pre surface size|Post surface size)\b|\.\s*$|\n|$)",
            combined,
            re.MULTILINE,
        )
    removed_text = match.group(1) if match else ""
    removed = tuple(
        sorted(
            {
                token.strip().strip("`'\"").rstrip(".")
                for token in removed_text.split(",")
                if token.strip() and token.strip() != "<none>"
            }
        )
    )
    changed_match = re.search(r"^signature_changed:\s*(.+)$", combined, re.MULTILINE)
    changed_text = changed_match.group(1) if changed_match else ""
    changed = tuple(
        sorted(
            {
                token.strip().strip("`'\"").rstrip(".")
                for token in changed_text.split(",")
                if token.strip() and token.strip() != "<none>"
            }
        )
    )
    # Preserve declaration source order (de-duped) so the directive lists the
    # declared repair targets deterministically.
    details_tuple = tuple(_parse_signature_detail_lines(combined))
    if not removed and not changed:
        return None
    lines = ["Public surface regression repair required."]
    if removed:
        lines.append("Restore these public symbols from the existing module:")
        for sym in removed:
            lines.append(f"- {sym}")
    # Prefer the DECLARED signature as the repair target: it is a stable target,
    # unlike "restore compatible signatures" (compatible with the code being
    # regenerated), which dead-ended the change->sync loop (issue #1900).
    declared_details = [d for d in details_tuple if d[3] == "pdd-interface"]
    if declared_details:
        # Inject the DECLARED signature as a VERBATIM hard constraint, not just a
        # description of the violation (issue #1968): annotation-level drift
        # (declared `object`, regenerated `Any`; or a broadened param union)
        # converges only when the retry is told to reproduce the declared
        # annotation text token-for-token instead of a "compatible" spelling.
        lines.append(
            "Restore these public symbols to their declared "
            "<pdd-interface> signatures — emit each declared signature "
            "VERBATIM. Reproduce the declared annotation text token-for-token; "
            "do not substitute an equivalent-but-differently-spelled type (keep "
            "`object` as `object`; never emit `Any` where the declaration says "
            "`object`) and do not broaden a declared parameter's type with `|` "
            "union members the declaration omits:"
        )
        for symbol, expected_entry, actual_entry, _ in declared_details:
            lines.append(
                f"- Restore `{symbol}` to its declared signature "
                f"`{expected_entry}` (found `{actual_entry}`). Emit exactly "
                f"`{expected_entry}` — the prior attempt emitted "
                f"`{actual_entry}`, which differs only in annotation spelling "
                f"and was rejected."
            )
        lines.append(
            "If a declared parameter change is intended, edit the prompt's "
            "<pdd-interface> declaration to the intended signature (the "
            "declaration is the contract for declared symbols)."
        )
    declared_changed = {d[0] for d in declared_details}
    remaining_changed = [sym for sym in changed if sym not in declared_changed]
    if remaining_changed:
        lines.append("Restore compatible signatures for these public symbols:")
        for sym in remaining_changed:
            lines.append(f"- {sym}")
    # Keep the BREAKING-CHANGE guidance only for UNDECLARED / removed violations:
    # for a declared symbol it relaxes only binding-kind/async, not the declared
    # params, so advising it on a pure declared-param violation loops the user
    # back into the dead-end #1900 removes (codex round-7 finding 3).
    if removed or remaining_changed or not declared_details:
        lines.append(
            "Preserve backward-compatible public helpers unless the prompt lists "
            "the intended changes with scoped BREAKING-CHANGE: remove <symbol> "
            "or BREAKING-CHANGE: change signature <symbol> markers."
        )
    return "\n".join(lines), removed, changed, details_tuple


def _parse_public_surface_failure(
    stdout: str, stderr: str
) -> Optional[Tuple[str, Tuple[str, ...]]]:
    """Detect a public-surface regression in subprocess output."""
    parsed = _parse_public_surface_failure_fields(stdout, stderr)
    if parsed is None:
        return None
    directive, removed, changed, _details = parsed
    signature = tuple(
        [f"removed:{symbol}" for symbol in removed]
        + [f"signature_changed:{symbol}" for symbol in changed]
    )
    return directive, signature


def _parse_test_churn_failure(
    stdout: str, stderr: str
) -> Optional[Tuple[str, Tuple[str, ...]]]:
    """Detect a test-churn failure in subprocess output."""
    combined = (stdout or "") + "\n" + (stderr or "")
    if _TEST_CHURN_PREFIX not in combined:
        return None
    ratio = "unknown"
    threshold = "unknown"
    match = re.search(r"^ratio:\s*([0-9.]+)", combined, re.MULTILINE)
    threshold_match = re.search(r"^threshold:\s*([0-9.]+)", combined, re.MULTILINE)
    if match and threshold_match:
        ratio, threshold = match.group(1), threshold_match.group(1)
    else:
        match = re.search(
        r"churn ratio\s+([0-9.]+)\s+exceeds threshold\s+([0-9.]+)",
        combined,
        )
        if match:
            ratio, threshold = match.group(1), match.group(2)
    pre_lines = "unknown"
    pre_match = re.search(
        r"(?:^|[.\n]\s*)(?:Pre lines|pre_line_count):\s*(\d+)",
        combined,
        re.MULTILINE,
    )
    if pre_match:
        pre_lines = pre_match.group(1)
    signature = (f"ratio={ratio}", f"pre_lines={pre_lines}")
    directive = (
        "Test churn repair required.\n"
        "- Keep the existing broad test coverage and avoid unrelated rewrites.\n"
        f"- Reduce churn below threshold {threshold}; current churn is {ratio}.\n"
        "- Add or update only tests needed for the prompt change."
    )
    return directive, signature


def _public_surface_repair_advice(
    has_declared: bool,
    has_non_declared: bool,
) -> List[str]:
    """Repair-advice lines for a public-surface hard-failure block.

    A declared ``<pdd-interface>`` violation is fixed by editing the declaration —
    ``BREAKING-CHANGE: change signature`` relaxes only the un-declarable
    binding-kind/async for declared symbols, NOT their parameters, so advising the
    marker for a declared-param mismatch loops the user back into the dead-end
    #1900 removes (codex round-7 finding 3). Undeclared / removed violations keep
    the BREAKING-CHANGE guidance.
    """
    lines: List[str] = []
    if has_declared:
        lines += [
            "For a declared `<pdd-interface>` symbol, update the prompt's",
            "`<pdd-interface>` declaration to the intended signature (the",
            "declaration is the contract), or restore the declared signature",
            "shown above.",
        ]
    if has_non_declared or not has_declared:
        lines += [
            "To allow this surface change, add a `BREAKING-CHANGE:` directive to",
            "the prompt body. Example: `BREAKING-CHANGE: remove <symbol>` (or",
            "`rename`, `change signature`).",
        ]
    return lines


def build_public_surface_hard_failure_from_error(
    exc: Any,
    basename: str,
) -> str:
    """Format a structured public-surface hard-failure block."""
    removed = list(getattr(exc, "removed_symbols", []) or [])
    changed = list(getattr(exc, "changed_signatures", []) or [])
    details = list(getattr(exc, "signature_details", []) or [])
    declared_changed = {d[0] for d in details if len(d) >= 4 and d[3] == "pdd-interface"}
    has_declared = bool(declared_changed)
    has_non_declared = bool(removed) or bool(set(changed) - declared_changed)
    block_lines = [
        str(exc),
        "",
        "=== public surface regression ===",
        f"prompt: {getattr(exc, 'prompt_name', '') or '<unknown>'}",
        f"output: {getattr(exc, 'output_path', '') or '<unknown>'}",
        "removed: " + (", ".join(removed) if removed else "<none>"),
        "signature_changed: " + (", ".join(changed) if changed else "<none>"),
        f"pre surface size: {getattr(exc, 'pre_surface_size', '<unknown>')}",
        f"post surface size: {getattr(exc, 'post_surface_size', '<unknown>')}",
        "",
        *_public_surface_repair_advice(has_declared, has_non_declared),
        "",
        f"Reproduce locally: pdd sync {basename}",
        "",
        _env_fingerprint(),
    ]
    return "\n".join(block_lines)


def build_test_churn_hard_failure_from_error(
    exc: Any,
    basename: str,
) -> str:
    """Format a structured test-churn hard-failure block."""
    block_lines = [
        str(exc),
        "",
        "=== test churn threshold exceeded ===",
        f"prompt: {getattr(exc, 'prompt_name', '') or '<unknown>'}",
        f"output: {getattr(exc, 'output_path', '') or '<unknown>'}",
        f"churn ratio: {getattr(exc, 'churn_ratio', '<unknown>')}",
        f"threshold: {getattr(exc, 'threshold', '<unknown>')}",
        f"pre lines: {getattr(exc, 'pre_line_count', '<unknown>')}",
        f"post lines: {getattr(exc, 'post_line_count', '<unknown>')}",
        # Issue #1903 §B.4 provenance — whether this test was ADOPTED from an
        # existing human co-located test (unpinned). The issue-driven never-block
        # requires it to be true (in addition to the in-repo co-located
        # classifier + issue scope).
        f"adopted: {str(bool(getattr(exc, 'adopted_human', False))).lower()}",
        "",
        "To allow this rewrite, add a `BREAKING-CHANGE: rewrite tests`",
        "directive to the prompt body.",
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
# Per-module context resolution (issue #1675)
# ---------------------------------------------------------------------------


class SyncContextResolutionError(RuntimeError):
    """A requested ``--context`` is invalid for a module's own cwd.

    Raised when the global ``--context`` does not exist in the ``.pddrc`` that
    governs the module's resolved cwd and no per-module context can be resolved
    for the target. Surfacing this before spawning the child sync turns a later,
    opaque child-process ``Unknown context`` failure into an actionable
    resolver error.
    """


class _ModuleContextDecision(NamedTuple):
    """Resolved ``--context`` decision for a single module.

    ``status`` is one of:
      * ``"omitted"`` — no global context requested; let the child resolve from
        its own cwd (legacy behavior).
      * ``"ok"`` — forward the requested context unchanged (valid for the cwd,
        or no governing ``.pddrc`` to validate against).
      * ``"substituted"`` — the requested context is not defined for this cwd,
        so the cwd's own context for the target is used instead.
      * ``"unresolved"`` — the requested context is invalid for the cwd and no
        per-module context resolves; the caller must fail early.
    """

    context: Optional[str]
    status: str
    requested: Optional[str] = None
    cwd: Optional[Path] = None
    available: Tuple[str, ...] = ()
    target: Optional[str] = None


def _detect_context_for_cwd(target: str, cwd: Path) -> Optional[str]:
    """Return the context the ``.pddrc`` governing ``cwd`` assigns to ``target``.

    Mirrors the child's own resolution: find the nearest ``.pddrc`` from ``cwd``
    and match ``target`` against its contexts. Returns ``None`` when no
    ``.pddrc`` is found, it cannot be parsed, or no context matches.
    """
    pddrc = _find_pddrc_file(cwd)
    if pddrc is None:
        return None
    try:
        config = _load_pddrc_config(pddrc)
        return _detect_context_from_basename(target, config, pddrc_path=pddrc)
    except Exception:
        return None


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
        module_contexts: Optional[Dict[str, Optional[str]]] = None,
        module_units: Optional[Dict[str, ResolvedSyncUnit]] = None,
        initial_cost: float = 0.0,
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
        # Secret per-run nonce for the trusted churn-provenance channel (issue
        # #1903 §B.4 review round 8): handed to each child sync over a
        # non-inherited pipe FD and required back in any churn block the
        # never-block trusts, so untrusted project-test stdout cannot forge the
        # adoption provenance / output path that downgrades a hard-fail.
        self._churn_nonce: str = secrets.token_hex(16)
        project_hint = github_info.get("cwd") if isinstance(github_info, dict) else None
        self.project_root: Path = Path(project_hint or Path.cwd()).resolve()
        self._issue_protected_base_sha = str(
            self.sync_options.get("protected_base_ref") or ""
        ).strip() or None
        self.module_cwds: Dict[str, Any] = dict(module_cwds or {})
        self.module_targets: Dict[str, str] = dict(module_targets or {})
        # Per-module context resolved against each module's own .pddrc (issue
        # #1675). Mirrors module_cwds/module_targets; the runner never forwards
        # a context that is invalid for the cwd the child will run in.
        self.module_contexts: Dict[str, Optional[str]] = dict(module_contexts or {})
        # Canonical per-module identity (issue #1675). When a unit exists for a
        # key it is the single source of truth for cwd / target / context; the
        # module_cwds/targets/contexts dicts are a fallback for callers that pass
        # no units (ad-hoc callers, unit tests).
        self.module_units: Dict[str, ResolvedSyncUnit] = dict(module_units or {})
        self.initial_cost = float(initial_cost or 0.0)
        self._steer_state: Dict[str, Any] = {}

        self.total_budget = self.sync_options.get("total_budget")
        self.max_workers = (
            1 if self.total_budget is not None else _read_sync_max_workers()
        )

        self.module_states: Dict[str, ModuleState] = {
            b: ModuleState() for b in self.basenames
        }
        # SCC membership is built over the subgraph induced by `basenames` so
        # external deps don't pull non-target nodes into a cycle.
        basename_set = set(self.basenames)
        subgraph = {
            b: [d for d in self.dep_graph.get(b, []) if d in basename_set]
            for b in self.basenames
        }
        self._scc_of: Dict[str, frozenset] = {}
        # SCCs that participate in a real cycle (size > 1, or a 1-node SCC
        # with a self-loop). A trivial SCC (single node, no self-loop) is NOT
        # here, so soft-edge logic only applies to actual cycle members.
        self._cyclic_sccs: set = set()
        for scc in compute_sccs(subgraph):
            scc_set = frozenset(scc)
            is_cyclic = len(scc) > 1 or any(
                m in subgraph.get(m, []) for m in scc
            )
            for m in scc:
                if m in basename_set:
                    self._scc_of[m] = scc_set
            if is_cyclic:
                self._cyclic_sccs.add(scc_set)
        self.failed: bool = False
        self.budget_exhausted: bool = False
        self.comment_id: Optional[int] = None
        self.lock = threading.Lock()
        # Serializes the ENTIRE snapshot->serialize->os.replace of _save_state
        # (round 9) so a stale save cannot finish AFTER a newer one and overwrite
        # it (which could resurrect a module as pending or drop its needs-review
        # note on resume). Distinct from self.lock, which only guards the snapshot.
        self._save_lock = threading.Lock()

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
                # Issue #1903 §B.4: restore the needs-review flag so a resumed
                # run still surfaces it in the progress comment / final summary.
                review_note = info.get("needs_review")
                if isinstance(review_note, str) and review_note:
                    state.needs_review = review_note
                if basename not in self._resumed_modules:
                    self._resumed_modules.append(basename)

        cid = saved.get("comment_id")
        if cid is not None:
            try:
                self.comment_id = int(cid)
            except (TypeError, ValueError):
                pass

    def _save_state(self) -> None:
        """Atomically persist current state to disk.

        The whole snapshot->write->replace runs under ``self._save_lock`` (round
        9) so concurrent saves are fully serialized: the save that acquires the
        lock LAST both snapshots and writes last, so an earlier stale save can
        never land on top of a newer one (which could drop a needs-review note or
        resurrect a module as pending on resume).
        """
        if not self.issue_url:
            return

        state_path = self._state_file_path()
        try:
            state_path.parent.mkdir(parents=True, exist_ok=True)
        except OSError:
            return

        with self._save_lock:
            self._write_state_locked(state_path)

    def _write_state_locked(self, state_path: Path) -> None:
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
                    # Issue #1903 §B.4: persist so a durable resume does not drop
                    # the "needs review" flag for an already-synced module (the
                    # PR shipped with an adopted test left for review).
                    "needs_review": state.needs_review,
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
        """Pending modules whose deps are all satisfied.

        For modules participating in a cyclic SCC (size > 1, or 1-node with
        a self-loop), intra-SCC dep edges are treated as **soft** — only a
        failed peer blocks readiness — and the union of cross-SCC deps over
        ALL members of the SCC must be satisfied before any member can
        start. Otherwise an SCC could begin work while a transitive
        dependency reached through a cycle peer was still pending or
        failed, weakening dependency ordering. Cycle execution is
        serialized: at most one member of a cyclic SCC may be running or
        scheduled per pass.

        Cross-SCC dep edges remain hard ordering constraints, and a consumer
        outside the SCC must wait until every member of the dep's SCC has
        succeeded.
        """
        ready: List[str] = []
        with self.lock:
            # SCCs that already have a running member -> peers must wait.
            running_cyclic_sccs: set = set()
            for b in self.basenames:
                if self.module_states[b].status == "running":
                    own = self._scc_of.get(b)
                    if own is not None and own in self._cyclic_sccs:
                        running_cyclic_sccs.add(own)

            # SCCs that already had a member picked in THIS pass -> only one
            # ready slot per SCC per pass (serialize cycle execution).
            picked_cyclic_sccs: set = set()
            for basename in self.basenames:
                state = self.module_states[basename]
                if state.status != "pending":
                    continue
                own = self._scc_of.get(basename)
                in_cycle = own is not None and own in self._cyclic_sccs
                if in_cycle:
                    if own in running_cyclic_sccs or own in picked_cyclic_sccs:
                        continue

                # For a cycle member, the SCC's effective dependencies are
                # the union of every member's cross-SCC deps; intra-SCC
                # edges are soft. For non-cycle members, just walk the
                # module's own deps.
                if in_cycle:
                    members_to_walk = list(own)
                else:
                    members_to_walk = [basename]

                deps_ok = True
                for member in members_to_walk:
                    if not deps_ok:
                        break
                    for d in self.dep_graph.get(member, []):
                        dep_state = self.module_states.get(d)
                        if dep_state is None:
                            # Out-of-target deps assumed already synced
                            continue
                        # Intra-SCC edges (including a self-loop) are soft
                        # when the SCC is cyclic; only a failed peer blocks
                        # readiness.
                        intra_scc = in_cycle and d in own
                        if intra_scc:
                            if dep_state.status == "failed":
                                deps_ok = False
                                break
                            continue
                        # Cross-SCC edge: depend on the WHOLE upstream SCC.
                        dep_scc = self._scc_of.get(d)
                        if dep_scc is None or dep_scc is own:
                            if dep_state.status != "success":
                                deps_ok = False
                                break
                        else:
                            all_success = True
                            for peer in dep_scc:
                                peer_state = self.module_states.get(peer)
                                if peer_state is None or peer_state.status != "success":
                                    all_success = False
                                    break
                            if not all_success:
                                deps_ok = False
                                break
                if deps_ok:
                    ready.append(basename)
                    if in_cycle:
                        picked_cyclic_sccs.add(own)
        return ready

    def _get_blocked_modules(self) -> List[str]:
        """Pending modules transitively blocked by a failed dep.

        Operates on the SCC condensation (which is a DAG) so blocked-status
        propagation through a cycle is sound regardless of which member is
        visited first. A per-module DFS with a "visiting" set would wrongly
        cache ``False`` on cycle re-entry before knowing whether the
        parent's later deps would fail the chain.
        """
        blocked: List[str] = []
        with self.lock:
            scc_blocked_cache: Dict[frozenset, bool] = {}

            def scc_is_blocked(scc: frozenset, visiting: set) -> bool:
                cached = scc_blocked_cache.get(scc)
                if cached is not None:
                    return cached
                # The condensation is acyclic, so this guard should never
                # trigger; keep it for safety.
                if scc in visiting:
                    return False
                visiting.add(scc)
                try:
                    # Any member of this SCC itself failed?
                    for m in scc:
                        st = self.module_states.get(m)
                        if st is not None and st.status == "failed":
                            scc_blocked_cache[scc] = True
                            return True
                    # Any cross-SCC dep is failed, or its SCC is blocked?
                    for m in scc:
                        for dep in self.dep_graph.get(m, []):
                            dep_state = self.module_states.get(dep)
                            if dep_state is None:
                                # Out-of-target dep -> treated as synced.
                                continue
                            dep_scc = self._scc_of.get(dep)
                            if dep_scc is None or dep_scc == scc:
                                continue
                            # Direct failure of the dep
                            if dep_state.status == "failed":
                                scc_blocked_cache[scc] = True
                                return True
                            # Dep's SCC may have a failed peer (cycle), or be
                            # transitively blocked, regardless of the named
                            # dep's current status. Always recurse to walk the
                            # condensation DAG correctly.
                            if scc_is_blocked(dep_scc, visiting):
                                scc_blocked_cache[scc] = True
                                return True
                finally:
                    visiting.discard(scc)
                scc_blocked_cache[scc] = False
                return False

            for basename in self.basenames:
                state = self.module_states[basename]
                if state.status != "pending":
                    continue
                own_scc = self._scc_of.get(basename)
                if own_scc is None:
                    # Treat as a trivial 1-element SCC of just this basename.
                    own_scc = frozenset({basename})
                if scc_is_blocked(own_scc, set()):
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

    def _merge_steer_metadata_into_github_info(self) -> None:
        """Attach steer UX fields from sync drain and interrupt context."""
        if not self.github_info:
            return
        for key, value in peek_agentic_progress_steer_metadata().items():
            self.github_info[key] = value
        pending = self.github_info.get("pending_steers")
        preview = self.github_info.get("steer_preview")
        if pending:
            return
        if self._steer_state.get("_last_drained_count"):
            self.github_info["pending_steers"] = self._steer_state["_last_drained_count"]
            self.github_info["steer_preview"] = self._steer_state.get(
                "_last_drained_preview", ""
            )

    def _steer_sync_cwd(self) -> Path:
        if self.github_info and self.github_info.get("cwd"):
            return Path(self.github_info["cwd"])
        return self.project_root

    def _seed_sync_steer_cursor(self) -> None:
        if not self.github_info:
            return
        owner = self.github_info.get("owner")
        repo = self.github_info.get("repo")
        issue_number = self.github_info.get("issue_number")
        if not (owner and repo and issue_number is not None):
            return
        ensure_issue_steer_cursor_seeded(
            owner,
            repo,
            int(issue_number),
            self._steer_state,
            cwd=self._steer_sync_cwd(),
            quiet=self.quiet,
        )

    def _drain_sync_steers_for_progress(self) -> None:
        """Drain issue comments at a module boundary for progress comment UX (#1324 §7)."""
        if not self.github_info:
            return
        owner = self.github_info.get("owner")
        repo = self.github_info.get("repo")
        issue_number = self.github_info.get("issue_number")
        if not (owner and repo and issue_number is not None):
            return
        steers = drain_step_steers(
            owner,
            repo,
            int(issue_number),
            self._steer_state,
            cwd=self._steer_sync_cwd(),
            quiet=self.quiet,
        )
        if steers:
            preview = ", ".join(f"@{entry.author}" for entry in steers[:3])
            suffix = f" (+{len(steers) - 3} more)" if len(steers) > 3 else ""
            self._steer_state["_last_drained_count"] = len(steers)
            self._steer_state["_last_drained_preview"] = preview + suffix
            if self.github_info is not None:
                self.github_info["pending_steers"] = len(steers)
                self.github_info["steer_preview"] = preview + suffix
        else:
            self._steer_state.pop("_last_drained_count", None)
            self._steer_state.pop("_last_drained_preview", None)

    def _update_github_comment(self, status_label: Optional[str] = None) -> None:
        """Create or update a GitHub issue comment with current progress."""
        if not self.github_info:
            return

        self._merge_steer_metadata_into_github_info()

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
        ]
        pending_steers = (
            self.github_info.get("pending_steers") if self.github_info else None
        )
        steer_preview = (
            self.github_info.get("steer_preview") if self.github_info else None
        )
        if pending_steers:
            detail = steer_preview or f"{pending_steers} comment(s)"
            lines.append(f"**Mid-run feedback:** {detail} pending at next step boundary.")
            lines.append("")
        lines.extend([
            "| Module | Status | Phase | Duration | Cost |",
            "|--------|--------|-------|----------|------|",
        ])

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
                    needs_review=s.needs_review,
                )
                for b, s in self.module_states.items()
            }

        for basename in self.basenames:
            state = states_snapshot[basename]
            total_cost += state.cost

            if state.status == "success":
                status_str = "Success (needs review)" if state.needs_review else "Success"
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

        # Issue #1903 §B.4: surface any adopted tests kept and flagged for
        # review (the workflow shipped the PR instead of hard-failing).
        needs_review_notes = [
            states_snapshot[b].needs_review
            for b in self.basenames
            if states_snapshot[b].needs_review
        ]
        if needs_review_notes:
            lines.append("")
            lines.append("### ⚠️ Needs review")
            for review_note in needs_review_notes:
                lines.append(f"- {review_note}")

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
        if not self.basenames:
            return True, "No modules to sync", self.initial_cost

        if self._resumed_modules and not self.quiet:
            resumed = sorted(self._resumed_modules)
            console.print(
                f"[green]Resuming: skipping {len(resumed)} already-succeeded "
                f"module(s): {resumed}[/green]"
            )

        self._seed_sync_steer_cursor()
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
                    self._drain_sync_steers_for_progress()
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
        # Issue #1903 §B.4: modules whose adopted test could not be reconciled
        # still succeeded (PR ships), but name them so the caller/report can
        # relay the "needs review" flag rather than claiming a clean sync.
        needs_review = [
            b for b in succeeded if self.module_states[b].needs_review
        ]
        summary = f"All {len(succeeded)} modules synced successfully"
        if needs_review:
            summary += (
                f" (needs review: {needs_review} — an adopted test was kept "
                "unchanged and flagged; see PR body)"
            )
        return (True, summary, total_cost)

    # ------------------------------------------------------------------
    # Subprocess execution
    # ------------------------------------------------------------------
    def _unit_for(self, basename: str) -> Optional[ResolvedSyncUnit]:
        """Return the canonical ResolvedSyncUnit for a key, if one was provided."""
        return self.module_units.get(basename)

    def _module_cwd_path(self, basename: str) -> Path:
        """Return the resolved cwd the child sync for `basename` will run in.

        A canonical unit (when present) is the source of truth; otherwise fall
        back to the module_cwds dict / project_root.
        """
        unit = self._unit_for(basename)
        if unit is not None:
            return Path(unit.cwd)
        return Path(self.module_cwds.get(basename, str(self.project_root)))

    def _module_target(self, basename: str) -> str:
        """Return the actual `pdd sync` target for a scheduler key."""
        unit = self._unit_for(basename)
        if unit is not None:
            return unit.target_basename
        return self.module_targets.get(basename, basename)

    def _compute_module_context(self, basename: str) -> _ModuleContextDecision:
        """Decide which ``--context`` (if any) to pass to this module's child.

        The child runs in this module's own cwd (``module_cwds``), which may be a
        nested project with its own ``.pddrc``. A global ``--context`` is only
        valid when that ``.pddrc`` defines it; forwarding a parent/root context
        into a nested cwd (or vice versa) makes the child die with
        ``Unknown context`` (issue #1675).

        When a canonical :class:`ResolvedSyncUnit` exists for the key, its
        already-resolved context is authoritative (resolved with the
        omit-not-fail policy — a nested project that only has a default context
        omits ``--context`` rather than failing). Without a unit, behavior is a
        no-op for every case that works today: when no context is requested, when
        the runner has no resolved cwd for the module, when no ``.pddrc`` governs
        the cwd, or when the requested context is valid there, the requested
        value is forwarded unchanged. Resolution only intervenes when a requested
        context is invalid for the module's own cwd — exactly the leak this fixes.
        """
        unit = self._unit_for(basename)
        if unit is not None:
            return _ModuleContextDecision(
                context=unit.context,
                status="unit",
                requested=(
                    str(self.sync_options["context"])
                    if self.sync_options.get("context")
                    else None
                ),
                cwd=Path(unit.cwd),
                target=unit.target_basename,
            )

        requested = self.sync_options.get("context")
        requested = str(requested) if requested else None
        if not requested:
            return _ModuleContextDecision(context=None, status="omitted")

        # Only modules the orchestrator placed in a specific cwd get cwd-aware
        # resolution. Directly-constructed runners (ad-hoc callers, unit tests)
        # keep legacy forwarding.
        if basename not in self.module_cwds:
            return _ModuleContextDecision(
                context=requested, status="ok", requested=requested
            )

        cwd = self._module_cwd_path(basename)
        pddrc = _find_pddrc_file(cwd)
        if pddrc is None:
            # No .pddrc governs this cwd — nothing to validate against; preserve
            # legacy behavior and forward the requested context unchanged.
            return _ModuleContextDecision(
                context=requested, status="ok", requested=requested, cwd=cwd
            )
        try:
            config = _load_pddrc_config(pddrc)
            available = tuple((config.get("contexts") or {}).keys())
        except Exception:
            # Malformed .pddrc: do not second-guess it here; forward as-is and
            # let the child surface the parse error.
            return _ModuleContextDecision(
                context=requested, status="ok", requested=requested, cwd=cwd
            )

        if requested in available:
            return _ModuleContextDecision(
                context=requested,
                status="ok",
                requested=requested,
                cwd=cwd,
                available=available,
            )

        # Requested context is not defined for this cwd's .pddrc (the leak).
        # Resolve the context the cwd's own .pddrc assigns to this target.
        target = self.module_targets.get(basename, basename)
        resolved = self.module_contexts.get(basename)
        if not resolved:
            resolved = _detect_context_for_cwd(target, cwd)
        if resolved and resolved in available:
            return _ModuleContextDecision(
                context=resolved,
                status="substituted",
                requested=requested,
                cwd=cwd,
                available=available,
                target=target,
            )

        return _ModuleContextDecision(
            context=None,
            status="unresolved",
            requested=requested,
            cwd=cwd,
            available=available,
            target=target,
        )

    @staticmethod
    def _format_context_resolution_error(
        basename: str, decision: _ModuleContextDecision
    ) -> str:
        """Build an actionable message for an unresolved context decision."""
        available = ", ".join(decision.available) if decision.available else "<none>"
        cwd = decision.cwd if decision.cwd is not None else "<unknown>"
        return (
            f"Requested --context '{decision.requested}' is not defined in the "
            f".pddrc governing module '{basename}' (cwd: {cwd}); available "
            f"contexts: {available}. No context in that .pddrc maps to target "
            f"'{decision.target or basename}'. Add the context to that .pddrc, "
            f"or run from the directory whose .pddrc defines it."
        )

    def _reproduce_command(self, basename: str) -> str:
        """Return a copy-pasteable reproduce-local command for `basename`.

        Includes the module's cwd and the resolved context so the printed
        command matches what the runner actually executed (issue #1675).
        """
        target = self._module_target(basename)
        try:
            context = self._compute_module_context(basename).context
        except Exception:
            context = None

        cmd = "pdd "
        if context:
            cmd += f"--context {context} "
        cmd += f"sync {target}"

        cwd = self._module_cwd_path(basename)
        rel_str = ""
        try:
            rel_str = str(cwd.resolve().relative_to(self.project_root.resolve()))
        except Exception:
            rel_str = str(cwd)
        if rel_str and rel_str != ".":
            return f"cd {rel_str} && {cmd}"
        return cmd

    def _build_command(self, basename: str, in_flight_cost: float = 0.0) -> List[str]:
        """Build the pdd sync subprocess command for a basename."""
        pdd_exe = _find_pdd_executable()
        if pdd_exe:
            cmd = [pdd_exe, "--force"]
        else:
            cmd = [sys.executable, "-m", "pdd", "--force"]

        if self.sync_options.get("local"):
            cmd.append("--local")
        decision = self._compute_module_context(basename)
        if decision.status == "unresolved":
            raise SyncContextResolutionError(
                self._format_context_resolution_error(basename, decision)
            )
        if decision.status == "substituted" and not self.quiet:
            try:
                console.print(
                    f"[yellow]Module {basename}: requested context "
                    f"'{decision.requested}' is not defined in {decision.cwd}/"
                    f".pddrc; using its own context '{decision.context}' "
                    f"instead.[/yellow]"
                )
            except Exception:
                pass
        if decision.context:
            cmd.extend(["--context", str(decision.context)])
        strength = self.sync_options.get("strength")
        if strength is not None:
            cmd.extend(["--strength", str(strength)])
        temperature = self.sync_options.get("temperature")
        if temperature is not None:
            cmd.extend(["--temperature", str(temperature)])
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

        compressed_context = self.sync_options.get("compressed_context")
        if compressed_context is True:
            cmd.append("--compressed-context")
        elif compressed_context is False:
            cmd.append("--no-compressed-context")

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

        cmd.append(self._module_target(basename))
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
        if (
            self.sync_options.get("require_protected_base")
            and not self._issue_protected_base_sha
        ):
            raise RuntimeError("issue-driven sync cannot establish protected ownership base")
        if self._issue_protected_base_sha:
            env["PDD_PROTECTED_BASE_REF"] = self._issue_protected_base_sha
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
        last_signature: Optional[Tuple[str, ...]] = None
        last_failure_kind: Optional[str] = None
        last_error = ""
        last_stdout = ""
        last_stderr = ""
        repair_directive: Optional[str] = None

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
                output_review_note = _extract_test_output_needs_review(stdout)
                if output_review_note:
                    self._register_test_output_needs_review(
                        basename, output_review_note
                    )
                return True, total_cost, ""

            prose_output = _parse_prose_output_failure(stdout, stderr)
            conformance = _parse_conformance_failure(stdout, stderr)
            public_surface = _parse_public_surface_failure(stdout, stderr)
            test_churn = _parse_test_churn_failure(stdout, stderr)
            failure_kind = "architecture"
            parsed_failure = prose_output
            if parsed_failure is not None:
                failure_kind = "prose_output"
            if parsed_failure is None and conformance is not None:
                parsed_failure = conformance
            if parsed_failure is None and public_surface is not None:
                failure_kind = "public_surface"
                parsed_failure = public_surface
            if parsed_failure is None and test_churn is not None:
                failure_kind = "test_churn"
                parsed_failure = test_churn

            if parsed_failure is None:
                # Not a conformance failure: do not retry
                return False, total_cost, error

            new_directive, new_signature = parsed_failure
            if (
                last_signature is not None
                and new_signature == last_signature
                and failure_kind == last_failure_kind
            ):
                # Stuck on identical symbol set — abort and emit hard-failure block
                break
            last_signature = new_signature
            last_failure_kind = failure_kind
            repair_directive = new_directive

            if attempt + 1 >= MAX_CONFORMANCE_ATTEMPTS:
                break
            if failure_kind == "prose_output" and attempt >= 1:
                break
            if failure_kind == "test_churn" and attempt >= 1:
                break
            remaining_budget = self._remaining_total_budget(total_cost)
            if remaining_budget is not None and remaining_budget <= 0.0:
                failure_label = (
                    "architecture conformance"
                    if failure_kind == "architecture"
                    else failure_kind
                )
                last_error = (
                    f"Budget exhausted during {failure_label} repair "
                    f"(${total_cost:.2f} spent in {basename})."
                )
                break

        # Hard-failure path: include structured conformance block
        if last_failure_kind == "prose_output":
            hard_block = self._build_prose_output_hard_failure(
                basename, last_error, last_stdout, last_stderr
            )
        elif last_failure_kind == "public_surface":
            hard_block = self._build_public_surface_hard_failure(
                basename, last_error, last_stdout, last_stderr
            )
        elif last_failure_kind == "test_churn":
            # Issue #1903 §B.4 — never block the issue-driven workflow on an
            # unreconcilable ADOPTED co-located test. Reaching here means: the
            # child sync already RESTORED the pre-existing test to disk before
            # re-raising, AND one-session's #2208 coverage-preserving auto-accept
            # already REFUSED (so this is the coverage-losing case the strict gate
            # would otherwise hard-fail). Per #1903 the command must still open the
            # working PR and flag that one test "needs review" rather than hand
            # work back to the user — but ONLY when the churned test is a
            # human-authored co-located test PDD adopted. A PDD-owned ``tests/``
            # shadow that is NOT proven adopted keeps the strict hard-fail so
            # coverage loss there is never silently swallowed. (Standalone
            # `pdd sync <module>` / `pdd test`, which do not run through this
            # issue-driven runner, always keep the strict hard-fail.)
            # Round 8: gate BOTH the path and the adoption provenance on the
            # per-run secret nonce, so only a genuinely PDD-emitted churn block
            # (which echoed the nonce it read over the private FD) can drive the
            # never-block. A block a hostile project test printed to stdout lacks
            # the nonce and is ignored -> strict hard-fail.
            churned_test_path = _extract_test_churn_output_path(
                last_stdout, last_stderr, expected_nonce=self._churn_nonce
            )
            churn_was_adopted = _extract_test_churn_adopted(
                last_stdout, last_stderr, expected_nonce=self._churn_nonce
            )
            # THREE guards, ALL required, so the relief never escapes its scope:
            #   (1) issue-driven workflow only — ``self.issue_url`` is set only
            #       when this runner backs a GitHub issue → PR sync (agentic_sync
            #       / durable_sync_runner). Project-wide ``pdd sync`` builds this
            #       runner with ``issue_url=None`` and opens NO PR, so it must
            #       keep the strict hard-fail (there is no PR to flag "needs
            #       review" against — relaxing it there would silently bypass the
            #       gate).
            #   (2) structured adoption provenance — the child stamped
            #       ``adopted: true`` because the churned test was ADOPTED from an
            #       existing human co-located test (unpinned), decided at path
            #       resolution BEFORE generation (``_extract_test_churn_adopted``).
            #       A user-pinned path, a greenfield test PDD created, or an older
            #       child (no marker) reads False -> strict hard-fail.
            #   (3) in-repo co-located shape — the path is a co-located test
            #       inside the worktree, not a ``tests/`` shadow or traversal
            #       (see ``_is_adopted_collocated_test_path``).
            if (
                self.issue_url
                and churn_was_adopted
                and _is_adopted_collocated_test_path(
                    churned_test_path, project_root=self.project_root
                )
            ):
                note = self._register_test_churn_needs_review(
                    basename, churned_test_path
                )
                if not self.quiet:
                    console.print(f"[yellow]{note}[/yellow]")
                return True, total_cost, ""
            hard_block = self._build_test_churn_hard_failure(
                basename, last_error, last_stdout, last_stderr
            )
        else:
            hard_block = self._build_conformance_hard_failure(
                basename, last_error, last_stdout, last_stderr
            )
        return False, total_cost, hard_block

    def _register_test_churn_needs_review(
        self, basename: str, test_path: Optional[str]
    ) -> str:
        """Flag an unreconcilable adopted test for review instead of failing (#1903).

        The child sync already restored the human-authored test to disk before
        re-raising the churn error; the issue workflow opens the PR with the test
        flagged for review. ``test_path`` is the adopted co-located test resolved
        by the caller (already classified via ``_is_adopted_collocated_test_path``).
        Records the note on the module state (surfaced in the progress comment /
        PR thread), emits a machine-readable marker to stdout, and returns the
        operator-facing note.
        """
        kept = test_path or "the adopted test"
        note = (
            f"`{basename}`: test churn could not be reconciled after bounded "
            f"repair — kept the existing test (`{kept}`) unchanged and "
            f"flagged it for review (issue #1903); the PR still ships."
        )
        print(f"{_TEST_CHURN_NEEDS_REVIEW_MARKER}: {kept}", flush=True)
        with self.lock:
            state = self.module_states.get(basename)
            if state is not None:
                state.needs_review = note
        return note

    def _register_test_output_needs_review(self, basename: str, note: str) -> str:
        """Persist an opaque-runner non-write decision on module state (#1903)."""
        rendered = f"`{basename}`: {note}"
        with self.lock:
            state = self.module_states.get(basename)
            if state is not None:
                state.needs_review = rendered
        return rendered

    def _build_prose_output_hard_failure(
        self,
        basename: str,
        failure_summary: str,
        stdout: str,
        stderr: str,
    ) -> str:
        """Build the structured prose-output hard-failure error string."""
        combined = (stdout or "") + "\n" + (stderr or "")

        prompt_field = "<unknown>"
        for line in combined.splitlines():
            if _PROSE_OUTPUT_PREFIX in line:
                tail = line.split(_PROSE_OUTPUT_PREFIX, 1)[1].strip()
                prompt_field = tail.split(":", 1)[0].strip() if ":" in tail else tail
                break

        def _extract_line_field(label: str, default: str = "<unknown>") -> str:
            line_match = re.search(
                rf"^{re.escape(label)}:\s*(.+)$",
                combined,
                re.MULTILINE | re.IGNORECASE,
            )
            if line_match:
                return line_match.group(1).strip() or default
            return default

        return "\n".join(
            [
                failure_summary or "Generation output extraction failure",
                "",
                "=== generation output extraction failure ===",
                f"prompt: {prompt_field}",
                f"output: {_extract_line_field('output')}",
                f"language: {_extract_line_field('language')}",
                f"model: {_extract_line_field('model_name')}",
                f"extractor_result: {_extract_line_field('Extractor result')}",
                f"raw_output_excerpt: {_extract_line_field('Raw output excerpt')}",
                (
                    "note: The model returned no extractable code. Check that "
                    "the provider/model is configured to return complete source "
                    "files, not planning text or agentic responses."
                ),
                "",
                f"Reproduce locally: {self._reproduce_command(basename)}",
                "",
                _env_fingerprint(),
            ]
        )

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
            f"Reproduce locally: {self._reproduce_command(basename)}",
            "",
            _env_fingerprint(),
        ]
        return "\n".join(block_lines)

    def _build_public_surface_hard_failure(
        self,
        basename: str,
        failure_summary: str,
        stdout: str,
        stderr: str,
    ) -> str:
        """Build the structured public-surface hard-failure error string."""
        parsed = _parse_public_surface_failure_fields(stdout, stderr)
        removed = parsed[1] if parsed else tuple()
        changed = parsed[2] if parsed else tuple()
        details = parsed[3] if parsed else tuple()
        combined = (stdout or "") + "\n" + (stderr or "")

        prompt_field = "<unknown>"
        for line in combined.splitlines():
            if _PUBLIC_SURFACE_PREFIX in line:
                tail = line.split(_PUBLIC_SURFACE_PREFIX, 1)[1].strip()
                prompt_field = tail.split(":", 1)[0].strip() if ":" in tail else tail
                break

        field_boundary = (
            r"(?=\.\s+(?:Output|Pre surface size|Post surface size)\b"
            r"|\.\s*$|\n|$)"
        )

        def _extract_field(label: str, default: str = "<unknown>") -> str:
            normalized = label.lower().replace(" ", "_")
            aliases = {
                "pre_lines": ("pre_lines", "pre_line_count"),
                "post_lines": ("post_lines", "post_line_count"),
            }.get(normalized, (normalized,))
            for alias in aliases:
                line_match = re.search(
                    rf"^{re.escape(alias)}:\s*(.+)$",
                    combined,
                    re.MULTILINE,
                )
                if line_match:
                    return line_match.group(1).strip() or default
            pattern = re.compile(
                rf"{re.escape(label)}:\s*(.*?){field_boundary}",
                re.DOTALL,
            )
            match = pattern.search(combined)
            if not match:
                return default
            return match.group(1).strip().rstrip(".").strip() or default

        block_lines = [
            failure_summary or "Public surface regression",
            "",
            "=== public surface regression ===",
            f"prompt: {prompt_field}",
            f"output: {_extract_field('Output')}",
            "removed: " + (", ".join(removed) if removed else "<none>"),
            "signature_changed: "
            + (", ".join(changed) if changed else "<none>"),
            f"pre surface size: {_extract_field('Pre surface size')}",
            f"post surface size: {_extract_field('Post surface size')}",
        ]
        # Carry the full expected-vs-actual contract for each declared signature
        # mismatch so criterion 4 (no truncation) holds on the agentic path too
        # (issue #1900). Byte-identical JSON to the ``signature_detail:`` message
        # line emitted by ``PublicSurfaceRegressionError`` (codex round-8 #2).
        for symbol, expected_entry, actual_entry, source in details:
            block_lines.append(
                "signature_detail: "
                + json.dumps(
                    {
                        "symbol": symbol,
                        "expected": expected_entry,
                        "actual": actual_entry,
                        "source": source,
                    }
                )
            )
        declared_changed = {
            d[0] for d in details if len(d) >= 4 and d[3] == "pdd-interface"
        }
        has_declared = bool(declared_changed)
        has_non_declared = bool(removed) or bool(set(changed) - declared_changed)
        block_lines.append("")
        block_lines.extend(
            _public_surface_repair_advice(has_declared, has_non_declared)
        )
        block_lines.extend(
            [
                "",
                f"Reproduce locally: {self._reproduce_command(basename)}",
                "",
                _env_fingerprint(),
            ]
        )
        return "\n".join(block_lines)

    def _build_test_churn_hard_failure(
        self,
        basename: str,
        failure_summary: str,
        stdout: str,
        stderr: str,
    ) -> str:
        """Build the structured test-churn hard-failure error string."""
        combined = (stdout or "") + "\n" + (stderr or "")

        prompt_field = "<unknown>"
        for line in combined.splitlines():
            if _TEST_CHURN_PREFIX in line:
                tail = line.split(_TEST_CHURN_PREFIX, 1)[1].strip()
                prompt_field = tail.split(":", 1)[0].strip() if ":" in tail else tail
                break

        field_boundary = r"(?=\.\s+(?:Output|Pre lines|Post lines)\b|\.\s*$|\n|$)"

        def _extract_field(label: str, default: str = "<unknown>") -> str:
            normalized = label.lower().replace(" ", "_")
            aliases = {
                "pre_lines": ("pre_lines", "pre_line_count"),
                "post_lines": ("post_lines", "post_line_count"),
            }.get(normalized, (normalized,))
            for alias in aliases:
                line_match = re.search(
                    rf"^{re.escape(alias)}:\s*(.+)$",
                    combined,
                    re.MULTILINE,
                )
                if line_match:
                    return line_match.group(1).strip() or default
            pattern = re.compile(
                rf"{re.escape(label)}:\s*(.*?){field_boundary}",
                re.DOTALL,
            )
            match = pattern.search(combined)
            if not match:
                return default
            return match.group(1).strip().rstrip(".").strip() or default

        ratio = threshold = "<unknown>"
        ratio_match = re.search(r"^ratio:\s*([0-9.]+)", combined, re.MULTILINE)
        threshold_match = re.search(r"^threshold:\s*([0-9.]+)", combined, re.MULTILINE)
        if ratio_match and threshold_match:
            ratio, threshold = ratio_match.group(1), threshold_match.group(1)
        else:
            match = re.search(
                r"churn ratio\s+([0-9.]+)\s+exceeds threshold\s+([0-9.]+)",
                combined,
            )
            if match:
                ratio, threshold = match.group(1), match.group(2)

        return "\n".join(
            [
                failure_summary or "Test churn threshold exceeded",
                "",
                "=== test churn threshold exceeded ===",
                f"prompt: {prompt_field}",
                f"output: {_extract_field('Output')}",
                f"churn ratio: {ratio}",
                f"threshold: {threshold}",
                f"pre lines: {_extract_field('Pre lines')}",
                f"post lines: {_extract_field('Post lines')}",
                # Issue #1903 §B.4 provenance — preserve the child's adoption
                # stamp in the FINAL recorded block too (round-5 lockstep), so a
                # hard-failure recorded when the never-block does NOT apply still
                # carries whether the churned test was an adopted human test.
                f"adopted: {str(_extract_test_churn_adopted(stdout, stderr, expected_nonce=self._churn_nonce)).lower()}",
                "",
                "To allow this rewrite, add a `BREAKING-CHANGE: rewrite tests`",
                "directive to the prompt body.",
                "",
                f"Reproduce locally: {self._reproduce_command(basename)}",
                "",
                _env_fingerprint(),
            ]
        )

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
        try:
            cmd = self._build_command(basename, in_flight_cost=in_flight_cost)
        except SyncContextResolutionError as exc:
            # Fail this module early with an actionable resolver error instead of
            # spawning a child that would die with "Unknown context" (#1675).
            return False, 0.0, str(exc), "", ""

        cost_file = tempfile.NamedTemporaryFile(suffix=".csv", delete=False)
        cost_file.close()

        env = self._build_env(cost_file.name, repair_directive=repair_directive)

        if not self.quiet:
            try:
                console.print(f"[blue]Starting sync: {basename}[/blue]")
            except Exception:
                pass

        # Bounded tail buffers: cap retained child output so a verbose or
        # retrying child cannot grow these to tens of MB and trigger a SIGKILL.
        # Allocated fresh per attempt, so output from a previous repair-retry
        # attempt is not retained across retries in memory.
        stdout_capture = _BoundedTextCapture(
            line_limit=STDOUT_CAPTURE_LINE_LIMIT,
            byte_limit=STDOUT_CAPTURE_BYTE_LIMIT,
        )
        stderr_capture = _BoundedTextCapture(
            line_limit=STDOUT_CAPTURE_LINE_LIMIT,
            byte_limit=STDOUT_CAPTURE_BYTE_LIMIT,
        )
        verbose_print = self.verbose and not self.quiet
        line_lock = threading.Lock()

        # Sticky capture of the child's "Overall status: ... Failed" verdict.
        # Recorded as each stdout line streams in (see _process_child_line) so a
        # failure marker followed by a flood of output that evicts it from the
        # bounded tail still yields a failed verdict and a correct failure
        # reason. Only the stdout reader thread writes it, so no lock is needed.
        streamed_failure_markers: List[str] = []
        streamed_needs_review_notes: List[str] = []

        def _dropped_output_message() -> str:
            out_lines = stdout_capture.dropped_lines
            out_bytes = stdout_capture.dropped_bytes
            err_lines = stderr_capture.dropped_lines
            err_bytes = stderr_capture.dropped_bytes
            if not (out_lines or out_bytes or err_lines or err_bytes):
                return ""
            return (
                f"{basename}: bounded child output capture dropped "
                f"{out_lines} stdout line(s) / {out_bytes} stdout byte(s), "
                f"{err_lines} stderr line(s) / {err_bytes} stderr byte(s) "
                f"(kept last {STDOUT_CAPTURE_LINE_LIMIT} line(s) and "
                f"{STDOUT_CAPTURE_BYTE_LIMIT} byte(s) per stream)"
            )

        def _log_dropped_output() -> None:
            """Emit a diagnostic when bounded capture discarded child output.

            The count is logged to the runner's own stdout, never injected into
            the captured child stdout/stderr, so conformance/public-surface/
            test-churn parsing and the success scan keep seeing exactly what the
            child emitted.
            """
            msg = _dropped_output_message()
            if msg and not self.quiet:
                try:
                    print(f"  {msg}")
                except Exception:
                    pass

        def _read_stream_chunk(stream):
            try:
                return os.read(stream.fileno(), OUTPUT_CAPTURE_READ_CHUNK_SIZE)
            except Exception:
                return stream.read(OUTPUT_CAPTURE_READ_CHUNK_SIZE)

        def _process_child_line(line: str, prefix: str = "") -> None:
            stripped = line.strip()
            # Record the failure verdict on the stdout stream (prefix == "") the
            # moment it is seen, mirroring the success-scan predicate, so it is
            # not lost if later output evicts the line from the bounded tail.
            if (
                prefix == ""
                and not streamed_failure_markers
                and "Overall status:" in stripped
                and "Failed" in stripped
            ):
                streamed_failure_markers.append(stripped)
            if (
                prefix == ""
                and not streamed_needs_review_notes
                and _TEST_OUTPUT_NEEDS_REVIEW_MARKER in stripped
            ):
                note = stripped.split(
                    _TEST_OUTPUT_NEEDS_REVIEW_MARKER, 1
                )[1].lstrip(" :")
                if note:
                    streamed_needs_review_notes.append(note)
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

        def _read_stream(
            stream,
            capture: _BoundedTextCapture,
            prefix: str = "",
        ) -> None:
            decoder = codecs.getincrementaldecoder("utf-8")(errors="replace")
            try:
                while True:
                    raw_chunk = _read_stream_chunk(stream)
                    if not raw_chunk:
                        break
                    if isinstance(raw_chunk, bytes):
                        text = decoder.decode(raw_chunk)
                    else:
                        text = str(raw_chunk)
                    with line_lock:
                        lines = capture.feed(text)
                    for line in lines:
                        _process_child_line(line, prefix)
                final_text = decoder.decode(b"", final=True)
                with line_lock:
                    lines = capture.feed(final_text)
                    lines.extend(capture.finish())
                for line in lines:
                    _process_child_line(line, prefix)
            except Exception:
                pass
            finally:
                try:
                    stream.close()
                except Exception:
                    pass

        cwd_str = str(self._module_cwd_path(basename))

        # Trusted churn-provenance channel (issue #1903 §B.4 review round 8).
        # POSIX hands the child ONLY the pipe's read end via ``pass_fds``. The
        # child inherits this FD; grandchild test processes do not, so a hostile
        # project test cannot learn the nonce and forge a trusted block.
        #
        # Windows does not support ``pass_fds``.  Do not substitute an env value
        # or temp file: either would disclose the secret to hostile project tests.
        # Instead omit the channel and fail closed.  The child can still run, but
        # no churn block can authenticate and the never-block exception stays off.
        nonce_read_fd: Optional[int] = None
        popen_nonce_kwargs: Dict[str, Any] = {}
        env.pop(_CHURN_NONCE_ENV, None)
        if _CHURN_NONCE_PASS_FDS_SUPPORTED:
            nonce_read_fd, nonce_write_fd = os.pipe()
            try:
                os.write(nonce_write_fd, self._churn_nonce.encode("ascii"))
            finally:
                os.close(nonce_write_fd)
            env[_CHURN_NONCE_ENV] = str(nonce_read_fd)
            popen_nonce_kwargs["pass_fds"] = (nonce_read_fd,)

        try:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                stdin=subprocess.DEVNULL,
                cwd=cwd_str,
                env=env,
                text=False,
                bufsize=0,
                start_new_session=True,
                **popen_nonce_kwargs,
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
        finally:
            # The child holds its own inherited copy; drop the parent's so the
            # write side's EOF reaches the child and no FD leaks per attempt.
            if nonce_read_fd is not None:
                try:
                    os.close(nonce_read_fd)
                except OSError:
                    pass

        t_out = threading.Thread(
            target=_read_stream,
            args=(process.stdout, stdout_capture, ""),
            daemon=True,
        )
        t_err = threading.Thread(
            target=_read_stream,
            args=(process.stderr, stderr_capture, "err:"),
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
                                for line in stdout_capture.reversed_lines():
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
            stdout = stdout_capture.text()
            stderr = stderr_capture.text()
            _log_dropped_output()
            truncation_msg = _dropped_output_message()
            error_msg = f"Timeout after {int(effective_timeout)}s waiting for sync"
            if truncation_msg:
                error_msg = f"{error_msg}\n{truncation_msg}"
            return (
                False,
                cost,
                error_msg,
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

        stdout = stdout_capture.text()
        stderr = stderr_capture.text()
        _log_dropped_output()
        if streamed_needs_review_notes and not _extract_test_output_needs_review(
            stdout
        ):
            stdout += (
                f"\n{_TEST_OUTPUT_NEEDS_REVIEW_MARKER}: "
                f"{streamed_needs_review_notes[0]}\n"
            )

        success = exit_code == 0
        if success and (
            streamed_failure_markers
            or any(
                "Overall status:" in line and "Failed" in line
                for line in stdout.splitlines()
            )
        ):
            success = False

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
        if streamed_failure_markers:
            failure_reason = streamed_failure_markers[0]
        else:
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
        truncation_msg = _dropped_output_message()
        if truncation_msg:
            error = f"{error}\n{truncation_msg}" if error else truncation_msg
        if not self.quiet:
            try:
                console.print(
                    f"[red]  Error for {basename}:[/red] {error[:500]}"
                )
            except Exception:
                pass

        return False, cost, error, stdout, stderr
