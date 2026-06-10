"""Shared, no-LLM context-audit core.

Preprocesses a prompt the same way generation's deterministic first pass does and
reports how many tokens each source segment (prompt body, each ``<include>``,
grounding, …) adds to the hydrated payload — **without** making an LLM call,
running a shell, or fetching the web. The result is a structured
:class:`ContextAudit` so that multiple surfaces — the ``pdd context`` CLI and the
``pdd connect`` server endpoint — produce identical answers from one
implementation path instead of each re-deriving the audit (PR #1387 review #2).

Attribution is derived from the real expansion path (so include selectors are
honored) via an in-memory snapshot recorder; deferred dynamic directives
(``<shell>``, ``<web>``, semantic ``query=`` includes) are surfaced as warnings
and zero-token ``deferred`` rows rather than billed as hydrated payload. Detection
and stripping are code-span aware: dynamic/include syntax inside fenced or inline
code is literal documentation, not a directive.

This module is presentation-free and applies no budget policy: it reports facts
(``total_tokens``, ``percent_used``). Callers decide rendering and any threshold
exit behavior (see :func:`threshold_exceeded`).
"""
from __future__ import annotations

import contextlib
import io
import os
import re
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Literal, Optional, Tuple

from .path_resolution import get_default_resolver
from .preprocess import (
    _extract_code_spans,
    _intersects_any_span,
    _parse_attrs,
    compute_user_intent_paths,
    process_backtick_includes,
    process_include_tags,
    preprocess,
    process_include_many_tags,
)
from .server.token_counter import count_tokens, get_context_limit

# ``status`` classifies each row so agent/code callers never have to parse human
# warning strings to understand a row's state (PR #1387 review #4):
#   resolved    -- an include whose realized content was hydrated and counted
#   unresolved  -- a top-level include path that does not resolve to a file
#   deferred    -- nondeterministic markup (<shell>/<web>/query=, ${VAR} lists)
#   unavailable -- a known segment that requires PDD Cloud (grounding)
#   body        -- the prompt body (everything not attributed to an include)
RowStatus = Literal["resolved", "unresolved", "deferred", "unavailable", "body"]

# Grounding requires PDD Cloud; it is reported as 0 tokens with a deferred
# warning rather than triggering a network call (see issue #789 acceptance).
_GROUNDING_UNAVAILABLE_NOTE = "unavailable (requires cloud)"

# Dynamic directives are *deferred* in the deterministic pass-1 hydration the
# audit performs: their markup survives in the expanded text but the real
# content (a shell run, a web fetch, a semantic query extraction) is never
# produced. We must not bill that leftover markup as if it were the hydrated
# payload (issue #789 review #3), so it is stripped before token counting and
# surfaced as a warning instead.
# A ``<include query="...">`` is an LLM-driven semantic extraction; pass-1
# hydration defers it and the audit surfaces it as a deferred dynamic tag.
_QUERY_INCLUDE_PATTERN = re.compile(
    r"<include\b[^>]*\bquery\s*=[^>]*>.*?</include>|<include\b[^>]*\bquery\s*=[^>]*/>",
    re.IGNORECASE | re.DOTALL,
)
_DYNAMIC_MARKUP_PATTERNS = (
    re.compile(r"<shell\b[^>]*>.*?</shell>|<shell\b[^>]*/>", re.IGNORECASE | re.DOTALL),
    re.compile(r"<web\b[^>]*>.*?</web>|<web\b[^>]*/>", re.IGNORECASE | re.DOTALL),
    _QUERY_INCLUDE_PATTERN,
)
_DYNAMIC_TAG_DETECT_PATTERNS = {
    "shell": re.compile(r"<shell\b[^>]*>.*?</shell>|<shell\b[^>]*/>", re.IGNORECASE | re.DOTALL),
    "web": re.compile(r"<web\b[^>]*>.*?</web>|<web\b[^>]*/>", re.IGNORECASE | re.DOTALL),
    "query_include": _QUERY_INCLUDE_PATTERN,
}
_DYNAMIC_TAG_OPENING_PATTERNS = {
    "shell": re.compile(r"<shell(?:\s[^>]*)?>", re.IGNORECASE),
    "web": re.compile(r"<web(?:\s[^>]*)?>", re.IGNORECASE),
    "query_include": re.compile(r"<include\b[^>]*\bquery\s*=", re.IGNORECASE),
}


# Matches a whole ``<include ...>...</include>`` (or self-closing) element so its
# attributes can be parsed; used only to decide whether a directive is a
# semantic ``query=`` include that must be skipped (see below).
# Possessive `[^>]*+` with a single leading `\s` (not `\s+`) keeps the attribute
# scan linear: CodeQL py/polynomial-redos flags the `\s+[^>]*?` overlap (both can
# match whitespace), and this prompt text reaches the regex from a remote source
# via the connect /context-audit endpoint (PR #1387).
_QUERY_INCLUDE_ELEMENT_RE = re.compile(
    r"<include(?P<attrs>\s[^>]*+)?>(?P<content>.*?)</include>"
    r"|<include(?P<attrs_self>\s[^>]*?)/>",
    re.IGNORECASE | re.DOTALL,
)


@dataclass(frozen=True)
class AuditRow:
    """One attributed source segment of the hydrated prompt.

    ``percent`` is intentionally absent: it is a presentation concern derived
    against a chosen basis (see :func:`row_percent`), so the core stays
    presentation-free and callers can compute it however they display it.
    """

    source: str
    tokens: int
    status: RowStatus
    note: Optional[str] = None


@dataclass(frozen=True)
class ContextAudit:
    """Structured result of a deterministic, no-LLM context audit."""

    model: str
    total_tokens: int
    context_limit: Optional[int]
    percent_used: Optional[float]
    rows: List[AuditRow] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


def _strip_semantic_query_includes(text: str) -> str:
    """Drop ``<include query="...">`` directives that would invoke the LLM.

    ``preprocess``'s non-recursive include branch runs ``IncludeQueryExtractor``
    (a real LLM call) for a ``query=`` include unless a deterministic ``select=``
    is also present, in which case the selector is preferred and no model is
    invoked. The deterministic audit must never trigger that extraction, so
    query-only includes are removed before unresolved-include detection runs the
    real include processors; they remain visible to users through the deferred
    dynamic-tag warning. (PR #1387 review)
    """

    def _replace(match: "re.Match") -> str:
        attrs = _parse_attrs(match.group("attrs") or match.group("attrs_self") or "")
        if attrs.get("query") and not attrs.get("select"):
            return ""
        return match.group(0)

    return _QUERY_INCLUDE_ELEMENT_RE.sub(_replace, text)


class _SegmentRecorder:
    """In-memory ``snapshot_recorder`` that captures per-include attribution.

    ``preprocess(..., snapshot_recorder=self)`` calls :meth:`record_include` at
    every resolved include site with the **actual inserted content** — already
    narrowed by ``lines=`` / ``select=`` / ``mode=`` / compression and with
    nested includes expanded in place. Counting that content is what makes the
    audit match the hydrated payload instead of re-reading whole files (issue
    #789 review #1). Other ``record_*`` hooks are not invoked by deterministic
    pass-1 preprocessing; the catch-all keeps us tolerant of that surface
    without coupling to it.
    """

    def __init__(self) -> None:
        self.includes: List[Dict[str, str]] = []
        self.deferred: List[str] = []

    def record_include(
        self, *, source_path, content, query=None, output=None, **kwargs: object
    ) -> Dict:
        """Capture one include's realized content for per-source attribution."""
        # Query includes are LLM-driven and deferred in pass 1; they are handled
        # as dynamic tags, so ignore any record to avoid double-counting markup.
        if query:
            return {}
        text = output if output is not None else content
        depth = int(kwargs.get("include_depth", 0) or 0)
        self.includes.append(
            {"source": str(source_path), "content": str(text), "depth": depth}
        )
        return {}

    def __getattr__(self, _name: str):  # record_shell / record_web / etc.
        def _noop(*_args: object, **_kwargs: object) -> Dict:
            return {}

        return _noop


def _strip_dynamic_markup(text: str) -> str:
    """Remove deferred dynamic-tag markup so it is not counted as payload."""
    for pattern in _DYNAMIC_MARKUP_PATTERNS:
        text = _strip_pattern_outside_code(text, pattern)
    return text


def _strip_pattern_outside_code(text: str, pattern: "re.Pattern") -> str:
    """Strip pattern matches that do not intersect fenced/inline code spans."""
    code_spans = _extract_code_spans(text)
    parts: List[str] = []
    pos = 0
    for match in pattern.finditer(text):
        parts.append(text[pos:match.start()])
        if _intersects_any_span(match.start(), match.end(), code_spans):
            parts.append(match.group(0))
        pos = match.end()
    parts.append(text[pos:])
    return "".join(parts)


def _detect_dynamic_tags_outside_code(text: str) -> List[str]:
    """Return deferred dynamic tags, ignoring literal examples in code spans."""
    code_spans = _extract_code_spans(text)
    found: List[str] = []
    for name, pattern in _DYNAMIC_TAG_DETECT_PATTERNS.items():
        if any(
            not _intersects_any_span(match.start(), match.end(), code_spans)
            for match in pattern.finditer(text)
        ):
            found.append(name)
            continue
        if any(
            not _intersects_any_span(match.start(), match.end(), code_spans)
            for match in _DYNAMIC_TAG_OPENING_PATTERNS[name].finditer(text)
        ):
            found.append(name)
    return found


# ``<include-many>`` is deferred past the recursive pass-1 hydration the audit
# runs (generation expands it in pass 2, after variable expansion). We expand
# the concrete, literal lists here so their file contents are attributed and
# counted; lists whose paths come from ``${VAR}`` only materialize at generation
# time, so they are reported as deferred rather than counted as markup.
_INCLUDE_MANY_RE = re.compile(
    r"<include-many(?:\s[^>]*+)?>(?P<inner>.*?)</include-many>", re.DOTALL
)


def _expand_include_many(text: str, recorder: "_SegmentRecorder") -> str:
    """Expand literal top-level ``<include-many>`` lists; defer variable ones."""
    code_spans = _extract_code_spans(text)
    user_intent_paths = compute_user_intent_paths(text)

    def _replace(match: "re.Match") -> str:
        if _intersects_any_span(match.start(), match.end(), code_spans):
            return match.group(0)
        inner = match.group("inner")
        if "${" in inner or "{" in inner:
            recorder.deferred.append(
                "include-many list is variable-driven and materializes at "
                "generation; its file contents are deferred and not counted"
            )
            return ""
        return process_include_many_tags(
            match.group(0),
            recursive=False,
            _user_intent_paths=user_intent_paths,
            _failed=[],
            snapshot_recorder=recorder,
        )

    return _INCLUDE_MANY_RE.sub(_replace, text)


# The audit resolves includes by temporarily mutating *process-global* state —
# ``os.chdir(base_dir)`` plus a couple of env vars. Under ``pdd connect`` the
# server calls the audit from a request handler, and the connect prompt screen
# fires the audit alongside ``/analyze`` in one debounced cycle, so two
# cwd-sensitive operations can be in flight at once. Because cwd/env are global,
# overlapping runs could otherwise observe a half-applied cwd and resolve
# includes against the wrong directory. This reentrant lock serializes that
# critical section so include resolution stays deterministic under concurrent
# connect usage (PR #1387 review #3). It is reentrant so a caller that already
# holds it via :func:`cwd_env_lock` (e.g. the ``/analyze`` route wrapping its own
# ``chdir`` + ``preprocess``) does not deadlock when it then runs an audit.
_CWD_ENV_LOCK = threading.RLock()


@contextlib.contextmanager
def cwd_env_lock():
    """Hold the audit's process-global cwd/env lock for cwd-sensitive work.

    The audit (and any other server code that resolves includes by changing the
    working directory — notably ``/analyze``'s ``chdir`` + ``preprocess``) must
    run its cwd mutation under this lock so concurrent ``pdd connect`` requests
    cannot cross-contaminate one another's include resolution (PR #1387 review
    #3). The lock is reentrant: wrapping a call that itself runs an audit is
    safe.
    """
    with _CWD_ENV_LOCK:
        yield


@contextlib.contextmanager
def _audit_env(base_dir: Optional[str] = None):
    """Quiet, no-query-fallback, optionally cwd-scoped environment for the audit.

    ``PDD_QUIET`` silences progress lines and ``PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK``
    tells preprocess never to fall back to ``IncludeQueryExtractor`` (an LLM call)
    when a deterministic ``select=`` on a ``query=`` include fails. ``base_dir``
    lets a caller (e.g. the server) resolve includes relative to a project root
    exactly as the CLI does when run from that directory.

    The whole body runs under :data:`_CWD_ENV_LOCK`: the env-var and cwd mutation
    are process-global, so holding the lock for the full set-yield-restore window
    guarantees concurrent audits (and lock-wrapped server work) never observe a
    partially-applied environment (PR #1387 review #3).
    """
    with _CWD_ENV_LOCK:
        prev_quiet = os.environ.get("PDD_QUIET")
        prev_no_query_fallback = os.environ.get("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK")
        prev_cwd = os.getcwd() if base_dir else None
        os.environ["PDD_QUIET"] = "1"
        os.environ["PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"] = "1"
        if base_dir:
            os.chdir(base_dir)
        try:
            yield
        finally:
            if prev_cwd is not None:
                os.chdir(prev_cwd)
            if prev_quiet is None:
                os.environ.pop("PDD_QUIET", None)
            else:
                os.environ["PDD_QUIET"] = prev_quiet
            if prev_no_query_fallback is None:
                os.environ.pop("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK", None)
            else:
                os.environ["PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"] = prev_no_query_fallback


def _hydrate(text: str) -> Tuple[str, _SegmentRecorder]:
    """Deterministically hydrate ``text`` (pass 1) and capture include segments.

    Mirrors what generation's first preprocessing pass does — recursive include
    expansion with selectors applied, but no variable expansion and no LLM /
    shell / web execution — and threads a recorder so each include's *realized*
    content is captured for attribution. Returns ``(expanded_text, recorder)``.
    Must be called inside :func:`_audit_env`.
    """
    recorder = _SegmentRecorder()
    # The include processor prints progress lines that are not gated by quiet
    # mode; redirect stdout so they cannot corrupt a caller's machine output.
    with contextlib.redirect_stdout(io.StringIO()):
        expanded = preprocess(
            text,
            recursive=True,
            double_curly_brackets=False,
            snapshot_recorder=recorder,
        )
        expanded = _expand_include_many(expanded, recorder)
    return expanded, recorder


def _display_source(source: str) -> str:
    """Render a recorded (resolved) include path relative to the cwd when possible."""
    try:
        rel = os.path.relpath(source, os.getcwd())
    except (ValueError, OSError):
        return source
    return source if rel.startswith("..") else rel


def _attribute_includes(
    records: List[Dict[str, str]], model: str
) -> Dict[str, int]:
    """Map each top-level include source to its realized token count.

    A nested include's content is expanded *into* its parent's content, so the
    recorder holds both. Counting all of them would double-count the nested
    text; keep only records emitted at include depth 0, which corresponds to
    the directives authored in the audited prompt. Repeated includes of the
    same source are summed.
    """
    by_source: Dict[str, int] = {}
    for rec in records:
        if int(rec.get("depth", 0) or 0) != 0:
            continue
        tokens = count_tokens(_strip_dynamic_markup(rec["content"]), model)
        display = _display_source(rec["source"])
        by_source[display] = by_source.get(display, 0) + tokens
    return by_source


def _unresolved_includes(raw: str) -> List[str]:
    """Top-level include paths that do not resolve to a readable file (CR #2).

    A context audit must not silently fold missing context into the body; an
    unresolved include is exactly the preflight failure a user needs to see.
    ``${VAR}`` paths are skipped — they only materialize after variable
    expansion at generation time, so they are deferred, not missing. Must be
    called inside :func:`_audit_env`.
    """
    _ = get_default_resolver()  # ensure resolver initialization errors surface here
    # Query includes are deferred (LLM-driven); strip them so the deterministic
    # include processors below never reach preprocess's semantic-extraction
    # branch. They are reported via the deferred dynamic-tag warning instead.
    raw = _strip_semantic_query_includes(raw)
    failed: List[str] = []
    user_intent_paths = compute_user_intent_paths(raw)
    with contextlib.redirect_stdout(io.StringIO()):
        checked = process_backtick_includes(
            raw,
            recursive=False,
            _failed=failed,
            _user_intent_paths=user_intent_paths,
        )
        checked = process_include_tags(
            checked,
            recursive=False,
            _failed=failed,
            _user_intent_paths=user_intent_paths,
        )
        process_include_many_tags(
            checked,
            recursive=False,
            _failed=failed,
            _user_intent_paths=compute_user_intent_paths(checked),
        )
    return sorted({path for path in failed if "${" not in path and "{" not in path})


def percent(part: int, whole: Optional[int]) -> Optional[float]:
    """Percent of ``part`` within ``whole`` (1 dp), or ``None`` when unknown."""
    if not whole:
        return None
    return round(part / whole * 100, 1)


def row_percent(row: AuditRow, total_tokens: int) -> float:
    """A row's share of the total tokens (0.0 when the total is zero)."""
    return percent(row.tokens, total_tokens) or 0.0


def threshold_exceeded(percent_used: Optional[float], threshold: int) -> bool:
    """Whether usage exceeds the budget threshold. ``threshold == 0`` disables it.

    The core never enforces a budget; this pure helper lets every surface apply
    the same rule (the CLI then chooses to exit non-zero, the server merely
    reports the bool).
    """
    return bool(percent_used is not None and 0 < threshold < percent_used)


def _build_rows(  # pylint: disable=too-many-locals
    raw: str, model: str
) -> Tuple[List[AuditRow], int, List[str]]:
    """Return ``(rows, total_tokens, warnings)`` attributing tokens per source."""
    expanded, recorder = _hydrate(raw)

    # The deterministic payload excludes deferred dynamic markup so the total —
    # and the percentages derived from it — reflect only what was actually
    # hydrated, not unexpanded <shell>/<web>/query tag text (review #3).
    total_tokens = count_tokens(_strip_dynamic_markup(expanded), model)

    warnings: List[str] = []
    deferred_rows: List[AuditRow] = []
    # Scan the *expanded* payload, not just the raw prompt, so dynamic tags that
    # live inside an included file are surfaced too (review #3).
    for tag in _detect_dynamic_tags_outside_code(expanded):
        note = (
            f"dynamic tag <{tag}> detected but not expanded "
            "(nondeterministic, deferred); excluded from the deterministic total"
        )
        warnings.append(note)
        deferred_rows.append(
            AuditRow(source=f"<{tag}>", tokens=0, status="deferred", note=note)
        )
    for note in recorder.deferred:
        warnings.append(note)
        deferred_rows.append(
            AuditRow(source="<include-many ${...}>", tokens=0, status="deferred", note=note)
        )

    rows: List[AuditRow] = []
    attributed = 0
    by_source = _attribute_includes(recorder.includes, model)
    for source, tokens in by_source.items():
        attributed += tokens
        rows.append(AuditRow(source=source, tokens=tokens, status="resolved"))

    for path in _unresolved_includes(raw):
        rows.append(
            AuditRow(
                source=path,
                tokens=0,
                status="unresolved",
                note="unresolved (file not found)",
            )
        )
        warnings.append(
            f"unresolved include: {path} "
            "(file not found; not part of the hydrated payload)"
        )

    rows.extend(deferred_rows)

    # Whatever is left after subtracting the resolved includes is the prompt
    # body. Clamp at zero: token counts of concatenated text are not strictly
    # additive (tokenizer boundary effects), so the subtraction can go slightly
    # negative for include-heavy prompts.
    body_tokens = max(0, total_tokens - attributed)
    rows.append(AuditRow(source="prompt_body", tokens=body_tokens, status="body"))

    # Grounding is a known segment but unavailable without PDD Cloud.
    rows.append(
        AuditRow(
            source="grounding",
            tokens=0,
            status="unavailable",
            note=_GROUNDING_UNAVAILABLE_NOTE,
        )
    )

    rows.sort(key=lambda r: r.tokens, reverse=True)
    return rows, total_tokens, warnings


def audit_prompt_text(
    text: str, model: str, *, base_dir: Optional[str] = None
) -> ContextAudit:
    """Audit already-loaded prompt ``text`` for ``model``.

    ``base_dir`` resolves relative includes from a project root (the server uses
    it so its rows match a CLI run from that directory). No LLM call is made.
    """
    with _audit_env(base_dir):
        rows, total_tokens, warnings = _build_rows(text, model)
    context_limit = get_context_limit(model)
    return ContextAudit(
        model=model,
        total_tokens=total_tokens,
        context_limit=context_limit,
        percent_used=percent(total_tokens, context_limit),
        rows=rows,
        warnings=warnings,
    )


def audit_prompt_file(
    prompt_path: str, model: str, *, base_dir: Optional[str] = None
) -> ContextAudit:
    """Audit the prompt file at ``prompt_path`` for ``model`` (no LLM call).

    ``base_dir`` resolves relative includes from a project root exactly as
    :func:`audit_prompt_text`. The server passes it so the audit's cwd change
    happens inside the shared :data:`_CWD_ENV_LOCK` (see :func:`_audit_env`)
    rather than the route mutating the process cwd itself — keeping connect
    audits deterministic under concurrency (PR #1387 review #3).
    """
    raw = Path(prompt_path).read_text(encoding="utf-8")
    return audit_prompt_text(raw, model, base_dir=base_dir)
