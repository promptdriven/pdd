"""context command: per-source token attribution for a hydrated prompt.

Preprocesses a prompt file the same way generation does and reports how many
tokens each source segment (prompt body, each ``<include>``, grounding) adds to
the hydrated payload -- without making an LLM call. By default it renders a
Claude-Code ``/context``-style usage box (a category breakdown of the context
window); ``--table`` shows the per-source attribution table and ``--json``
emits machine-readable output. This makes context-window cost visible so users
can find oversized includes and gate CI on a budget.
"""
from __future__ import annotations

import contextlib
import io
import json as json_module
import os
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import click

from ..context_snapshot import detect_dynamic_tags
from ..core.errors import handle_error
from ..path_resolution import get_default_resolver
from ..preprocess import (
    _extract_code_spans,
    _intersects_any_span,
    _parse_attrs,
    compute_user_intent_paths,
    process_backtick_includes,
    process_include_tags,
    preprocess,
    process_include_many_tags,
)
from ..server.token_counter import count_tokens, get_context_limit

# Grounding requires PDD Cloud; it is reported as 0 tokens with a deferred
# warning rather than triggering a network call (see issue #789 acceptance).
_GROUNDING_UNAVAILABLE_NOTE = "unavailable (requires cloud)"

# Dynamic directives are *deferred* in the deterministic pass-1 hydration the
# audit performs: their markup survives in the expanded text but the real
# content (a shell run, a web fetch, a semantic query extraction) is never
# produced. We must not bill that leftover markup as if it were the hydrated
# payload (issue #789 review #3), so it is stripped before token counting and
# surfaced as a warning instead. These match the same forms as
# ``context_snapshot._DYNAMIC_TAG_PATTERNS`` but span the whole element.
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


# Matches a whole ``<include ...>...</include>`` (or self-closing) element so its
# attributes can be parsed; used only to decide whether a directive is a
# semantic ``query=`` include that must be skipped (see below).
_QUERY_INCLUDE_ELEMENT_RE = re.compile(
    r"<include(?P<attrs>\s+[^>]*?)?>(?P<content>.*?)</include>"
    r"|<include(?P<attrs_self>\s+[^>]*?)\s*/>",
    re.IGNORECASE | re.DOTALL,
)


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
        text = pattern.sub("", text)
    return text


# ``<include-many>`` is deferred past the recursive pass-1 hydration the audit
# runs (generation expands it in pass 2, after variable expansion). We expand
# the concrete, literal lists here so their file contents are attributed and
# counted; lists whose paths come from ``${VAR}`` only materialize at generation
# time, so they are reported as deferred rather than counted as markup.
_INCLUDE_MANY_RE = re.compile(
    r"<include-many(?:\s+[^>]*?)?>(?P<inner>.*?)</include-many>", re.DOTALL
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

# Distinct glyphs let categories be told apart in the monochrome usage box,
# mirroring the colored squares of Claude Code's ``/context`` display. ``⛶``
# marks free (unused) context-window space.
_CATEGORY_GLYPHS = ("⛁", "⛀", "⛂", "▩", "▦", "▧", "▤", "▥", "▣", "▢")
_FREE_GLYPH = "⛶"
_BOX_COLS = 27
_BOX_ROWS = 5


def _hydrate(text: str) -> Tuple[str, _SegmentRecorder]:
    """Deterministically hydrate ``text`` (pass 1) and capture include segments.

    Mirrors what generation's first preprocessing pass does — recursive include
    expansion with selectors applied, but no variable expansion and no LLM /
    shell / web execution — and threads a recorder so each include's *realized*
    content is captured for attribution. Returns ``(expanded_text, recorder)``.
    """
    recorder = _SegmentRecorder()
    prev_quiet = os.environ.get("PDD_QUIET")
    prev_no_query_fallback = os.environ.get("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK")
    os.environ["PDD_QUIET"] = "1"
    os.environ["PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"] = "1"
    try:
        # The include processor prints progress lines that are not gated by
        # quiet mode; redirect stdout so they cannot corrupt --json output.
        with contextlib.redirect_stdout(io.StringIO()):
            expanded = preprocess(
                text,
                recursive=True,
                double_curly_brackets=False,
                snapshot_recorder=recorder,
            )
            expanded = _expand_include_many(expanded, recorder)
        return expanded, recorder
    finally:
        if prev_quiet is None:
            os.environ.pop("PDD_QUIET", None)
        else:
            os.environ["PDD_QUIET"] = prev_quiet
        if prev_no_query_fallback is None:
            os.environ.pop("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK", None)
        else:
            os.environ[
                "PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"
            ] = prev_no_query_fallback


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
    expansion at generation time, so they are deferred, not missing.
    """
    _ = get_default_resolver()  # ensure resolver initialization errors surface here
    # Query includes are deferred (LLM-driven); strip them so the deterministic
    # include processors below never reach preprocess's semantic-extraction
    # branch. They are reported via the deferred dynamic-tag warning instead.
    raw = _strip_semantic_query_includes(raw)
    failed: List[str] = []
    user_intent_paths = compute_user_intent_paths(raw)
    prev_quiet = os.environ.get("PDD_QUIET")
    prev_no_query_fallback = os.environ.get("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK")
    os.environ["PDD_QUIET"] = "1"
    os.environ["PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"] = "1"
    try:
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
    finally:
        if prev_quiet is None:
            os.environ.pop("PDD_QUIET", None)
        else:
            os.environ["PDD_QUIET"] = prev_quiet
        if prev_no_query_fallback is None:
            os.environ.pop("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK", None)
        else:
            os.environ[
                "PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"
            ] = prev_no_query_fallback
    return sorted({path for path in failed if "${" not in path and "{" not in path})


def _build_rows(prompt_path: str, model: str) -> Tuple[List[Dict], int, List[str]]:
    """Return ``(rows, total_tokens, warnings)`` attributing tokens per source."""
    raw = Path(prompt_path).read_text(encoding="utf-8")
    expanded, recorder = _hydrate(raw)

    # The deterministic payload excludes deferred dynamic markup so the total —
    # and the percentages derived from it — reflect only what was actually
    # hydrated, not unexpanded <shell>/<web>/query tag text (review #3).
    total_tokens = count_tokens(_strip_dynamic_markup(expanded), model)

    warnings: List[str] = []
    # Scan the *expanded* payload, not just the raw prompt, so dynamic tags that
    # live inside an included file are surfaced too (review #3).
    for tag in detect_dynamic_tags(expanded):
        warnings.append(
            f"dynamic tag <{tag}> detected but not expanded "
            "(nondeterministic, deferred); excluded from the deterministic total"
        )
    warnings.extend(recorder.deferred)

    rows: List[Dict] = []
    attributed = 0
    by_source = _attribute_includes(recorder.includes, model)
    for source, tokens in by_source.items():
        attributed += tokens
        rows.append({"source": source, "tokens": tokens})

    for path in _unresolved_includes(raw):
        rows.append({"source": path, "tokens": 0, "note": "unresolved (file not found)"})
        warnings.append(
            f"unresolved include: {path} "
            "(file not found; not part of the hydrated payload)"
        )

    # Whatever is left after subtracting the resolved includes is the prompt
    # body. Clamp at zero: token counts of concatenated text are not strictly
    # additive (tokenizer boundary effects), so the subtraction can go slightly
    # negative for include-heavy prompts.
    body_tokens = max(0, total_tokens - attributed)
    rows.append({"source": "prompt_body", "tokens": body_tokens})

    # Grounding is a known segment but unavailable without PDD Cloud.
    rows.append(
        {"source": "grounding", "tokens": 0, "note": _GROUNDING_UNAVAILABLE_NOTE}
    )

    rows.sort(key=lambda r: r["tokens"], reverse=True)
    return rows, total_tokens, warnings


def _percent(part: int, whole: Optional[int]) -> Optional[float]:
    if not whole:
        return None
    return round(part / whole * 100, 1)


def _render_usage_box(
    rows: List[Dict],
    total_tokens: int,
    context_limit: Optional[int],
    model: str,
    percent_used: Optional[float],
) -> str:
    """Render a Claude-Code ``/context``-style usage box for the attribution.

    The grid shows used context-window space split by category (one glyph per
    source) against free space (``⛶``), followed by the model, the
    total/limit/percent summary, and a per-category breakdown.
    """
    lines: List[str] = ["Context Usage", ""]

    if context_limit:
        total_cells = _BOX_COLS * _BOX_ROWS
        cells: List[str] = []
        for idx, row in enumerate(rows):
            glyph = _CATEGORY_GLYPHS[idx % len(_CATEGORY_GLYPHS)]
            count = int(round(row["tokens"] / context_limit * total_cells))
            cells.extend([glyph] * count)
        cells = cells[:total_cells]
        cells.extend([_FREE_GLYPH] * (total_cells - len(cells)))
        for r in range(_BOX_ROWS):
            chunk = cells[r * _BOX_COLS:(r + 1) * _BOX_COLS]
            lines.append("  " + " ".join(chunk))
        lines.append("")

    lines.append(f"  {model}")
    if context_limit:
        lines.append(
            f"  {total_tokens:,}/{context_limit:,} tokens ({percent_used}%)"
        )
    else:
        lines.append(f"  {total_tokens:,} tokens  (context limit unknown)")
    lines.append("")
    lines.append("  Estimated usage by category")

    share_basis = context_limit if context_limit else total_tokens
    for idx, row in enumerate(rows):
        glyph = _CATEGORY_GLYPHS[idx % len(_CATEGORY_GLYPHS)]
        share = _percent(row["tokens"], share_basis)
        share_text = f"{share}%" if share is not None else "-"
        note = f"  (WARN: {row['note']})" if row.get("note") else ""
        lines.append(
            f"  {glyph} {row['source']}: {row['tokens']:,} tokens ({share_text}){note}"
        )

    if context_limit:
        free = max(0, context_limit - total_tokens)
        free_pct = _percent(free, context_limit)
        free_text = f"{free_pct}%" if free_pct is not None else "-"
        lines.append(f"  {_FREE_GLYPH} Free space: {free:,} tokens ({free_text})")

    return "\n".join(lines)


def _render_table(
    rows: List[Dict],
    total_tokens: int,
    context_limit: Optional[int],
    model: str,
    percent_used: Optional[float],
) -> str:
    """Render the per-source token-attribution table (``--table``)."""
    limit_text = f"{context_limit:,} tokens" if context_limit else "unknown"
    pct_text = f"{percent_used}%" if percent_used is not None else "unknown%"
    lines = [
        f"Model: {model}  |  Context limit: {limit_text}",
        f"Total tokens: {total_tokens:,}  ({pct_text} of context window)",
        "",
        f"{'Source':<48}{'Tokens':>10}{'% of total':>14}",
        "-" * 72,
    ]
    for row in rows:
        row_pct = _percent(row["tokens"], total_tokens)
        pct_col = f"{row_pct}%" if row_pct is not None else "-"
        note = f"  (WARN: {row['note']})" if row.get("note") else ""
        lines.append(f"{row['source']:<48}{row['tokens']:>10,}{pct_col:>14}{note}")
    return "\n".join(lines)


@click.command("context")
@click.argument("prompt_path", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--model",
    default=None,
    help="Model name for context-limit lookup (default: PDD_MODEL_DEFAULT env, else gpt-4o).",
)
@click.option(
    "--json",
    "json_output",
    is_flag=True,
    default=False,
    help="Emit machine-readable JSON instead of the usage box.",
)
@click.option(
    "--table",
    "table_output",
    is_flag=True,
    default=False,
    help="Show the per-source token-attribution table instead of the usage box.",
)
@click.option(
    "--threshold",
    type=click.IntRange(0, 100),
    default=80,
    show_default=True,
    help="Exit with code 2 when total tokens exceed N% of the context limit. 0 disables.",
)
@click.pass_context
def context(  # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals
    ctx: click.Context,
    prompt_path: str,
    model: Optional[str],
    json_output: bool,
    table_output: bool,
    threshold: int,
) -> None:
    """Show context-window usage by source for a preprocessed prompt."""

    try:
        if isinstance(ctx.obj, dict):
            ctx.obj["_suppress_result_summary"] = True
            ctx.obj["_suppress_core_dump"] = True

        resolved_model = model or os.environ.get("PDD_MODEL_DEFAULT") or "gpt-4o"

        rows, total_tokens, warnings = _build_rows(prompt_path, resolved_model)
        context_limit = get_context_limit(resolved_model)
        percent_used = _percent(total_tokens, context_limit)

        threshold_exceeded = bool(
            percent_used is not None
            and 0 < threshold < percent_used
        )

        if json_output:
            payload = {
                "total_tokens": total_tokens,
                "context_limit": context_limit,
                "percent_used": percent_used,
                "model": resolved_model,
                "rows": [
                    {
                        "source": r["source"],
                        "tokens": r["tokens"],
                        "percent": _percent(r["tokens"], total_tokens) or 0.0,
                    }
                    for r in rows
                ],
                "warnings": warnings,
                "threshold_exceeded": threshold_exceeded,
            }
            click.echo(json_module.dumps(payload, indent=2, sort_keys=True))
            if threshold_exceeded:
                raise click.exceptions.Exit(2)
            return

        if table_output:
            click.echo(
                _render_table(
                    rows, total_tokens, context_limit, resolved_model, percent_used
                )
            )
        else:
            click.echo(
                _render_usage_box(
                    rows, total_tokens, context_limit, resolved_model, percent_used
                )
            )

        for warning in warnings:
            click.echo(f"WARN: {warning}", err=True)

        if threshold_exceeded:
            click.echo(
                f"WARN: context budget exceeded — {percent_used}% of limit "
                f"is above the {threshold}% threshold.",
                err=True,
            )
            raise click.exceptions.Exit(2)
    except (click.Abort, click.UsageError, click.exceptions.Exit):
        raise
    except Exception as exc:  # pragma: no cover - defensive
        handle_error(exc, "context", (ctx.obj or {}).get("quiet", False))
