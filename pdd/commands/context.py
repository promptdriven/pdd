"""context command: per-source token attribution for a hydrated prompt.

A thin CLI over the shared :mod:`pdd.context_audit` core (PR #1387 review #2):
the audit business logic — deterministic hydration, per-include attribution,
unresolved-include detection, deferred dynamic-tag handling — lives in the core
so the ``pdd context`` CLI and the ``pdd connect`` server endpoint give identical
answers. This module owns only CLI concerns: argument parsing, model-default
resolution, the budget-threshold exit-code policy, and rendering (the
``/context``-style usage box by default, ``--table`` for the raw attribution
table, ``--json`` for machine-readable output). The deterministic audit still
makes no LLM call.
"""
from __future__ import annotations

import json as json_module
import os
import sys
from typing import Callable, List, Optional, Tuple

import click

from ..cli_theme import (
    ANSI_FAINT,
    ANSI_RESET,
    BREAK_RED,
    BUILD_GREEN,
    DIFF_YELLOW,
    ELECTRIC_CYAN,
    LUMEN_PURPLE,
    PROMPT_MAGENTA,
    hex_to_ansi,
)
from ..context_audit import (
    AuditRow,
    ContextAudit,
    audit_prompt_file,
    percent,
    row_percent,
    threshold_exceeded,
)
from ..core.errors import handle_error

# Glyphs mirror Claude Code's ``/context`` usage box — the view this command is
# modeled on: a draughts piece for a used token cell and ``⛶`` (U+26F6) for free
# space. On macOS, Terminal.app's CoreText font fallback (Apple Symbols) renders
# all of them as single narrow cells, so the grid stays aligned. Color is the
# *primary* per-source channel, but the glyph is a *parallel* one: every counted
# source also gets its own glyph (see ``_SOURCE_GLYPHS`` / ``_row_styles``), so the
# grid keeps per-source attribution even with color off (pipes, CI, ``NO_COLOR``).
# The cloud-only ``unavailable`` row uses a faint ``▨`` and free space a faint
# ``⛶``, both legible without color. ``_glyph_for`` picks the glyph for the
# reserved override rows.
_USED_GLYPH = "⛁"          # U+26C1 — a used token cell (Claude /context style)
_UNAVAILABLE_GLYPH = "▨"   # U+25A8 — faint, distinct (requires PDD Cloud)
_FREE_GLYPH = "⛶"          # U+26F6 — faint, reads as empty space
# One distinct draughts glyph per palette hue, so a counted source is identified
# by glyph as well as color. All four are Neutral-width like ``_USED_GLYPH`` and
# render via Terminal.app's Apple Symbols fallback, so the grid stays aligned.
# With color off the glyph alone keeps the first ``len(_SOURCE_GLYPHS)`` sources
# distinct in the grid; like the colors, the glyphs cycle (wrap) when there are
# more sources than entries, so two sources that share a glyph also share a color.
_SOURCE_GLYPHS = (_USED_GLYPH, "⛀", "⛃", "⛂")  # U+26C1/26C0/26C3/26C2 draughts
_BOX_COLS = 27
_BOX_ROWS = 5


def _glyph_for(status: str) -> str:
    """Glyph for an override row's ``status``: a distinct one for ``unavailable``,
    the base ``_USED_GLYPH`` otherwise. Counted-source glyphs come from
    :func:`_row_styles` (which varies them by position); this picks the glyph for
    the reserved/override rows that do not participate in the source cycle."""
    return _UNAVAILABLE_GLYPH if status == "unavailable" else _USED_GLYPH

# --- Token coloring rules (one place; no scattered ANSI codes) --------------
#
# Color distinguishes *sources*, with two semantic colors reserved as overrides
# for problem rows so they always pop — like Claude Code's ``/context`` (each
# area its own color; trouble stands out). All hues are brand colors from
# cli_theme (PromptDriven.ai Brand Guidelines v1.4 §3):
#   * ``unresolved`` (a missing include)  -> Break-Red   (always)
#   * ``deferred``   (dynamic, not realized) -> Diff-Yellow (always)
#   * ``unavailable``/free space          -> faint        (low emphasis)
#   * every other (counted) source        -> the next color in ``_SOURCE_CYCLE``,
#       assigned by the source's position in the core's deterministic row order
#       so two includes never share a color (they cycle if there are more
#       sources than palette entries, but neighbors always differ).
_SOURCE_CYCLE = (
    hex_to_ansi(ELECTRIC_CYAN),
    hex_to_ansi(PROMPT_MAGENTA),
    hex_to_ansi(BUILD_GREEN),
    hex_to_ansi(LUMEN_PURPLE),
)
_STATUS_OVERRIDE = {
    "unresolved": hex_to_ansi(BREAK_RED),
    "deferred": hex_to_ansi(DIFF_YELLOW),
    "unavailable": ANSI_FAINT,
}
_FREE_COLOR = ANSI_FAINT


def _row_styles(rows: List[AuditRow]) -> List[Tuple[str, str]]:
    """``(glyph, color)`` per row (parallel to ``rows``) — the single source of
    truth for how each row is drawn.

    A row whose ``status`` has a reserved override takes that color and a
    status glyph (:func:`_glyph_for`: ``⛁``, or ``▨`` for ``unavailable``). Every
    other (counted) source takes a parallel glyph+color identity by its position
    among counted rows: glyph and color each cycle their own table per source, so
    the first ``len(_SOURCE_GLYPHS)`` distinct sources differ in *both* channels.
    The glyph alone therefore keeps the grid source-attributed with color off; like
    the colors, glyphs wrap when there are more sources than entries (two sources
    sharing a glyph also share a color). Overrides never consume a cycle slot.
    Deterministic, given the core's stable row order.
    """
    styles: List[Tuple[str, str]] = []
    nth_source = 0
    for row in rows:
        override = _STATUS_OVERRIDE.get(row.status)
        if override is not None:
            styles.append((_glyph_for(row.status), override))
        else:
            color = _SOURCE_CYCLE[nth_source % len(_SOURCE_CYCLE)]
            glyph = _SOURCE_GLYPHS[nth_source % len(_SOURCE_GLYPHS)]
            styles.append((glyph, color))
            nth_source += 1
    return styles


def _row_colors(rows: List[AuditRow]) -> List[str]:
    """ANSI color per row (parallel to ``rows``) — the color half of
    :func:`_row_styles`, kept for callers (e.g. ``--table``) that color by source
    but draw no glyph.
    """
    return [color for _glyph, color in _row_styles(rows)]


# Type of the seam every colored surface paints through: ``paint(color, text)``
# where ``color`` is an ANSI prefix (from :func:`_row_styles` / :data:`_FREE_COLOR`).
Painter = Callable[[str, str], str]


def _make_painter(enabled: bool) -> Painter:
    """Return the single ``paint(color, text)`` seam used for all coloring.

    When ``enabled`` is false it returns ``text`` unchanged, so the no-color path
    is byte-for-byte identical to the uncolored output (CI logs, pipes, JSON's
    siblings stay clean). When enabled it wraps ``text`` in the given ANSI
    ``color`` prefix, resetting after.
    """

    def paint(color: str, text: str) -> str:
        if not enabled or not color:
            return text
        return f"{color}{text}{ANSI_RESET}"

    return paint


def _color_enabled(preference: Optional[bool], stream) -> bool:
    """Resolve whether to emit ANSI color for ``stream``.

    Explicit ``--color`` / ``--no-color`` (``preference`` True/False) always wins.
    Otherwise auto-detect: honor ``NO_COLOR`` (https://no-color.org — any value,
    including empty, disables) and emit color only when ``stream`` is a TTY, so
    piping or redirecting (``pdd context ... | tee``) and CI logs stay plain.
    """
    if preference is not None:
        return preference
    if os.environ.get("NO_COLOR") is not None:
        return False
    isatty = getattr(stream, "isatty", None)
    return bool(isatty()) if callable(isatty) else False


def _render_usage_box(  # pylint: disable=too-many-locals
    audit: ContextAudit,
    paint: Optional[Painter] = None,
) -> str:
    """Render a Claude-Code ``/context``-style usage box for the attribution.

    The grid shows used context-window space, each source in its own ``(glyph,
    color)`` identity (problem rows take a reserved red/yellow ``⛁``), against free
    space (``⛶``), followed by the model, the total/limit/percent summary, and a
    per-source breakdown. ``paint`` is the coloring seam; when omitted, output is
    uncolored.
    """
    if paint is None:
        paint = _make_painter(False)
    rows = audit.rows
    context_limit = audit.context_limit
    styles = _row_styles(rows)
    lines: List[str] = ["Context Usage", ""]

    if context_limit:
        total_cells = _BOX_COLS * _BOX_ROWS
        cells: List[str] = []
        for row, (glyph, color) in zip(rows, styles):
            count = int(round(row.tokens / context_limit * total_cells))
            cells.extend([paint(color, glyph)] * count)
        cells = cells[:total_cells]
        free_cell = paint(_FREE_COLOR, _FREE_GLYPH)
        cells.extend([free_cell] * (total_cells - len(cells)))
        for r in range(_BOX_ROWS):
            chunk = cells[r * _BOX_COLS:(r + 1) * _BOX_COLS]
            lines.append("  " + " ".join(chunk))
        lines.append("")

    lines.append(f"  {audit.model}")
    if context_limit:
        lines.append(
            f"  {audit.total_tokens:,}/{context_limit:,} tokens ({audit.percent_used}%)"
        )
    else:
        lines.append(f"  {audit.total_tokens:,} tokens  (context limit unknown)")
    lines.append("")
    lines.append("  Estimated usage by category")

    share_basis = context_limit if context_limit else audit.total_tokens
    for row, (glyph, color) in zip(rows, styles):
        share = percent(row.tokens, share_basis)
        share_text = f"{share}%" if share is not None else "-"
        note = f"  (WARN: {row.note})" if row.note else ""
        marker = paint(color, f"{glyph} {row.source}")
        lines.append(
            f"  {marker}: {row.tokens:,} tokens ({share_text}){note}"
        )

    if context_limit:
        free = max(0, context_limit - audit.total_tokens)
        free_pct = percent(free, context_limit)
        free_text = f"{free_pct}%" if free_pct is not None else "-"
        free_marker = paint(_FREE_COLOR, f"{_FREE_GLYPH} Free space")
        lines.append(f"  {free_marker}: {free:,} tokens ({free_text})")

    return "\n".join(lines)


def _render_table(audit: ContextAudit, paint: Optional[Painter] = None) -> str:
    """Render the per-source token-attribution table (``--table``).

    ``paint`` colors only the ``Source`` cell by the row's color; it is applied
    *after* fixed-width padding so column alignment is unaffected by escape
    sequences. When omitted, output is uncolored.
    """
    if paint is None:
        paint = _make_painter(False)
    rows = audit.rows
    colors = _row_colors(rows)
    limit_text = f"{audit.context_limit:,} tokens" if audit.context_limit else "unknown"
    pct_text = f"{audit.percent_used}%" if audit.percent_used is not None else "unknown%"
    lines = [
        f"Model: {audit.model}  |  Context limit: {limit_text}",
        f"Total tokens: {audit.total_tokens:,}  ({pct_text} of context window)",
        "",
        f"{'Source':<48}{'Tokens':>10}{'% of total':>14}",
        "-" * 72,
    ]
    for row, color in zip(rows, colors):
        row_pct = percent(row.tokens, audit.total_tokens)
        pct_col = f"{row_pct}%" if row_pct is not None else "-"
        note = f"  (WARN: {row.note})" if row.note else ""
        source_col = paint(color, f"{row.source:<48}")
        lines.append(f"{source_col}{row.tokens:>10,}{pct_col:>14}{note}")
    return "\n".join(lines)


def _json_payload(audit: ContextAudit, threshold_hit: bool) -> dict:
    """Assemble the machine-readable ``--json`` object from an audit result.

    Top-level keys are unchanged for backward compatibility; each row now also
    carries ``status`` and ``note`` so callers never parse warning strings to
    learn a row's state (PR #1387 review #4).
    """
    return {
        "total_tokens": audit.total_tokens,
        "context_limit": audit.context_limit,
        "percent_used": audit.percent_used,
        "model": audit.model,
        "rows": [
            {
                "source": r.source,
                "tokens": r.tokens,
                "percent": row_percent(r, audit.total_tokens),
                "status": r.status,
                "note": r.note,
            }
            for r in audit.rows
        ],
        "warnings": audit.warnings,
        "threshold_exceeded": threshold_hit,
    }


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
@click.option(
    "--color/--no-color",
    "color",
    default=None,
    help="Force or disable ANSI color in the usage box / table. "
    "Default: auto (color on a TTY, off when piped or NO_COLOR is set). "
    "JSON output is always uncolored.",
)
@click.pass_context
def context(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    ctx: click.Context,
    prompt_path: str,
    model: Optional[str],
    json_output: bool,
    table_output: bool,
    threshold: int,
    color: Optional[bool],
) -> None:
    """Show context-window usage by source for a preprocessed prompt."""

    try:
        if isinstance(ctx.obj, dict):
            ctx.obj["_suppress_result_summary"] = True
            ctx.obj["_suppress_core_dump"] = True

        resolved_model = model or os.environ.get("PDD_MODEL_DEFAULT") or "gpt-4o"

        audit = audit_prompt_file(prompt_path, resolved_model)
        threshold_hit = threshold_exceeded(audit.percent_used, threshold)

        if json_output:
            # Machine-readable output stays byte-stable and never colored, so
            # CI/agent parsers are unaffected by the rendering change.
            click.echo(
                json_module.dumps(
                    _json_payload(audit, threshold_hit), indent=2, sort_keys=True
                )
            )
            if threshold_hit:
                raise click.exceptions.Exit(2)
            return

        # Decide once, then tell click.echo explicitly (color=use_color) so it
        # does not second-guess us: click strips ANSI on a non-TTY by default,
        # which would drop color from a forced ``--color`` run, and would keep
        # it on a TTY even when we chose to suppress it.
        #
        # Precedence: this command's own ``--color/--no-color`` wins; otherwise
        # inherit the global ``pdd --color/--no-color`` preference (ctx.obj);
        # otherwise auto-detect. This keeps ``pdd --color context …`` consistent
        # with the rest of the CLI even through a pipe.
        color_pref = color
        if color_pref is None and isinstance(ctx.obj, dict):
            color_pref = ctx.obj.get("color")
        use_color = _color_enabled(color_pref, sys.stdout)
        paint = _make_painter(use_color)
        if table_output:
            rendered = _render_table(audit, paint)
        else:
            rendered = _render_usage_box(audit, paint)
        click.echo(rendered, color=use_color)

        for warning in audit.warnings:
            click.echo(f"WARN: {warning}", err=True)

        if threshold_hit:
            click.echo(
                f"WARN: context budget exceeded — {audit.percent_used}% of limit "
                f"is above the {threshold}% threshold.",
                err=True,
            )
            raise click.exceptions.Exit(2)
    except (click.Abort, click.UsageError, click.exceptions.Exit):
        raise
    except Exception as exc:  # pragma: no cover - defensive  # pylint: disable=broad-exception-caught
        handle_error(exc, "context", (ctx.obj or {}).get("quiet", False))
