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
from typing import Callable, List, Optional

import click

from ..cli_theme import (
    ANSI_FAINT,
    ANSI_RESET,
    BREAK_RED,
    DIFF_YELLOW,
    ELECTRIC_CYAN,
    LUMEN_PURPLE,
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

# Distinct glyphs let sources be told apart even with color off, mirroring the
# colored squares of Claude Code's ``/context`` display. ``⛶`` marks free
# (unused) context-window space.
_CATEGORY_GLYPHS = ("⛁", "⛀", "⛂", "▩", "▦", "▧", "▤", "▥", "▣", "▢")
_FREE_GLYPH = "⛶"
_BOX_COLS = 27
_BOX_ROWS = 5

# --- Token coloring rules (one place; no scattered ANSI codes) --------------
#
# A row's *category* is its deterministic ``status`` (plus the synthetic
# ``"free"`` for unused space), so color tracks what a segment IS, not which
# file it came from. Each category maps to exactly one brand color, sourced from
# cli_theme (PromptDriven.ai Brand Guidelines v1.4 §3) — like Claude Code's
# ``/context``, color carries meaning rather than decoration:
#   body        the prompt's own instructions (the hero)      -> Electric-Cyan
#   resolved    a hydrated ``<include>`` source                -> Lumen-Purple
#   deferred    dynamic markup not yet realized (warn)         -> Diff-Yellow
#   unresolved  an include path that did not resolve (error)   -> Break-Red
#   unavailable requires PDD Cloud; counted as 0 tokens        -> faint
#   free        unused context-window space (low emphasis)     -> faint
_CATEGORY_COLOR = {
    "body": hex_to_ansi(ELECTRIC_CYAN),
    "resolved": hex_to_ansi(LUMEN_PURPLE),
    "deferred": hex_to_ansi(DIFF_YELLOW),
    "unresolved": hex_to_ansi(BREAK_RED),
    "unavailable": ANSI_FAINT,
    "free": ANSI_FAINT,
}

# Type of the seam every colored surface paints through: ``paint(category, text)``.
Painter = Callable[[str, str], str]


def _make_painter(enabled: bool) -> Painter:
    """Return the single ``paint(category, text)`` seam used for all coloring.

    When ``enabled`` is false it returns ``text`` unchanged, so the no-color path
    is byte-for-byte identical to the uncolored output (CI logs, pipes, JSON's
    siblings stay clean). When enabled it wraps ``text`` in the category's brand
    color from :data:`_CATEGORY_COLOR`, resetting after.
    """

    def paint(category: str, text: str) -> str:
        if not enabled:
            return text
        color = _CATEGORY_COLOR.get(category)
        return f"{color}{text}{ANSI_RESET}" if color else text

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
    rows: List[AuditRow],
    total_tokens: int,
    context_limit: Optional[int],
    model: str,
    percent_used: Optional[float],
    paint: Optional[Painter] = None,
) -> str:
    """Render a Claude-Code ``/context``-style usage box for the attribution.

    The grid shows used context-window space split by category (one glyph per
    source, colored by the source's category) against free space (``⛶``),
    followed by the model, the total/limit/percent summary, and a per-category
    breakdown. ``paint`` is the coloring seam; when omitted, output is uncolored.
    """
    if paint is None:
        paint = _make_painter(False)
    lines: List[str] = ["Context Usage", ""]

    if context_limit:
        total_cells = _BOX_COLS * _BOX_ROWS
        cells: List[str] = []
        for idx, row in enumerate(rows):
            glyph = _CATEGORY_GLYPHS[idx % len(_CATEGORY_GLYPHS)]
            count = int(round(row.tokens / context_limit * total_cells))
            cells.extend([paint(row.status, glyph)] * count)
        cells = cells[:total_cells]
        free_cell = paint("free", _FREE_GLYPH)
        cells.extend([free_cell] * (total_cells - len(cells)))
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
        share = percent(row.tokens, share_basis)
        share_text = f"{share}%" if share is not None else "-"
        note = f"  (WARN: {row.note})" if row.note else ""
        marker = paint(row.status, f"{glyph} {row.source}")
        lines.append(
            f"  {marker}: {row.tokens:,} tokens ({share_text}){note}"
        )

    if context_limit:
        free = max(0, context_limit - total_tokens)
        free_pct = percent(free, context_limit)
        free_text = f"{free_pct}%" if free_pct is not None else "-"
        free_marker = paint("free", f"{_FREE_GLYPH} Free space")
        lines.append(f"  {free_marker}: {free:,} tokens ({free_text})")

    return "\n".join(lines)


def _render_table(
    rows: List[AuditRow],
    total_tokens: int,
    context_limit: Optional[int],
    model: str,
    percent_used: Optional[float],
    paint: Optional[Painter] = None,
) -> str:
    """Render the per-source token-attribution table (``--table``).

    ``paint`` colors only the ``Source`` cell by the row's category; it is
    applied *after* fixed-width padding so column alignment is unaffected by
    escape sequences. When omitted, output is uncolored.
    """
    if paint is None:
        paint = _make_painter(False)
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
        row_pct = percent(row.tokens, total_tokens)
        pct_col = f"{row_pct}%" if row_pct is not None else "-"
        note = f"  (WARN: {row.note})" if row.note else ""
        source_col = paint(row.status, f"{row.source:<48}")
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
        use_color = _color_enabled(color, sys.stdout)
        paint = _make_painter(use_color)
        if table_output:
            rendered = _render_table(
                audit.rows,
                audit.total_tokens,
                audit.context_limit,
                audit.model,
                audit.percent_used,
                paint,
            )
        else:
            rendered = _render_usage_box(
                audit.rows,
                audit.total_tokens,
                audit.context_limit,
                audit.model,
                audit.percent_used,
                paint,
            )
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
    except Exception as exc:  # pragma: no cover - defensive
        handle_error(exc, "context", (ctx.obj or {}).get("quiet", False))
