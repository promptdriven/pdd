"""context-audit command: per-source token attribution for a hydrated prompt.

Preprocesses a prompt file the same way generation does and reports how many
tokens each source segment (prompt body, each ``<include>``, grounding) adds to
the hydrated payload — without making an LLM call. This makes context-window
cost visible so users can find oversized includes and gate CI on a budget.
"""
from __future__ import annotations

import contextlib
import io
import json as json_module
import os
from pathlib import Path
from typing import Dict, List, Optional

import click

from ..context_snapshot import detect_dynamic_tags
from ..core.errors import handle_error
from ..path_resolution import get_default_resolver
from ..preprocess import compute_user_intent_paths, preprocess
from ..server.token_counter import count_tokens, get_context_limit

# Grounding requires PDD Cloud; it is reported as 0 tokens with a deferred
# warning rather than triggering a network call (see issue #789 acceptance).
_GROUNDING_UNAVAILABLE_NOTE = "unavailable (requires cloud)"


def _hydrate(text: str) -> str:
    """Run the preprocessing pipeline quietly to obtain fully hydrated text."""
    prev_quiet = os.environ.get("PDD_QUIET")
    os.environ["PDD_QUIET"] = "1"
    try:
        # The include processor prints progress lines that are not gated by
        # quiet mode; redirect stdout so they cannot corrupt --json output.
        with contextlib.redirect_stdout(io.StringIO()):
            return preprocess(text, recursive=True, double_curly_brackets=False)
    finally:
        if prev_quiet is None:
            os.environ.pop("PDD_QUIET", None)
        else:
            os.environ["PDD_QUIET"] = prev_quiet


def _include_segment_tokens(include_path: str, model: str) -> Optional[int]:
    """Resolve a single include and count tokens in its hydrated content.

    Returns ``None`` when the include cannot be resolved or read (e.g. a
    ``${VAR}`` path that only materialises at generation time), so the caller
    can skip attributing it rather than reporting a misleading zero.
    """
    try:
        resolved = get_default_resolver().resolve_include(include_path)
        raw = Path(resolved).read_text(encoding="utf-8")
    except (OSError, ValueError):
        return None
    return count_tokens(_hydrate(raw), model)


def _build_rows(prompt_path: str, model: str) -> tuple[List[Dict], int]:
    """Return (rows, total_tokens) attributing tokens per source segment."""
    raw = Path(prompt_path).read_text(encoding="utf-8")
    total_tokens = count_tokens(_hydrate(raw), model)

    rows: List[Dict] = []
    attributed = 0
    for include_path in sorted(compute_user_intent_paths(raw)):
        tokens = _include_segment_tokens(include_path, model)
        if tokens is None:
            continue
        attributed += tokens
        rows.append({"source": include_path, "tokens": tokens})

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
    return rows, total_tokens


def _deferred_warnings(prompt_path: str) -> List[str]:
    """Warn about nondeterministic tags detected but not expanded."""
    raw = Path(prompt_path).read_text(encoding="utf-8")
    return [
        f"dynamic tag <{tag}> detected but not expanded (nondeterministic, deferred)"
        for tag in detect_dynamic_tags(raw)
    ]


def _percent(part: int, whole: Optional[int]) -> Optional[float]:
    if not whole:
        return None
    return round(part / whole * 100, 1)


@click.command("context-audit")
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
    help="Emit machine-readable JSON instead of the human-readable table.",
)
@click.option(
    "--threshold",
    type=click.IntRange(0, 100),
    default=80,
    show_default=True,
    help="Exit with code 2 when total tokens exceed N% of the context limit. 0 disables.",
)
@click.pass_context
def context_audit(
    ctx: click.Context,
    prompt_path: str,
    model: Optional[str],
    json_output: bool,
    threshold: int,
) -> None:
    """Audit token attribution by source for a preprocessed prompt."""

    try:
        resolved_model = model or os.environ.get("PDD_MODEL_DEFAULT") or "gpt-4o"

        rows, total_tokens = _build_rows(prompt_path, resolved_model)
        context_limit = get_context_limit(resolved_model)
        percent_used = _percent(total_tokens, context_limit)
        warnings = _deferred_warnings(prompt_path)

        threshold_exceeded = bool(
            threshold > 0
            and percent_used is not None
            and percent_used > threshold
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

        limit_text = f"{context_limit:,} tokens" if context_limit else "unknown"
        pct_text = f"{percent_used}%" if percent_used is not None else "unknown%"
        click.echo(f"Model: {resolved_model}  |  Context limit: {limit_text}")
        click.echo(f"Total tokens: {total_tokens:,}  ({pct_text} of context window)")
        click.echo("")
        click.echo(f"{'Source':<48}{'Tokens':>10}{'% of total':>14}")
        click.echo("-" * 72)
        for r in rows:
            row_pct = _percent(r["tokens"], total_tokens)
            pct_col = f"{row_pct}%" if row_pct is not None else "-"
            note = f"  (WARN: {r['note']})" if r.get("note") else ""
            click.echo(
                f"{r['source']:<48}{r['tokens']:>10,}{pct_col:>14}{note}"
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
        handle_error(exc, "context-audit", (ctx.obj or {}).get("quiet", False))
