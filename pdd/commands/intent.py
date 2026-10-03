"""`pdd intent` command group for local ordinary-language intent planning."""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Optional

import click

from ..intent import build_intent_plan, intent_plan_to_dict, render_review_card

_MAX_INTENT_CHARS = 100_000


def _read_intent_source(
    source: Optional[Path], inline_text: Optional[str]
) -> tuple[str, str, Optional[str]]:
    if source is not None and inline_text is not None:
        raise click.ClickException("Use either SOURCE or --text, not both.")

    if inline_text is not None:
        request = inline_text
        source_kind = "inline"
        source_ref = None
    elif source is not None:
        if not source.is_file():
            raise click.ClickException(f"Intent source is not a file: {source}")
        try:
            request = source.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            raise click.ClickException(f"Could not read intent source {source}: {exc}") from exc
        source_kind = "file"
        source_ref = str(source.resolve())
    elif not sys.stdin.isatty():
        request = click.get_text_stream("stdin").read()
        source_kind = "stdin"
        source_ref = "<stdin>"
    else:
        raise click.ClickException(
            "Provide a local SOURCE file, pass --text, or pipe the request on standard input."
        )

    if not request.strip():
        raise click.ClickException("Intent request must not be empty.")
    if len(request) > _MAX_INTENT_CHARS:
        raise click.ClickException(
            f"Intent request exceeds the {_MAX_INTENT_CHARS:,}-character planning limit."
        )
    return request, source_kind, source_ref


@click.group(name="intent")
def intent() -> None:
    """Accept ordinary product intent and determine the appropriate PDD route."""


@intent.command("plan")
@click.argument(
    "source",
    required=False,
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
)
@click.option("--text", "inline_text", default=None, help="Ordinary-language request.")
@click.option("--title", default=None, help="Optional human-readable intent title.")
@click.option(
    "--project-root",
    default=".",
    type=click.Path(file_okay=False, path_type=Path),
    help="Existing or proposed project scope. Defaults to the current directory.",
)
@click.option("--json", "as_json", is_flag=True, help="Emit structured agent output.")
def plan_intent(
    source: Optional[Path],
    inline_text: Optional[str],
    title: Optional[str],
    project_root: Path,
    as_json: bool,
) -> None:
    """Plan local product intent without GitHub, model calls, or file changes."""
    request, source_kind, source_ref = _read_intent_source(source, inline_text)
    try:
        plan = build_intent_plan(
            request,
            project_root,
            title=title,
            source_kind=source_kind,
            source_ref=source_ref,
        )
    except ValueError as exc:
        raise click.ClickException(str(exc)) from exc

    if as_json:
        click.echo(json.dumps(intent_plan_to_dict(plan), indent=2, sort_keys=True))
    else:
        click.echo(render_review_card(plan))


intent_cli = intent
