"""`pdd resolve` — resolve a both-changed CONFLICT unit.

A CONFLICT arises when a unit's prompt AND one or more derived artifacts (code,
example, test) both changed since the last synced fingerprint. `pdd sync` refuses
to auto-pick a winner there (see ``sync_determine_operation`` #1929); this command
lets the user finalize the resolution explicitly:

* ``--accept-current`` — deterministic, no LLM. Stamp the current working tree as
  the agreed baseline for the unit (re-fingerprint), so the co-edited prompt and
  code are recorded as the new last-synced ancestor. Use this after hand-merging.
* ``--prompt-wins`` / ``--code-wins`` — documented previews of the LLM-backed
  strategies (regenerate code from the prompt / back-propagate code into the
  prompt). These are not yet automated; they print what WOULD run and exit
  non-zero.
"""
from __future__ import annotations

import json
from typing import Dict, Optional

import click

from ..continuous_sync import SyncUnit, classify_unit, discover_units, project_root
from ..operation_log import save_fingerprint
from ..sync_determine_operation import get_pdd_file_paths, read_fingerprint

# Fingerprint commands treated as "settled" workflow states. Preserving one of
# these (rather than resetting to a running op) keeps a stamped baseline from
# re-triggering verify/test on the next sync — mirrors continuous_sync._heal_units.
_SETTLED_COMMANDS = {"verify", "test", "fix", "update"}


def _find_unit(basename: str, language: str) -> Optional[SyncUnit]:
    """Locate the discovered sync unit for ``basename``/``language`` (or None)."""
    base = project_root()
    for unit in discover_units(base, modules=[basename]):
        if unit.language == language and unit.basename == basename:
            return unit
    # Fall back to a language-only match (basename may be path-qualified/aliased).
    for unit in discover_units(base, modules=[basename]):
        if unit.language == language:
            return unit
    return None


def _baseline_command(basename: str, language: str, paths: Dict) -> str:
    """Command to record on the accepted baseline fingerprint."""
    fingerprint = read_fingerprint(basename, language, paths=paths)
    if fingerprint and fingerprint.command in _SETTLED_COMMANDS:
        return fingerprint.command
    return "fix"


def _accept_current(unit: SyncUnit, as_json: bool, quiet: bool) -> int:
    """Stamp the current tree as the agreed baseline for ``unit``.

    Transactional at the command level: it re-fingerprints, then re-classifies
    and only reports success when the unit lands IN_SYNC. Any other post-state is
    surfaced as a failure rather than a silent partial stamp.
    """
    base = project_root()
    before = classify_unit(unit, base)
    paths = get_pdd_file_paths(
        unit.basename, unit.language, prompts_dir=str(unit.prompts_dir)
    )
    command = _baseline_command(unit.basename, unit.language, paths)
    save_fingerprint(unit.basename, unit.language, command, paths, 0.0, "resolve")
    after = classify_unit(unit, base)

    resolved = after["classification"] == "IN_SYNC"
    result = {
        "basename": unit.basename,
        "language": unit.language,
        "strategy": "accept-current",
        "before": before["classification"],
        "after": after["classification"],
        "changed_files": before.get("changed_files", []),
        "fingerprint_path": after.get("fingerprint_path"),
        "resolved": resolved,
    }
    if as_json:
        click.echo(json.dumps(result, indent=2, sort_keys=True))
    elif not quiet:
        if resolved:
            moved = ", ".join(before.get("changed_files", [])) or "no tracked"
            click.echo(
                f"Resolved '{unit.basename}' ({unit.language}) with --accept-current: "
                f"stamped the current tree as the new baseline "
                f"(was {before['classification']}: {moved} changed)."
            )
        else:
            click.echo(
                f"Could not fully resolve '{unit.basename}' ({unit.language}): "
                f"after stamping it is {after['classification']}, not IN_SYNC. "
                f"Ensure the prompt and its derived artifacts all exist on disk, "
                f"then retry."
            )
    return 0 if resolved else 1


def _preview_llm_strategy(basename: str, language: str, strategy: str) -> int:
    """Print what a not-yet-automated LLM strategy WOULD run; return non-zero."""
    suffix = "" if language.lower() == "python" else f" --language {language}"
    if strategy == "prompt-wins":
        would_run = f"pdd sync {basename}{suffix}"
        effect = "regenerate the code from the prompt (an LLM generation)"
    else:  # code-wins
        would_run = f"pdd update {basename}{suffix}"
        effect = "back-propagate the code into the prompt (an LLM update)"
    click.echo(
        f"--{strategy} would run `{would_run}` to {effect}, then re-stamp the "
        f"fingerprint. This LLM-backed strategy is not yet automated by "
        f"`pdd resolve`."
    )
    click.echo(
        "Run that command yourself, or use "
        f"`pdd resolve {basename}{suffix} --accept-current` to keep the current "
        "tree as the baseline."
    )
    return 2


@click.command("resolve")
@click.argument("basename")
@click.option(
    "--language",
    default="python",
    show_default=True,
    help="Language of the unit to resolve.",
)
@click.option(
    "--accept-current",
    "accept_current",
    is_flag=True,
    default=False,
    help="Stamp the current tree as the agreed baseline (deterministic, no LLM).",
)
@click.option(
    "--prompt-wins",
    "prompt_wins",
    is_flag=True,
    default=False,
    help="[preview] Regenerate code from the prompt (not yet automated).",
)
@click.option(
    "--code-wins",
    "code_wins",
    is_flag=True,
    default=False,
    help="[preview] Back-propagate code into the prompt (not yet automated).",
)
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Emit machine-readable JSON.",
)
@click.pass_context
def resolve(
    ctx: click.Context,
    basename: str,
    language: str,
    accept_current: bool,
    prompt_wins: bool,
    code_wins: bool,
    as_json: bool,
) -> None:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Resolve a CONFLICT unit (prompt and code both changed since last sync).

    Choose exactly one strategy: --accept-current keeps the current files as the
    new baseline; --prompt-wins / --code-wins preview the LLM strategies.
    """
    ctx.ensure_object(dict)
    if as_json:
        ctx.obj["_suppress_result_summary"] = True
    quiet = ctx.obj.get("quiet", False)

    chosen = [
        name
        for name, flag in (
            ("--accept-current", accept_current),
            ("--prompt-wins", prompt_wins),
            ("--code-wins", code_wins),
        )
        if flag
    ]
    if len(chosen) != 1:
        raise click.UsageError(
            "Choose exactly one of --accept-current, --prompt-wins, --code-wins."
        )

    if prompt_wins:
        raise click.exceptions.Exit(
            _preview_llm_strategy(basename, language, "prompt-wins")
        )
    if code_wins:
        raise click.exceptions.Exit(
            _preview_llm_strategy(basename, language, "code-wins")
        )

    unit = _find_unit(basename, language)
    if unit is None:
        raise click.ClickException(
            f"No PDD unit '{basename}' ({language}) found to resolve. "
            f"Run `pdd sync` or `pdd reconcile` to see tracked units."
        )
    raise click.exceptions.Exit(_accept_current(unit, as_json, quiet))
