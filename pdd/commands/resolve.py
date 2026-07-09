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

Deliberately self-contained: classification reuses ``sync_determine_operation``'s
own changed-artifact primitive (so the CONFLICT definition — prompt-side AND
derived-side both moved vs the stored fingerprint — matches the sync decision
path exactly), and stamping uses the shared runtime ``save_fingerprint`` writer.
It does NOT depend on ``continuous_sync``/``reconcile`` (owned by the sibling
#1927 effort); any overlap with ``reconcile --accept-current`` is consolidated at
merge.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import click

from ..operation_log import get_fingerprint_path, save_fingerprint
from ..sync_determine_operation import (
    Fingerprint,
    _changed_artifacts_from_hashes,
    calculate_current_hashes,
    get_pdd_file_paths,
    read_fingerprint,
)

# Fingerprint commands treated as "settled" workflow states. Preserving one of
# these (rather than resetting to a running op) keeps a stamped baseline from
# re-triggering verify/test on the next sync.
_SETTLED_COMMANDS = {"verify", "test", "fix", "update"}


def _resolve_paths(basename: str, language: str) -> Optional[Dict[str, Path]]:
    """Resolve the unit's artifact paths (or None if resolution fails)."""
    try:
        return get_pdd_file_paths(basename, language, prompts_dir="prompts")
    except Exception:  # pylint: disable=broad-except
        return None


def _classify(
    basename: str,
    language: str,
    paths: Dict[str, Path],
) -> Tuple[Optional[Fingerprint], List[str], str]:
    """Classify the unit against its stored fingerprint without mutating anything.

    Returns ``(fingerprint, changed_artifacts, classification)``. CONFLICT means
    the prompt AND at least one derived artifact both moved vs the fingerprint —
    identical to the both-changed trigger in ``_prompt_derived_conflict_decision``.
    """
    fingerprint = read_fingerprint(basename, language, paths=paths)
    if fingerprint is None:
        return None, [], "UNBASELINED"
    current = calculate_current_hashes(paths, stored_include_deps=fingerprint.include_deps)
    changes = _changed_artifacts_from_hashes(fingerprint, paths, current)
    derived = [item for item in changes if item != "prompt"]
    if not changes:
        classification = "IN_SYNC"
    elif "prompt" in changes and derived:
        classification = "CONFLICT"
    else:
        classification = "DRIFT"
    return fingerprint, changes, classification


def _accept_current(
    basename: str,
    language: str,
    paths: Dict[str, Path],
    as_json: bool,
    quiet: bool,
) -> int:
    """Stamp the current tree as the agreed baseline for the unit.

    Transactional at the command level: it re-fingerprints, then re-classifies and
    only reports success when the unit lands IN_SYNC. Any other post-state is
    surfaced as a failure rather than a silent partial stamp.
    """
    before_fp, before_changes, before_class = _classify(basename, language, paths)
    command = (
        before_fp.command
        if before_fp is not None and before_fp.command in _SETTLED_COMMANDS
        else "fix"
    )
    save_fingerprint(basename, language, command, paths, 0.0, "resolve")
    _after_fp, _after_changes, after_class = _classify(basename, language, paths)

    resolved = after_class == "IN_SYNC"
    result = {
        "basename": basename,
        "language": language,
        "strategy": "accept-current",
        "before": before_class,
        "after": after_class,
        "changed_files": before_changes,
        "fingerprint_path": str(get_fingerprint_path(basename, language, paths=paths)),
        "resolved": resolved,
    }
    if as_json:
        click.echo(json.dumps(result, indent=2, sort_keys=True))
    elif not quiet:
        if resolved:
            moved = ", ".join(before_changes) or "no tracked"
            click.echo(
                f"Resolved '{basename}' ({language}) with --accept-current: "
                f"stamped the current tree as the new baseline "
                f"(was {before_class}: {moved} changed)."
            )
        else:
            click.echo(
                f"Could not fully resolve '{basename}' ({language}): after stamping "
                f"it is {after_class}, not IN_SYNC. Ensure the prompt and its derived "
                f"artifacts all exist on disk, then retry."
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

    paths = _resolve_paths(basename, language)
    if paths is None or (
        read_fingerprint(basename, language, paths=paths) is None
        and not paths["prompt"].exists()
    ):
        raise click.ClickException(
            f"No PDD unit '{basename}' ({language}) found to resolve. "
            f"Run `pdd sync` to see tracked units."
        )
    raise click.exceptions.Exit(
        _accept_current(basename, language, paths, as_json, quiet)
    )
