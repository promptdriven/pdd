"""Automatic prompt quality gate configuration and workflow hooks."""
from __future__ import annotations

import logging
import sys
from pathlib import Path
from typing import Optional, Sequence

import click

from .checkup_prompt_main import (
    render_automatic_gate_summary,
    run_checkup_prompt_paths,
)
from .construct_paths import _find_pddrc_file, _load_pddrc_config
from .path_resolution import find_project_root_from_path

logger = logging.getLogger(__name__)

_PROMPT_GATE_MODES = frozenset({"off", "warn", "strict"})
_DEFAULT_MODE = "warn"
_PROMPT_GATE_BLOCKED_PREFIX = "Prompt checkup blocked"


def resolve_prompt_gate_project_root(
    prompt_paths: Sequence[Path | str],
    *,
    fallback: Optional[Path] = None,
) -> Path:
    """Resolve the PDD project root that anchors gate config and evidence.

    Anchors on the first prompt path so nested-repo / ``--project-root`` layouts
    resolve the gate against the prompt's own project rather than ``Path.cwd()``.
    Falls back to *fallback* (or the current working directory) when no project
    marker is found above the prompt.
    """
    base = (fallback or Path.cwd()).resolve()
    for raw in prompt_paths:
        if not raw:
            continue
        resolved = find_project_root_from_path(str(raw))
        if resolved:
            return Path(resolved).resolve()
        break
    return base


def prompt_gate_block_message(gate_exit: int) -> str:
    """Return the standard message when strict prompt checkup blocks a workflow."""
    return (
        f"{_PROMPT_GATE_BLOCKED_PREFIX} downstream change steps "
        f"(exit {gate_exit})."
    )


def parse_prompt_gate_block_exit(message: str) -> Optional[int]:
    """Return the gate exit code when *message* is a strict block message."""
    if not message.startswith(_PROMPT_GATE_BLOCKED_PREFIX):
        return None
    marker = "(exit "
    start = message.rfind(marker)
    if start == -1:
        return 2
    end = message.find(")", start)
    if end == -1:
        return 2
    try:
        return int(message[start + len(marker) : end])
    except ValueError:
        return 2


def _normalize_prompt_gate_mode(raw: object, *, source: str) -> Optional[str]:
    if raw is None:
        return None
    # PyYAML 1.1 maps off/no/false → False and on/yes/true → True.
    # Use isinstance to distinguish Python bools from integers (0 is not False by identity).
    if isinstance(raw, bool):
        if not raw:
            return "off"
        logger.warning(
            "checkup.prompt_gate value %r in %s is a boolean True; use 'off', 'warn', or 'strict'.",
            raw,
            source,
        )
        return None
    mode = str(raw).strip().lower()
    if mode not in _PROMPT_GATE_MODES:
        logger.warning(
            "Unknown checkup.prompt_gate value %r in %s; ignoring.",
            raw,
            source,
        )
        return None
    return mode


def load_prompt_gate_config(project_root: Path) -> str:
    """Load ``checkup.prompt_gate`` from ``.pddrc`` or ``pyproject.toml``."""
    root = project_root.resolve()

    pddrc = _find_pddrc_file(root)
    if pddrc is not None:
        try:
            config = _load_pddrc_config(pddrc)
        except (OSError, ValueError) as exc:
            logger.warning("Failed to load .pddrc for prompt gate: %s", exc)
        else:
            checkup = config.get("checkup", {})
            if isinstance(checkup, dict) and "prompt_gate" in checkup:
                mode = _normalize_prompt_gate_mode(
                    checkup.get("prompt_gate"),
                    source=str(pddrc),
                )
                if mode is not None:
                    return mode

    pyproject = root / "pyproject.toml"
    if pyproject.is_file():
        try:
            import tomllib

            data = tomllib.loads(pyproject.read_text(encoding="utf-8"))
        except (OSError, ValueError, ImportError):
            return _DEFAULT_MODE
        checkup = data.get("tool", {}).get("pdd", {}).get("checkup", {})
        if isinstance(checkup, dict) and "prompt_gate" in checkup:
            mode = _normalize_prompt_gate_mode(
                checkup.get("prompt_gate"),
                source=str(pyproject),
            )
            if mode is not None:
                return mode

    return _DEFAULT_MODE


def resolve_prompt_gate_mode(
    *,
    cli_prompt_checkup: Optional[str],
    no_prompt_checkup: bool,
    project_root: Path,
) -> str:
    """Resolve effective gate mode: CLI overrides config."""
    if no_prompt_checkup:
        return "off"
    if cli_prompt_checkup is not None:
        mode = cli_prompt_checkup.strip().lower()
        if mode not in {"warn", "strict"}:
            raise click.BadParameter(
                "--prompt-checkup must be 'warn' or 'strict'.",
                param_hint="'--prompt-checkup'",
            )
        return mode
    return load_prompt_gate_config(project_root)


def filter_changed_prompt_paths(paths: Sequence[str | Path]) -> list[Path]:
    """Keep only changed ``.prompt`` files, excluding ``*_LLM.prompt``."""
    prompt_paths: list[Path] = []
    for raw in paths:
        path = Path(raw)
        if path.suffix.lower() != ".prompt":
            continue
        if path.name.lower().endswith("_llm.prompt"):
            continue
        prompt_paths.append(path.resolve())
    return prompt_paths


def run_automatic_prompt_gate(
    prompt_paths: Sequence[Path],
    *,
    mode: str,
    project_root: Path,
    quiet: bool = False,
    strict: bool = False,
) -> tuple[bool, int]:
    """
    Run automatic prompt checkup on changed prompt files.

    Returns ``(should_continue, exit_code)``. ``should_continue`` is False only
    when ``mode == 'strict'`` and deterministic checks fail (errors, or warnings
    when strict evaluation is enabled).
    """
    if mode == "off" or not prompt_paths:
        return True, 0

    reports, exit_code = run_checkup_prompt_paths(
        prompt_paths,
        project_root=project_root,
        strict=strict or mode == "strict",
    )
    render_automatic_gate_summary(reports, mode=mode, quiet=quiet)

    if mode == "strict" and exit_code != 0:
        return False, exit_code
    return True, 0


def maybe_run_workflow_prompt_gate(
    changed_files: Sequence[str | Path],
    *,
    cli_prompt_checkup: Optional[str],
    no_prompt_checkup: bool,
    project_root: Path,
    quiet: bool = False,
    interactive: bool = False,
    apply: bool = False,
    dry_run: bool = False,
) -> tuple[bool, int]:
    """Shared hook for generate/change workflows that touch ``.prompt`` files."""
    prompt_paths = [
        path
        for path in filter_changed_prompt_paths(changed_files)
        if path.is_file()
    ]
    if not prompt_paths:
        return True, 0

    if apply and not interactive:
        raise click.UsageError("--apply requires --interactive.")

    if interactive:
        if not (sys.stdin.isatty() and sys.stdout.isatty()):
            raise click.UsageError(
                "--interactive requires a TTY (stdin and stdout must be a terminal)."
            )
        from .checkup_interactive_main import run_interactive_checkup  # pylint: disable=import-outside-toplevel

        gate_mode = resolve_prompt_gate_mode(
            cli_prompt_checkup=cli_prompt_checkup,
            no_prompt_checkup=no_prompt_checkup,
            project_root=project_root,
        )
        strict = gate_mode == "strict"
        for prompt_path in prompt_paths:
            try:
                run_interactive_checkup(
                    str(prompt_path),
                    apply=apply,
                    dry_run=dry_run,
                    project_root=project_root,
                    strict=strict,
                    quiet=quiet,
                    explicit_interactive=True,
                )
            except click.exceptions.Exit as exc:
                click.echo(
                    f"Interactive checkup stopped for {prompt_path.name} "
                    f"(exit {exc.exit_code}). "
                    "Check the output above for details.",
                    err=True,
                )
                return False, exc.exit_code
        return True, 0

    gate_mode = resolve_prompt_gate_mode(
        cli_prompt_checkup=cli_prompt_checkup,
        no_prompt_checkup=no_prompt_checkup,
        project_root=project_root,
    )
    return run_automatic_prompt_gate(
        prompt_paths,
        mode=gate_mode,
        project_root=project_root,
        quiet=quiet,
        strict=(gate_mode == "strict"),
    )
