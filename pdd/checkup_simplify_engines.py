"""Engine selection and invocation for ``pdd checkup simplify``."""
from __future__ import annotations

import os
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator, List, Optional, Sequence, Tuple

from .agentic_common import (
    DEFAULT_TIMEOUT_SECONDS,
    get_available_agents,
    run_agentic_task,
)
from .checkup_simplify_claude import (
    build_simplify_slash_message,
    check_claude_code_simplify_available,
    run_claude_simplify_command,
)

SIMPLIFY_ENGINES = frozenset({"claude", "codex", "gemini", "opencode", "auto"})
ENGINE_TO_AGENTIC_PROVIDER = {
    "codex": "openai",
    "gemini": "google",
    "opencode": "opencode",
}
_WORKFLOW_PROMPT_PATH = (
    Path(__file__).resolve().parent / "prompts" / "checkup_simplify_workflow_LLM.prompt"
)


def normalize_simplify_engine(engine: Optional[str], *, default: str = "claude") -> str:
    """Return a validated simplify engine name."""
    value = (engine or default).strip().lower()
    if value not in SIMPLIFY_ENGINES:
        allowed = ", ".join(sorted(SIMPLIFY_ENGINES))
        raise ValueError(f"Unknown simplify engine {engine!r}; expected one of: {allowed}")
    return value


def resolve_simplify_engine(engine: str) -> str:
    """Resolve ``auto`` to the first available concrete engine."""
    normalized = normalize_simplify_engine(engine)
    if normalized != "auto":
        return normalized

    if check_claude_code_simplify_available(quiet=True)[2] is None:
        return "claude"

    available = set(get_available_agents())
    for candidate, provider in (
        ("codex", "openai"),
        ("gemini", "google"),
        ("opencode", "opencode"),
    ):
        if provider in available:
            return candidate
    return "claude"


def _read_workflow_prompt() -> str:
    lines: List[str] = []
    for line in _WORKFLOW_PROMPT_PATH.read_text(encoding="utf-8").splitlines():
        if line.strip().startswith("%"):
            continue
        lines.append(line)
    return "\n".join(lines).strip()


def build_agentic_simplify_instruction(
    rel_files: Sequence[str],
    *,
    focus: str,
) -> str:
    """Build a provider-agnostic simplify instruction from the packaged workflow prompt."""
    parts = [
        _read_workflow_prompt(),
        "",
        "## In-scope files (edit only these paths)",
        *[f"- {path}" for path in rel_files],
    ]
    focus_text = focus.strip()
    if focus_text:
        parts.extend(["", f"## Focus: {focus_text}"])
    parts.extend(
        [
            "",
            "Apply edits directly in the current working tree.",
            "Respond with a concise summary of what you changed.",
        ]
    )
    return "\n".join(parts)


def build_simplify_command_repr(
    engine: str,
    rel_files: Sequence[str],
    *,
    focus: str,
) -> str:
    """Human-readable command representation for summaries and evidence."""
    if engine == "claude":
        return build_simplify_slash_message(rel_files, focus=focus)
    return f"agentic-simplify ({engine})"


@contextmanager
def _forced_agentic_provider(provider: str) -> Iterator[None]:
    old_value = os.environ.get("PDD_AGENTIC_PROVIDER")
    os.environ["PDD_AGENTIC_PROVIDER"] = provider
    try:
        yield
    finally:
        if old_value is None:
            os.environ.pop("PDD_AGENTIC_PROVIDER", None)
        else:
            os.environ["PDD_AGENTIC_PROVIDER"] = old_value


def check_simplify_engine_available(
    engine: str,
    *,
    quiet: bool,
) -> Tuple[str, str, Optional[str]]:
    """Return ``(version_label, provider_name, error_message)`` for an engine."""
    resolved = resolve_simplify_engine(engine)
    if resolved == "claude":
        _cli_path, version_tuple, error = check_claude_code_simplify_available(quiet=quiet)
        if error:
            return "", "claude", error
        if version_tuple is None:
            return "", "claude", "Could not parse Claude Code version"
        version_label = f"{version_tuple[0]}.{version_tuple[1]}.{version_tuple[2]}"
        return version_label, "claude", None

    provider = ENGINE_TO_AGENTIC_PROVIDER[resolved]
    if provider not in get_available_agents():
        return (
            "",
            provider,
            (
                f"No available agent for simplify engine {resolved!r}. "
                f"Install/auth the {resolved} CLI or set PDD_AGENTIC_PROVIDER."
            ),
        )
    return resolved, provider, None


def run_simplify_engine_command(  # pylint: disable=too-many-arguments,too-many-locals
    engine: str,
    rel_files: Sequence[str],
    repo_root: Path,
    *,
    focus: str,
    verbose: bool,
    quiet: bool,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
) -> Tuple[bool, str, float, str]:
    """Run simplify for ``engine`` and return ``(success, summary, cost, provider)``."""
    resolved = resolve_simplify_engine(engine)
    if resolved == "claude":
        cli_path, _version_tuple, error = check_claude_code_simplify_available(quiet=quiet)
        if error:
            return False, error, 0.0, "claude"
        assert cli_path is not None
        slash_message = build_simplify_slash_message(rel_files, focus=focus)
        success, summary, cost, _ = run_claude_simplify_command(
            slash_message,
            repo_root,
            cli_path=cli_path,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
        )
        return success, summary, cost, "claude"

    provider = ENGINE_TO_AGENTIC_PROVIDER[resolved]
    instruction = build_agentic_simplify_instruction(rel_files, focus=focus)
    with _forced_agentic_provider(provider):
        success, summary, cost, provider_used = run_agentic_task(
            instruction,
            repo_root,
            verbose=verbose,
            quiet=quiet,
            label=f"checkup-simplify-{resolved}",
            timeout=timeout,
        )
    return success, summary or "", cost, provider_used or provider
