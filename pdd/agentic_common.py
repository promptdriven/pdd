from __future__ import annotations

import os
import shutil
import subprocess
import time
import uuid
from pathlib import Path
from typing import Any, Dict, List, Tuple

from rich.console import Console

from .llm_invoke import _load_model_data, LLM_MODEL_CSV_PATH

console = Console()

# Providers are tried in this order by run_agentic_task.
AGENT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai"]

# Mapping from provider name to its CLI binary.
_PROVIDER_CLI_BINARIES: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
}

# Environment variables that can satisfy "API key configured" for each provider.
_PROVIDER_API_ENV_VARS: Dict[str, List[str]] = {
    "anthropic": ["ANTHROPIC_API_KEY"],
    "google": ["GOOGLE_API_KEY", "GEMINI_API_KEY"],
    "openai": ["OPENAI_API_KEY"],
}

# Cached result of _load_model_data so we don't repeatedly hit disk.
_MODEL_DATA: Any | None = None
_MODEL_DATA_LOAD_ERROR: Exception | None = None


# ---------------------------------------------------------------------------
# Logging utilities (rich-based, controlled by verbose/quiet flags)
# ---------------------------------------------------------------------------


def log_info(message: str, *, verbose: bool, quiet: bool) -> None:
    """
    Log a normal informational message.

    Respects the caller's verbosity settings:
    - Suppressed when quiet is True.
    - Shown regardless of verbose when quiet is False.
    """
    if quiet:
        return
    console.print(message)


def log_debug(message: str, *, verbose: bool, quiet: bool) -> None:
    """
    Log a debug/verbose message.

    Only shown when verbose is True and quiet is False.
    """
    if quiet or not verbose:
        return
    console.print(message, style="dim")


def log_error(message: str, *, verbose: bool, quiet: bool) -> None:
    """
    Log an error message.

    Errors are always shown, even when quiet is True.
    """
    console.print(message, style="bold red")


# ---------------------------------------------------------------------------
# Provider / environment helpers
# ---------------------------------------------------------------------------


def _ensure_model_data_loaded(*, verbose: bool, quiet: bool) -> bool:
    """
    Ensure model metadata has been loaded via _load_model_data.

    Returns:
        True if metadata was loaded successfully, False otherwise.
    """
    global _MODEL_DATA, _MODEL_DATA_LOAD_ERROR

    if _MODEL_DATA is not None:
        return True
    if _MODEL_DATA_LOAD_ERROR is not None:
        return False

    try:
        _MODEL_DATA = _load_model_data(LLM_MODEL_CSV_PATH)
        return True
    except Exception as exc:  # pragma: no cover - defensive
        _MODEL_DATA_LOAD_ERROR = exc
        log_debug(
            f"Failed to load LLM model metadata via _load_model_data: {exc}",
            verbose=verbose,
            quiet=quiet,
        )
        return False


def _is_cli_available(provider: str) -> bool:
    """
    Check whether the CLI binary for a provider is available on PATH.
    """
    binary = _PROVIDER_CLI_BINARIES.get(provider)
    if not binary:
        return False
    return shutil.which(binary) is not None


def _is_provider_api_configured(provider: str, *, verbose: bool, quiet: bool) -> bool:
    """
    Check whether an API key is configured for the given provider.

    This requires both:
    - Successful model metadata load via _load_model_data; and
    - Presence of at least one known API key environment variable.
    """
    if not _ensure_model_data_loaded(verbose=verbose, quiet=quiet):
        return False

    env_vars = _PROVIDER_API_ENV_VARS.get(provider, [])
    return any(os.getenv(name) for name in env_vars)


def _is_provider_available(provider: str, *, verbose: bool, quiet: bool) -> bool:
    """
    Determine if a provider is usable (CLI present AND API configured).
    """
    if not _is_cli_available(provider):
        binary = _PROVIDER_CLI_BINARIES.get(provider, "?")
        log_debug(
            f"Skipping provider '{provider}': CLI binary '{binary}' not found on PATH.",
            verbose=verbose,
            quiet=quiet,
        )
        return False

    if not _is_provider_api_configured(provider, verbose=verbose, quiet=quiet):
        log_debug(
            f"Skipping provider '{provider}': API key environment variable not configured.",
            verbose=verbose,
            quiet=quiet,
        )
        return False

    return True


def _build_agentic_instruction(prompt_file: Path) -> str:
    """
    Build the agentic instruction string pointing at the prompt file.
    """
    return (
        f"Read the file {prompt_file} for instructions. "
        "You have full file access to explore and modify files as needed."
    )


def _build_command_for_provider(provider: str, instruction: str) -> List[str]:
    """
    Build the CLI command for the given provider in agentic mode.

    The commands intentionally avoid:
    - Anthropic/Google: any `-p` (print mode) flag.
    - OpenAI: `--sandbox read-only` (we want full file access).
    """
    if provider == "anthropic":
        return ["claude", "--dangerously-skip-permissions", instruction]
    if provider == "google":
        return ["gemini", instruction]
    if provider == "openai":
        return ["codex", "exec", instruction]
    raise ValueError(f"Unsupported provider: {provider}")


def _build_sanitized_env() -> Dict[str, str]:
    """
    Build a sanitized environment for non-interactive subprocess execution.
    """
    env: Dict[str, str] = dict(os.environ)
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    return env


def _get_cost_per_call() -> float:
    """
    Read the per-call cost estimate from the environment.

    Environment:
        PDD_AGENTIC_COST_PER_CALL: cost per call (default: 0.02)
    """
    raw = os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02")
    try:
        return float(raw)
    except ValueError:  # pragma: no cover - defensive
        return 0.02


def _get_timeout_seconds() -> float:
    """
    Read the CLI timeout in seconds from the environment.

    Environment:
        PDD_AGENTIC_TIMEOUT: timeout in seconds (default: 240)
    """
    raw = os.getenv("PDD_AGENTIC_TIMEOUT", "240")
    try:
        return float(raw)
    except ValueError:  # pragma: no cover - defensive
        return 240.0


def _safe_unlink(path: Path, *, verbose: bool, quiet: bool) -> None:
    """
    Best-effort removal of a file, logging only in verbose mode on failure.
    """
    try:
        path.unlink(missing_ok=True)
    except Exception as exc:  # pragma: no cover - defensive
        log_debug(
            f"Failed to remove temporary prompt file '{path}': {exc}",
            verbose=verbose,
            quiet=quiet,
        )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def get_available_agents() -> List[str]:
    """
    Return a list of provider names that are currently available.

    A provider is considered available when BOTH:
      * Its CLI binary is present on PATH, and
      * Model metadata can be loaded via `_load_model_data`, and
      * At least one of its associated API key env vars is set.
    """
    available: List[str] = []
    for provider in AGENT_PROVIDER_PREFERENCE:
        if _is_provider_available(provider, verbose=False, quiet=True):
            available.append(provider)
    return available


def run_agentic_task(
    instruction: str,
    cwd: Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
    label: str = "",
) -> Tuple[bool, str, float, str]:
    """
    Run an agentic task using CLI-based agents.

    The function tries providers in AGENT_PROVIDER_PREFERENCE order and returns
    on the first successful run. Providers are only attempted if their CLI
    binary is available and an API key is configured.

    Args:
        instruction: Natural-language instruction for the agent.
        cwd: Working directory in which the CLI should be executed.
        verbose: Enable verbose logging if True.
        quiet: Suppress non-essential logging if True (errors still shown).
        label: Optional label to prefix log lines (e.g., task id).

    Returns:
        Tuple[success, output, cost, provider_used]:
            success:
                True if an agent completed successfully (exit code == 0).
            output:
                Combined stdout/stderr from the provider CLI, or an error
                message if no provider completed successfully.
            cost:
                Estimated cost, computed as
                PDD_AGENTIC_COST_PER_CALL * number_of_attempted_invocations.
            provider_used:
                Name of the provider that produced `output`, or the last
                attempted provider when all fail, or "" if none were attempted.
    """
    prefix = f"[{label}] " if label else ""

    # Basic input validation.
    if not instruction.strip():
        message = f"{prefix}No instruction provided for agentic task."
        log_error(message, verbose=verbose, quiet=quiet)
        return False, message, 0.0, ""

    if not cwd.exists() or not cwd.is_dir():
        message = f"{prefix}Working directory does not exist or is not a directory: {cwd}"
        log_error(message, verbose=verbose, quiet=quiet)
        return False, message, 0.0, ""

    cost_per_call = _get_cost_per_call()
    timeout = _get_timeout_seconds()
    env = _build_sanitized_env()

    attempts = 0
    last_provider: str = ""

    for provider in AGENT_PROVIDER_PREFERENCE:
        if not _is_provider_available(provider, verbose=verbose, quiet=quiet):
            continue

        last_provider = provider
        attempts += 1

        prompt_file = cwd / f".agentic_prompt_{uuid.uuid4().hex}.txt"
        try:
            prompt_file.write_text(instruction, encoding="utf-8")
        except Exception as exc:  # pragma: no cover - defensive
            message = (
                f"{prefix}Failed to write agentic prompt file '{prompt_file}': {exc}"
            )
            log_error(message, verbose=verbose, quiet=quiet)
            # Even though the CLI was not invoked, we count this as an attempt
            # against the chosen provider.
            return False, message, attempts * cost_per_call, provider

        agentic_instruction = _build_agentic_instruction(prompt_file)
        cmd = _build_command_for_provider(provider, agentic_instruction)

        log_info(
            f"{prefix}Invoking {provider} agent via CLI: {' '.join(cmd)}",
            verbose=verbose,
            quiet=quiet,
        )

        start_time = time.monotonic()
        try:
            result = subprocess.run(
                cmd,
                cwd=str(cwd),
                env=env,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            _safe_unlink(prompt_file, verbose=verbose, quiet=quiet)
            elapsed = time.monotonic() - start_time
            message = (
                f"{prefix}Agent provider '{provider}' timed out after "
                f"{elapsed:.1f}s (timeout={timeout:.0f}s)."
            )
            log_error(message, verbose=verbose, quiet=quiet)
            # Try the next provider, if any.
            continue
        except Exception as exc:  # pragma: no cover - defensive
            _safe_unlink(prompt_file, verbose=verbose, quiet=quiet)
            message = f"{prefix}Error while running provider '{provider}': {exc}"
            log_error(message, verbose=verbose, quiet=quiet)
            # Try the next provider, if any.
            continue
        finally:
            _safe_unlink(prompt_file, verbose=verbose, quiet=quiet)

        elapsed = time.monotonic() - start_time
        combined_output = (result.stdout or "") + (
            ("\n" + result.stderr) if result.stderr else ""
        )

        if result.returncode == 0:
            log_info(
                f"{prefix}Agent provider '{provider}' completed successfully "
                f"in {elapsed:.1f}s.",
                verbose=verbose,
                quiet=quiet,
            )
            return True, combined_output, attempts * cost_per_call, provider

        # Non-zero exit code: log and fall back to the next provider.
        message = (
            f"{prefix}Agent provider '{provider}' exited with code "
            f"{result.returncode} after {elapsed:.1f}s."
        )
        log_error(message, verbose=verbose, quiet=quiet)
        log_debug(
            f"{prefix}Output from '{provider}':\n{combined_output}",
            verbose=verbose,
            quiet=quiet,
        )

    # If we reach here, no provider could complete the task successfully.
    if attempts == 0:
        message = (
            f"{prefix}No available agents. Ensure that at least one of "
            f"{AGENT_PROVIDER_PREFERENCE} has its CLI installed and API key configured."
        )
        provider_used = ""
    else:
        message = (
            f"{prefix}All configured agent providers failed to complete the task."
        )
        provider_used = last_provider

    log_error(message, verbose=verbose, quiet=quiet)
    return False, message, attempts * cost_per_call, provider_used
