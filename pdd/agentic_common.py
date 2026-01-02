# pdd/agentic_common.py
from __future__ import annotations

import json
import os
import secrets
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Mapping, MutableMapping, Optional, Tuple

from rich.console import Console

from .llm_invoke import LLM_MODEL_CSV_PATH, _load_model_data

console = Console()

AGENT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai"]

# CLI command mapping for each provider
CLI_COMMANDS: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
}

# Timeouts
DEFAULT_TIMEOUT_SECONDS: float = 240.0
TIMEOUT_ENV_VAR: str = "PDD_AGENTIC_TIMEOUT"


@dataclass(frozen=True)
class TokenPricing:
    """
    Simple per-token pricing descriptor.

    Prices are expressed in USD per 1,000,000 tokens.
    cached_input_multiplier is the fraction of full input price charged
    for cached tokens (e.g. 0.25 == 75% discount).
    """

    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 1.0


# Approximate Gemini pricing by model family.
# These values can be refined if needed; they are only used when the
# provider returns token counts instead of a direct USD cost.
GEMINI_PRICING_BY_FAMILY: Dict[str, TokenPricing] = {
    "flash": TokenPricing(input_per_million=0.35, output_per_million=1.05, cached_input_multiplier=0.5),
    "pro": TokenPricing(input_per_million=3.50, output_per_million=10.50, cached_input_multiplier=0.5),
    "default": TokenPricing(input_per_million=0.35, output_per_million=1.05, cached_input_multiplier=0.5),
}

# Codex/OpenAI pricing (explicitly provided in prompt)
CODEX_PRICING: TokenPricing = TokenPricing(
    input_per_million=1.50,
    output_per_million=6.00,
    cached_input_multiplier=0.25,  # 75% discount for cached tokens
)


# ---------------------------------------------------------------------------
# Logging utilities (Rich-based, respect verbose/quiet flags)
# ---------------------------------------------------------------------------


def _format_label(label: str) -> str:
    return f"[{label}] " if label else ""


def log_info(message: str, *, verbose: bool, quiet: bool, label: str = "") -> None:
    """
    Log an informational message.

    Skips output when quiet=True.
    """
    if quiet:
        return
    prefix = _format_label(label)
    console.print(f"{prefix}{message}")


def log_debug(message: str, *, verbose: bool, quiet: bool, label: str = "") -> None:
    """
    Log a debug message.

    Only emits output when verbose=True and quiet=False.
    """
    if quiet or not verbose:
        return
    prefix = _format_label(label)
    console.log(f"{prefix}{message}")


def log_error(message: str, *, verbose: bool, quiet: bool, label: str = "") -> None:
    """
    Log an error message.

    Errors are always printed, even in quiet mode.
    """
    prefix = _format_label(label)
    console.print(f"[red]{prefix}{message}[/red]")


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------


def _safe_load_model_data() -> Any | None:
    """
    Best-effort wrapper around _load_model_data.

    This is used as part of provider availability checks so that we
    respect whatever configuration llm_invoke is using (including
    any API-key related metadata encoded in the model CSV).
    """
    try:
        return _load_model_data(LLM_MODEL_CSV_PATH)
    except Exception:
        return None


def _provider_has_api_key(provider: str, model_data: Any | None) -> bool:
    """
    Determine whether the given provider has an API key or CLI auth configured.

    This function:
    - For Anthropic: Also checks if Claude CLI is available (subscription auth)
      which doesn't require an API key.
    - Attempts to infer API-key environment variable names from the
      llm_invoke model data (if it is a DataFrame-like object).
    - Falls back to well-known default environment variable names.

    The actual presence of API keys is checked via os.environ.
    """
    env = os.environ

    # For Anthropic: Check if Claude CLI is available for subscription auth
    # This is more robust as it uses the user's Claude subscription instead of API credits
    if provider == "anthropic":
        if shutil.which("claude"):
            # Claude CLI is available - we can use subscription auth
            # even without an API key
            return True

    # Try to extract env var hints from model_data, if it looks like a DataFrame.
    inferred_env_vars: List[str] = []
    if model_data is not None:
        try:
            columns = list(getattr(model_data, "columns", []))
            if "provider" in columns:
                # DataFrame-like path
                try:
                    df = model_data  # type: ignore[assignment]
                    # Filter rows matching provider name (case-insensitive)
                    provider_mask = df["provider"].str.lower() == provider.lower()  # type: ignore[index]
                    provider_rows = df[provider_mask]
                    # Look for any column that might specify an API-key env var
                    candidate_cols = [
                        c
                        for c in columns
                        if "api" in c.lower() and "key" in c.lower() or "env" in c.lower()
                    ]
                    for _, row in provider_rows.iterrows():  # type: ignore[attr-defined]
                        for col in candidate_cols:
                            value = str(row.get(col, "")).strip()
                            # Heuristic: looks like an env var name (upper & contains underscore)
                            if value and value.upper() == value and "_" in value:
                                inferred_env_vars.append(value)
                except Exception:
                    # If anything above fails, we silently fall back to defaults.
                    pass
        except Exception:
            pass

    default_env_map: Dict[str, List[str]] = {
        "anthropic": ["ANTHROPIC_API_KEY"],
        "google": ["GEMINI_API_KEY", "GOOGLE_API_KEY"],
        "openai": ["OPENAI_API_KEY"],
    }

    env_candidates = inferred_env_vars or default_env_map.get(provider, [])
    return any(env.get(name) for name in env_candidates)


def _get_agent_timeout() -> float:
    """
    Resolve the agentic subprocess timeout from environment, with a sane default.
    """
    raw = os.getenv(TIMEOUT_ENV_VAR)
    if not raw:
        return DEFAULT_TIMEOUT_SECONDS
    try:
        value = float(raw)
        if value <= 0:
            raise ValueError
        return value
    except ValueError:
        return DEFAULT_TIMEOUT_SECONDS


def _build_subprocess_env(
    base: Optional[Mapping[str, str]] = None,
    *,
    use_cli_auth: bool = False,
) -> Dict[str, str]:
    """
    Build a sanitized environment for non-interactive subprocess execution.

    Ensures:
      - TERM=dumb
      - NO_COLOR=1
      - CI=1
    while preserving existing variables (including API keys).

    Args:
        base: Optional base environment mapping (defaults to os.environ).
        use_cli_auth: If True, remove ANTHROPIC_API_KEY to force Claude CLI
                      subscription auth instead of API key auth. This is more
                      robust as it uses the user's Claude subscription.
    """
    env: Dict[str, str] = dict(base or os.environ)
    env.setdefault("TERM", "dumb")
    env.setdefault("NO_COLOR", "1")
    env.setdefault("CI", "1")

    if use_cli_auth:
        # Remove API key to force Claude CLI subscription auth
        env.pop("ANTHROPIC_API_KEY", None)

    return env


def _build_provider_command(
    provider: str,
    instruction: str,
    *,
    use_interactive_mode: bool = False,
) -> List[str]:
    """
    Build the CLI command line for the given provider.

    Provider commands:

    - Anthropic (Claude Code):
      Normal: ["claude", "-p", <instruction>, "--dangerously-skip-permissions", "--output-format", "json"]
      Interactive (more robust, uses subscription auth):
        ["claude", "--dangerously-skip-permissions", "--output-format", "json", <instruction>]

    - Google (Gemini CLI):
      Normal: ["gemini", "-p", <instruction>, "--yolo", "--output-format", "json"]
      Interactive: ["gemini", "--yolo", "--output-format", "json", <instruction>]

    - OpenAI (Codex CLI):
      ["codex", "exec", "--full-auto", "--json", <instruction>]

    Args:
        provider: The provider name ("anthropic", "google", "openai").
        instruction: The instruction to pass to the CLI.
        use_interactive_mode: If True, use interactive mode instead of -p flag.
                              This is more robust for Anthropic as it uses
                              subscription auth and allows full file access.
    """
    if provider == "anthropic":
        if use_interactive_mode:
            # Interactive mode: no -p flag, uses subscription auth
            # This allows full file access and is more robust
            return [
                "claude",
                "--dangerously-skip-permissions",
                "--output-format",
                "json",
                instruction,
            ]
        else:
            return [
                "claude",
                "-p",
                instruction,
                "--dangerously-skip-permissions",
                "--output-format",
                "json",
            ]
    if provider == "google":
        if use_interactive_mode:
            # Interactive mode for Gemini
            return [
                "gemini",
                "--yolo",
                "--output-format",
                "json",
                instruction,
            ]
        else:
            return [
                "gemini",
                "-p",
                instruction,
                "--yolo",
                "--output-format",
                "json",
            ]
    if provider == "openai":
        return [
            "codex",
            "exec",
            "--full-auto",
            "--json",
            instruction,
        ]
    raise ValueError(f"Unknown provider: {provider}")


def _classify_gemini_model(model_name: str) -> str:
    """
    Classify a Gemini model name into a pricing family: 'flash', 'pro', or 'default'.
    """
    lower = model_name.lower()
    if "flash" in lower:
        return "flash"
    if "pro" in lower:
        return "pro"
    return "default"


def _safe_int(value: Any) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def _calculate_gemini_cost(stats: Mapping[str, Any]) -> float:
    """
    Compute total Gemini cost from stats.models[model]["tokens"] entries.

    Each model entry should have:
      tokens = { "prompt": int, "candidates": int, "cached": int, ... }

    Pricing is determined by the model family (flash/pro/default).
    Cached tokens are charged at a discounted rate.
    """
    models = stats.get("models") or {}
    if not isinstance(models, Mapping):
        return 0.0

    total_cost = 0.0
    for model_name, model_data in models.items():
        if not isinstance(model_data, Mapping):
            continue
        tokens = model_data.get("tokens") or {}
        if not isinstance(tokens, Mapping):
            continue

        prompt_tokens = _safe_int(tokens.get("prompt"))
        output_tokens = _safe_int(tokens.get("candidates"))
        cached_tokens = _safe_int(tokens.get("cached"))

        family = _classify_gemini_model(str(model_name))
        pricing = GEMINI_PRICING_BY_FAMILY.get(family, GEMINI_PRICING_BY_FAMILY["default"])

        # Assume prompt_tokens includes cached_tokens; charge non-cached at full price,
        # cached at a discounted rate.
        new_prompt_tokens = max(prompt_tokens - cached_tokens, 0)
        effective_cached_tokens = min(cached_tokens, prompt_tokens)

        cost_input_new = new_prompt_tokens * pricing.input_per_million / 1_000_000
        cost_input_cached = (
            effective_cached_tokens
            * pricing.input_per_million
            * pricing.cached_input_multiplier
            / 1_000_000
        )
        cost_output = output_tokens * pricing.output_per_million / 1_000_000

        total_cost += cost_input_new + cost_input_cached + cost_output

    return total_cost


def _calculate_codex_cost(usage: Mapping[str, Any]) -> float:
    """
    Compute Codex/OpenAI cost from a `usage` dict with:

      - input_tokens
      - output_tokens
      - cached_input_tokens

    Cached tokens are charged at a 75% discount (i.e. 25% of full price).
    """
    input_tokens = _safe_int(usage.get("input_tokens"))
    output_tokens = _safe_int(usage.get("output_tokens"))
    cached_input_tokens = _safe_int(usage.get("cached_input_tokens"))

    new_input_tokens = max(input_tokens - cached_input_tokens, 0)
    effective_cached_tokens = min(cached_input_tokens, input_tokens)

    pricing = CODEX_PRICING

    cost_input_new = new_input_tokens * pricing.input_per_million / 1_000_000
    cost_input_cached = (
        effective_cached_tokens
        * pricing.input_per_million
        * pricing.cached_input_multiplier
        / 1_000_000
    )
    cost_output = output_tokens * pricing.output_per_million / 1_000_000

    return cost_input_new + cost_input_cached + cost_output


def _parse_anthropic_result(data: Mapping[str, Any]) -> Tuple[bool, str, float]:
    """
    Parse Claude Code (Anthropic) JSON result.

    Expected:
      - data["result"]: main content (Claude Code output format)
      - data["response"]: fallback for backwards compatibility
      - data["error"]: optional error block
      - data["total_cost_usd"]: total cost in USD (if available)
    """
    error_info = data.get("error")
    has_error = bool(error_info)

    if isinstance(error_info, Mapping):
        error_msg = str(error_info.get("message") or error_info)
    elif error_info is not None:
        error_msg = str(error_info)
    else:
        error_msg = ""

    response_text = str(data.get("result") or data.get("response") or "")
    if not response_text and error_msg:
        response_text = error_msg

    cost_raw = data.get("total_cost_usd")
    try:
        cost = float(cost_raw)
    except (TypeError, ValueError):
        cost = 0.0

    return (not has_error, response_text, cost)


def _parse_gemini_result(data: Mapping[str, Any]) -> Tuple[bool, str, float]:
    """
    Parse Gemini CLI JSON result.

    Expected high-level structure:
      {
        "response": "string",
        "stats": { ... per-model token usage ... },
        "error": { ... }  # optional
      }
    """
    error_info = data.get("error")
    has_error = bool(error_info)

    if isinstance(error_info, Mapping):
        error_msg = str(error_info.get("message") or error_info)
    elif error_info is not None:
        error_msg = str(error_info)
    else:
        error_msg = ""

    response_text = str(data.get("response") or "")
    if not response_text and error_msg:
        response_text = error_msg

    stats = data.get("stats") or {}
    cost = 0.0
    if isinstance(stats, Mapping):
        try:
            cost = _calculate_gemini_cost(stats)
        except Exception:
            cost = 0.0

    return (not has_error, response_text, cost)


def _extract_codex_usage(stdout: str) -> Optional[Mapping[str, Any]]:
    """
    Extract the latest `usage` object from Codex JSONL output.

    The `codex exec --json` command emits newline-delimited JSON events.
    We scan all lines and keep the most recent event containing a `usage` key.
    """
    last_usage: Optional[Mapping[str, Any]] = None
    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        usage = event.get("usage")
        if isinstance(usage, Mapping):
            last_usage = usage
    return last_usage


def _extract_codex_output(stdout: str) -> str:
    """
    Extract assistant-visible output text from Codex JSONL output.

    Heuristic:
      - Collect content from events with type == "message" and role == "assistant"
      - Fallback to raw stdout if nothing is found
    """
    assistant_messages: List[str] = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue

        if event.get("type") == "message" and event.get("role") == "assistant":
            content = event.get("content")
            if isinstance(content, str):
                assistant_messages.append(content)
            elif isinstance(content, list):
                # Sometimes content may be a list of segments; concatenate any text fields.
                parts: List[str] = []
                for part in content:
                    if isinstance(part, Mapping) and "text" in part:
                        parts.append(str(part["text"]))
                    else:
                        parts.append(str(part))
                assistant_messages.append("".join(parts))

    if assistant_messages:
        return "\n".join(assistant_messages)

    return stdout.strip()


def _run_with_provider(
    provider: str,
    agentic_instruction: str,
    cwd: Path,
    *,
    verbose: bool,
    quiet: bool,
    label: str = "",
) -> Tuple[bool, str, float]:
    """
    Invoke the given provider's CLI in headless JSON mode.

    For Anthropic (Claude), uses subscription auth (removes API key from env)
    and interactive mode (no -p flag) for more robust authentication that
    doesn't require API credits.

    Returns:
        (success, message, cost)

        - success: True if the CLI completed successfully without reported errors
        - message: natural-language output on success, or error description on failure
        - cost: estimated USD cost for this attempt
    """
    # Use interactive mode and CLI auth for Anthropic (more robust, uses subscription)
    use_interactive = provider == "anthropic"
    use_cli_auth = provider == "anthropic"

    cmd = _build_provider_command(
        provider,
        agentic_instruction,
        use_interactive_mode=use_interactive,
    )
    timeout = _get_agent_timeout()
    env = _build_subprocess_env(use_cli_auth=use_cli_auth)

    log_debug(
        f"Invoking provider '{provider}' with timeout {timeout:.1f}s",
        verbose=verbose,
        quiet=quiet,
        label=label,
    )
    log_debug(
        f"Command: {' '.join(cmd)}",
        verbose=verbose,
        quiet=quiet,
        label=label,
    )

    try:
        completed = subprocess.run(
            cmd,
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except FileNotFoundError:
        message = f"CLI command for provider '{provider}' was not found."
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0
    except subprocess.TimeoutExpired:
        message = f"Provider '{provider}' CLI timed out after {timeout:.1f} seconds."
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0
    except Exception as exc:
        message = f"Error invoking provider '{provider}': {exc}"
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0

    stdout = completed.stdout or ""
    stderr = completed.stderr or ""
    if verbose and stdout:
        log_debug(f"{provider} stdout:\n{stdout}", verbose=verbose, quiet=quiet, label=label)
    if verbose and stderr:
        log_debug(f"{provider} stderr:\n{stderr}", verbose=verbose, quiet=quiet, label=label)

    # Default assumptions
    success = completed.returncode == 0
    cost = 0.0
    message: str

    # Provider-specific JSON parsing and cost extraction
    if provider in ("anthropic", "google"):
        raw_json = stdout.strip() or stderr.strip()
        if not raw_json:
            message = f"Provider '{provider}' produced no JSON output."
            log_error(message, verbose=verbose, quiet=quiet, label=label)
            return False, message, 0.0

        try:
            data = json.loads(raw_json)
        except json.JSONDecodeError as exc:
            # Include raw output in the error message to aid debugging
            # (e.g. if the provider printed a plain text error instead of JSON)
            message = f"Failed to parse JSON from provider '{provider}': {exc}\nOutput: {raw_json}"
            log_error(message, verbose=verbose, quiet=quiet, label=label)
            return False, message, 0.0

        if not isinstance(data, Mapping):
            message = f"Unexpected JSON structure from provider '{provider}'."
            log_error(message, verbose=verbose, quiet=quiet, label=label)
            return False, message, 0.0

        if provider == "anthropic":
            parsed_success, response_text, cost = _parse_anthropic_result(data)
        else:  # google / Gemini
            parsed_success, response_text, cost = _parse_gemini_result(data)

        # Combine CLI exit code with JSON-level success flag
        if not success or not parsed_success:
            success = False
        message = response_text or stderr.strip() or stdout.strip() or "No response from provider."

        if not success and completed.returncode != 0 and stderr:
            message = f"{message}\n\nCLI stderr:\n{stderr.strip()}"
        return success, message, cost

    # OpenAI / Codex: JSONL stream on stdout
    if provider == "openai":
        usage = _extract_codex_usage(stdout)
        if usage is not None:
            try:
                cost = _calculate_codex_cost(usage)
            except Exception:
                cost = 0.0

        message = _extract_codex_output(stdout)
        if not success:
            if stderr.strip():
                message = (
                    f"{message}\n\nCLI stderr:\n{stderr.strip()}"
                    if message
                    else f"Codex CLI failed with exit code {completed.returncode}.\n\nstderr:\n{stderr.strip()}"
                )
            elif not message:
                message = f"Codex CLI failed with exit code {completed.returncode}."

        return success, message or "No response from provider.", cost

    # Should not reach here because _build_provider_command validates provider
    message = f"Unsupported provider '{provider}'."
    log_error(message, verbose=verbose, quiet=quiet, label=label)
    return False, message, 0.0


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def get_available_agents() -> List[str]:
    """
    Return a list of available agent providers, e.g. ["anthropic", "google"].

    A provider is considered available if:
      - Its CLI binary exists on PATH (checked via shutil.which)
      - Its API key appears configured (using llm_invoke's model data plus
        well-known environment variables)
    """
    model_data = _safe_load_model_data()
    available: List[str] = []

    for provider in AGENT_PROVIDER_PREFERENCE:
        cli = CLI_COMMANDS.get(provider)
        if not cli:
            continue
        if shutil.which(cli) is None:
            continue
        if not _provider_has_api_key(provider, model_data):
            continue
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
    Run an agentic task using the first available provider in preference order.

    The task is executed in headless mode with JSON output for structured
    parsing and real cost tracking.

    Process:
      1. Write `instruction` into a unique temp file named
         `.agentic_prompt_<random>.txt` under `cwd`.
      2. Build agentic meta-instruction:

         "Read the file {prompt_file} for instructions. You have full file
          access to explore and modify files as needed."

      3. Try providers in `AGENT_PROVIDER_PREFERENCE` order, but only those
         returned by `get_available_agents()`.
      4. For each provider:
           - Invoke its CLI in headless JSON mode with file-write permissions.
           - Parse JSON to extract response text and cost.
           - On success, stop and return.
           - On failure, proceed to next provider.
      5. Clean up the temp prompt file.

    Args:
        instruction: Natural-language instruction describing the task.
        cwd: Project root where the agent should operate.
        verbose: Enable verbose logging (debug output).
        quiet: Suppress non-error logging.
        label: Optional label prefix for log messages (e.g. "agentic-fix").

    Returns:
        Tuple[bool, str, float, str]:
            - success: Whether the task completed successfully.
            - output:  On success, the agent's main response text.
                       On failure, a human-readable error message.
            - cost:    Total estimated USD cost across all provider attempts.
            - provider_used: Name of the successful provider
                             ("anthropic", "google", or "openai"),
                             or "" if no provider succeeded.
    """
    if not instruction or not instruction.strip():
        message = "Agentic instruction must be a non-empty string."
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0, ""

    if not cwd.exists() or not cwd.is_dir():
        message = f"Working directory does not exist or is not a directory: {cwd}"
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0, ""

    available = get_available_agents()
    if not available:
        message = "No agent providers are available. Ensure CLI tools and API keys are configured."
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0, ""

    log_info(
        f"Available providers (in preference order): {', '.join(available)}",
        verbose=verbose,
        quiet=quiet,
        label=label,
    )

    # 1. Write user instruction into a unique prompt file under cwd
    prompt_token = secrets.token_hex(8)
    prompt_file = cwd / f".agentic_prompt_{prompt_token}.txt"

    try:
        prompt_file.write_text(instruction, encoding="utf-8")
    except OSError as exc:
        message = f"Failed to write prompt file '{prompt_file}': {exc}"
        log_error(message, verbose=verbose, quiet=quiet, label=label)
        return False, message, 0.0, ""

    agentic_instruction = (
        f"Read the file {prompt_file} for instructions. "
        "You have full file access to explore and modify files as needed."
    )

    total_cost = 0.0
    provider_errors: List[str] = []

    try:
        for provider in AGENT_PROVIDER_PREFERENCE:
            if provider not in available:
                continue

            log_info(
                f"Trying provider '{provider}'...",
                verbose=verbose,
                quiet=quiet,
                label=label,
            )

            success, message, cost = _run_with_provider(
                provider,
                agentic_instruction,
                cwd,
                verbose=verbose,
                quiet=quiet,
                label=label,
            )
            total_cost += cost

            if success:
                log_info(
                    f"Provider '{provider}' completed successfully. "
                    f"Estimated cost: ${cost:.6f}",
                    verbose=verbose,
                    quiet=quiet,
                    label=label,
                )
                return True, message, total_cost, provider

            provider_errors.append(f"{provider}: {message}")
            log_error(
                f"Provider '{provider}' failed: {message}",
                verbose=verbose,
                quiet=quiet,
                label=label,
            )

        # If we reach here, all providers failed
        combined_error = "All agent providers failed. " + " | ".join(provider_errors)
        log_error(combined_error, verbose=verbose, quiet=quiet, label=label)
        return False, combined_error, total_cost, ""

    finally:
        # 5. Clean up prompt file
        try:
            if prompt_file.exists():
                prompt_file.unlink()
        except OSError:
            # Best-effort cleanup; ignore errors.
            pass