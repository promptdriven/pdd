from __future__ import annotations

import functools
import os
import signal
import sys
import json
import shutil
import subprocess
import tempfile
import time
import uuid
import re
import random
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Any, Union
from dataclasses import dataclass

from rich.console import Console

def _load_model_data(*args, **kwargs):
    """Lazily load model data from ``pdd.llm_invoke``.

    The real loader lives in ``pdd.llm_invoke``, but a top-level import here
    creates a circular import: ``pdd/__init__.py`` imports this module, which
    would import ``pdd.llm_invoke``, which (transitively, via the FastAPI
    routes) imports back into ``pdd.agentic_common`` while it is still
    initializing. Importing inside the helpers defers the resolution until
    after package import completes. Returns ``None`` when the loader is
    genuinely unavailable.
    """
    try:
        from pdd.llm_invoke import _load_model_data as _real_loader
    except ImportError:
        return None
    return _real_loader(*args, **kwargs)

# Constants
_DEFAULT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai", "opencode"]

# Default number of tail lines to scan for semantic regex patterns.
# Semantic matching is restricted to the tail to prevent false positives
# when LLMs quote/discuss a status without declaring it (Issue #865).
_SEMANTIC_TAIL_LINES = 30

# Semantic fallback patterns for when LLMs paraphrase instead of emitting exact tokens.
# Each token maps to a list of regex patterns that capture common paraphrases.
# Patterns are checked only after exact and case-insensitive matching fail,
# and only in the tail of the output.
SEMANTIC_PATTERNS: Dict[str, List[str]] = {
    "ALL_TESTS_PASS": [
        r"\ball\b.*\btests?\b.*\bpass",         # "all tests pass", "all 18 tests pass"
        r"\d+/\d+\s+pass",                     # "18/18 passing"
        r"both\s+passed",                       # "both passed"
        r"all\s+tests?\s+(are\s+)?green",       # "all tests are green"
        r"all\s+tests?\s+passed\s+successfully", # "all tests passed successfully"
        r"tests?\s+suite\s+passed",             # "test suite passed"
        r"100%\s+pass",                         # "100% passing"
        r"\b\d+\s+passed\b(?!.*\b\d+\s+failed\b)", # "788 passed" (no failures mentioned)
        r"\bfix\b.*\bcomplete\b",               # "fix is complete"
        r"\bverif(?:ied|ication)\b.*\bcleanly\b", # "verification completed cleanly"
    ],
    "NOT_A_BUG": [
        r"\bnot\s+(?:actually\s+)?(?:a\s+)?(?:real\s+)?bug\b", # "not a bug", "not a real bug", "not actually a bug"
        r"(it\s+is\s+|already\s+)fixed",        # "it is already fixed", "already fixed"
        r"expected\s+behavio[u]?r",             # "expected behavior"
        r"working\s+(as\s+)?(designed|intended|correctly|expected)", # "working correctly"
        r"not\s+(actually\s+)?a\s+(code\s+)?issue", # "not actually an issue"
    ],
    "CONTINUE_CYCLE": [
        r"tests?\s+still\s+fail",              # "tests still failing"
        r"more\s+work\s+needed",                # "more work needed"
        r"not\s+yet\s+(fixed|resolved|passing)", # "not yet fixed"
        r"continue\s+(to\s+)?(next\s+)?cycle",  # "continue to next cycle"
    ],
    "MAX_CYCLES_REACHED": [
        r"max(imum)?\s+cycles?\s+(reached|exceeded|limit)", # "max cycles reached"
        r"cycle\s+limit\s+(reached|exceeded)",  # "cycle limit reached"
    ],
    "STOP_CONDITION": [
        r"awaiting\s+(architectural\s+)?decisions", # "awaiting decisions"
        r"clarification\s+(is\s+)?needed",      # "clarification is needed"
        r"need[s]?\s+clarification\s+(from|before)", # "needs clarification from/before"
        r"need[s]?\s+more\s+info(rmation)?\s+(from|before)", # "needs more info from"
    ],
}


@dataclass
class TokenMatch:
    """Result of control token detection with tier and pattern info."""
    tier: str  # "exact", "case_insensitive", "semantic", "llm_classification"
    token: Optional[str] = None  # The classified token (e.g., "NOT_A_BUG", "ALL_TESTS_PASS")
    pattern: Optional[str] = None
    cost: Optional[float] = None

    def __bool__(self) -> bool:
        return True


def detect_control_token(
    output: Optional[str],
    token: str,
    tail_lines: int = _SEMANTIC_TAIL_LINES,
) -> Optional[TokenMatch]:
    """Detect a control token in LLM output with three-tier fallback.

    Tier 1: Exact substring match (fastest, most reliable) — full output.
    Tier 2: Case-insensitive substring match — full output.
    Tier 3: Semantic regex patterns for common LLM paraphrases — tail only.

    Restricting tier 3 to the tail prevents false positives when LLMs
    quote or discuss a status in the middle of analysis without declaring it.

    Args:
        output: The raw LLM step output text.
        token: The control token to detect (e.g., 'ALL_TESTS_PASS').
        tail_lines: Number of lines from the end to scan for semantic patterns.

    Returns:
        TokenMatch if detected (truthy), None if not (falsy).
    """
    if not output:
        return None

    # Tier 1: exact match (full output)
    if token in output:
        return TokenMatch(tier="exact", token=token)

    # Tier 2: case-insensitive (full output)
    output_upper = output.upper()
    if token.upper() in output_upper:
        return TokenMatch(tier="case_insensitive", token=token)

    # Tier 3: semantic regex fallback (tail only for long outputs)
    patterns = SEMANTIC_PATTERNS.get(token, [])
    if patterns:
        lines = output.splitlines()
        if len(lines) > tail_lines:
            tail_text = '\n'.join(lines[-tail_lines:])
        else:
            tail_text = output
        for pattern in patterns:
            if re.search(pattern, tail_text, re.IGNORECASE):
                return TokenMatch(tier="semantic", token=token, pattern=pattern)

    return None


def classify_step_output(
    output: str,
    expected_tokens: List[str],
    model: str = "gemini/gemini-3-flash",
) -> Optional[TokenMatch]:
    """Classify step output via LLM when regex-based detection fails.

    Makes a single cheap API call with structured output to classify
    the step output into one of the expected control tokens.
    Only call this as a tier-4 fallback after detect_control_token returns None.

    Args:
        output: The raw step output text.
        expected_tokens: List of valid tokens (e.g., ["ALL_TESTS_PASS", "CONTINUE_CYCLE"]).
        model: LiteLLM model identifier for classification.

    Returns:
        TokenMatch when classified to a known token.
        None when the classifier confidently returns NONE.
        TokenMatch(token="CLASSIFICATION_ERROR") when classification fails
        (timeout/rate-limit/provider error/parse failure), allowing callers to
        distinguish "no token" from "classifier unavailable".
    """
    try:
        from pdd.llm_invoke import llm_invoke
    except ImportError:
        return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")

    token_list = ", ".join(expected_tokens)
    prompt = (
        "Classify the following step output into exactly one of these statuses: "
        "{token_list}, or NONE if none apply.\n\n"
        "Step output (last 3000 chars):\n{step_output}\n\n"
        "Return a JSON object with status, confidence (0-1 float), and reasoning (brief string)."
    )

    schema = {
        "type": "object",
        "properties": {
            "status": {"type": "string", "enum": expected_tokens + ["NONE"]},
            "confidence": {"type": "number"},
            "reasoning": {"type": "string"},
        },
        "required": ["status", "confidence", "reasoning"],
    }

    try:
        result = llm_invoke(
            prompt=prompt,
            input_json={"token_list": token_list, "step_output": output[-3000:]},
            output_schema=schema,
            strength=0.0,
            temperature=0.0,
        )
        # llm_invoke returns content in "result" key, not "output"
        raw = result.get("result") or result.get("output", "")
        parsed = json.loads(raw) if isinstance(raw, str) else raw
        if not parsed:
            return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")
        status = parsed.get("status", "NONE")
        if status == "NONE" or status not in expected_tokens:
            return None
        cost = result.get("cost")
        return TokenMatch(tier="llm_classification", token=status, cost=cost)
    except Exception:
        return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")


def substitute_template_variables(
    template: Any,
    context: Dict[str, Any],
    *, 
    strict_unresolved: bool = False,
) -> str:
    """Safely substitute known {placeholders} without raising on unknown keys.

    This intentionally uses iterative ``str.replace`` instead of ``str.format``
    so unknown placeholders remain intact and context values containing braces
    (e.g. JSON) are preserved verbatim.
    """
    # Compatibility path for tests/mocks that provide template objects with a
    # .format(**context) method rather than a raw string prompt.
    if not isinstance(template, str) and hasattr(template, "format") and callable(template.format):
        return str(template.format(**context))

    if strict_unresolved:
        for match in re.finditer(r"(?<![{])[{]([A-Za-z_][A-Za-z0-9_]*)[}](?![}])", template):
            key = match.group(1)
            if key not in context:
                raise KeyError(key)

    rendered = template
    for key, value in context.items():
        rendered = rendered.replace("{" + str(key) + "}", str(value))

    return rendered


def get_agent_provider_preference() -> List[str]:
    """Return provider preference order, overridable via PDD_AGENTIC_PROVIDER env var.

    Examples:
        PDD_AGENTIC_PROVIDER=google,anthropic,openai  ->  ["google", "anthropic", "openai"]
        PDD_AGENTIC_PROVIDER=google                    ->  ["google"]
        (unset)                                        ->  ["anthropic", "google", "openai"]
    """
    env_val = os.environ.get("PDD_AGENTIC_PROVIDER", "")
    if env_val:
        return [p.strip() for p in env_val.split(",") if p.strip()]
    return _DEFAULT_PROVIDER_PREFERENCE

# CLI command mapping for each provider
CLI_COMMANDS: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
    "opencode": "opencode",
}

# Common installation paths for CLI tools (platform-specific)
# Used as fallback when shutil.which() fails to find the binary
_COMMON_CLI_PATHS: Dict[str, List[Path]] = {
    "claude": [
        Path.home() / ".npm-global" / "bin" / "claude",
        Path.home() / ".local" / "bin" / "claude",
        Path.home() / "bin" / "claude",
        Path("/usr/local/bin/claude"),
        Path("/opt/homebrew/bin/claude"),
        Path("/home/linuxbrew/.linuxbrew/bin/claude"),
        # nvm base path - glob-expanded in _find_cli_binary() to search
        # ~/.nvm/versions/node/*/bin/ for all installed node versions
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "codex": [
        Path.home() / ".npm-global" / "bin" / "codex",
        Path.home() / ".local" / "bin" / "codex",
        Path.home() / "bin" / "codex",
        Path("/usr/local/bin/codex"),
        Path("/opt/homebrew/bin/codex"),
        Path("/home/linuxbrew/.linuxbrew/bin/codex"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "gemini": [
        Path.home() / ".npm-global" / "bin" / "gemini",
        Path.home() / ".local" / "bin" / "gemini",
        Path.home() / "bin" / "gemini",
        Path("/usr/local/bin/gemini"),
        Path("/opt/homebrew/bin/gemini"),
        Path("/home/linuxbrew/.linuxbrew/bin/gemini"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "opencode": [
        Path.home() / ".npm-global" / "bin" / "opencode",
        Path.home() / ".local" / "bin" / "opencode",
        Path.home() / "bin" / "opencode",
        Path("/usr/local/bin/opencode"),
        Path("/opt/homebrew/bin/opencode"),
        Path("/home/linuxbrew/.linuxbrew/bin/opencode"),
        Path.home() / ".nvm" / "versions" / "node",
    ],
}

# Maximum depth to search for .pddrc file
MAX_PDDRC_SEARCH_DEPTH: int = 10

DEFAULT_TIMEOUT_SECONDS: float = 600.0  # Increased from 240s; Claude needs time for complex verify tasks
MIN_VALID_OUTPUT_LENGTH: int = 50
DEFAULT_MAX_RETRIES: int = 3
DEFAULT_RETRY_DELAY: float = 5.0
MAX_RETRY_DELAY: float = 120.0
MAX_PATH_DISPLAY_LENGTH: int = 200  # Truncation length for PATH in diagnostic messages
MAX_ERROR_SNIPPET_LENGTH: int = 2000  # Truncation length for provider error messages (Issue #492)
# Issue #1232: max newlines allowed in a leading-"Error:" provider error response.
# Genuine terse provider errors have 0-2 newlines (single status line, or
# "Error: ...\nDetails: ..."). Multi-paragraph findings docs have many more
# newlines — this gate prevents demoting substantive docs that happen to start
# with "Error:" while preserving the long-single-line error case from #902.
MAX_ERROR_RESPONSE_NEWLINES: int = 3


def _is_rate_limited(error_message: str) -> bool:
    """Detect transient rate-limit errors that need extended backoff.

    Provider 429s clear in seconds-to-minutes; the default exponential
    backoff (1s → 2s → 4s) burns the retry budget before the rate limit
    window opens. When this returns True, the caller should pick a
    longer floor (e.g. 60s) for the next sleep.

    Background: in the May 5 agentic split run on solving_orchestrator.py,
    3 of 12 child extractions ended in ``api_error_status: 429`` after
    DEFAULT_MAX_RETRIES (3) attempts under standard backoff — children
    that would have succeeded with one or two longer waits were marked
    as terminal failures and never retried.
    """
    msg = error_message.lower()
    rate_limit_patterns = [
        r'"api_error_status"\s*:\s*429',
        r"\b429\b",
        r"rate[\s_-]?limit",
        r"too\s+many\s+requests",
        r"requests\s+per\s+minute",
        r"rate\s+exceeded",
    ]
    return any(re.search(p, msg) for p in rate_limit_patterns)


# Floor for the next sleep when the previous attempt hit a 429. Long enough
# that token-window-based limits (per-minute) have a chance to clear, short
# enough that a deadline-bounded run still attempts another shot.
RATE_LIMIT_BACKOFF_FLOOR: float = 60.0


def _is_permanent_error(error_message: str) -> bool:
    """Detect permanent provider errors that should NOT be retried.

    Includes authentication failures, invalid parameters (like temperature),
    and model access/not found errors.
    """
    msg = error_message.lower()
    permanent_patterns = [
        r"authentication[_\s]error",
        r"authentication\s+failed",
        r"failed\s+to\s+authenticate",
        r"invalid\s+bearer",
        r"invalid\s+api\s+key",
        r"invalid\s+key",
        r"invalid\s+parameter",
        r"invalid.*temperature|temperature.*(?:not supported|out of range)",
        r"\b401\b",
        r"not\s+supported\s+for\s+this\s+model",
        r"model\s+not\s+found",
        r"access\s+denied",
        r"permission\s+denied",
        # Issue #1072: Quota exhaustion patterns
        r"quota\s+(exhausted|exceeded)",
        r"daily\s+quota",
        r"terminal\s*quota\s*error",
        # Issue #1232: Anthropic CLI OAuth/login failure on cloud workers
        # ("Not logged in - Please run /login"). Without this, every cloud
        # one-session run burns its first attempt on Anthropic before falling
        # through to OpenAI.
        r"not\s+logged\s+in",
        r"please\s+run\s+/login",
        # OpenCode-specific configuration failures: these cannot heal
        # without user action (running `opencode auth login`, configuring a
        # provider, or correcting the OPENCODE_MODEL identifier). Retrying
        # them on the same provider just burns the retry budget.
        r"provider\s+not\s+configured",
        r"no\s+provider\s+configured",
        r"model\s+not\s+found\s+in\s+provider",
        r"run\s+`?opencode\s+auth\s+login`?",
        r"opencode\s+auth\s+login",
        r"configure\s+(a\s+|the\s+)?provider",
    ]
    return any(re.search(p, msg) for p in permanent_patterns)


def _codex_auth_failure_message(error_detail: str) -> Optional[str]:
    """Return a concise user-facing message for stale Codex CLI auth."""
    msg = error_detail.lower()
    auth_patterns = [
        "access token could not be refreshed",
        "please sign in again",
        "codex/responses",
        "chatgpt.com/backend-api/codex",
    ]
    if not any(pattern in msg for pattern in auth_patterns):
        return None
    if "401" not in msg and "unauthorized" not in msg and "sign in" not in msg:
        return None

    return (
        "Codex CLI authentication failed: the stored ChatGPT/Codex login token "
        "could not be refreshed. Run `codex login` (or `codex login --device-auth`; "
        "use `codex login --with-api-key` for API-key auth) and retry. "
        "To avoid Codex for this run, set `PDD_AGENTIC_PROVIDER=anthropic,google`. "
        "Other ways to disable Codex auto-detection: unset `PDD_CODEX_AUTH_AVAILABLE` "
        "(if set in env), or run `codex logout` / remove `~/.codex/auth.json` "
        "(picked up by `_has_codex_auth_file` since Issue #813 round-6)."
    )


# Interrupt context: set by agentic orchestrators so KeyboardInterrupt handling
# can report how far the workflow progressed (console + core dumps).
_agentic_interrupt_context: Optional[Dict[str, Any]] = None


def set_agentic_progress(
    workflow: str,
    current_step: int,
    total_steps: int,
    step_name: str,
    completed_steps: Optional[List[int]] = None,
) -> None:
    """Record current step progress for KeyboardInterrupt reporting and core dumps."""
    global _agentic_interrupt_context
    _agentic_interrupt_context = {
        "workflow": workflow,
        "current_step": current_step,
        "total_steps": total_steps,
        "step_name": step_name,
        "completed_steps": completed_steps or [],
    }


def clear_agentic_progress() -> None:
    """Clear progress context (call at start of workflow or on normal completion)."""
    global _agentic_interrupt_context
    _agentic_interrupt_context = None


def get_and_clear_agentic_interrupt_context() -> Optional[Dict[str, Any]]:
    """Return current progress and clear it (used by error handler on KeyboardInterrupt)."""
    global _agentic_interrupt_context
    ctx = _agentic_interrupt_context
    _agentic_interrupt_context = None
    return ctx


# Job deadline constants — prevent agentic retry loops from consuming the full job timeout
JOB_TIMEOUT_MARGIN_SECONDS: float = 120.0   # Reserve for cleanup/reporting after last attempt
MIN_ATTEMPT_TIMEOUT_SECONDS: float = 60.0   # Don't start an attempt if less than this remains

def get_job_deadline() -> Optional[float]:
    """Return the absolute Unix timestamp deadline from PDD_JOB_DEADLINE env var.

    Set by the server (jobs.py) when launching subprocess jobs so that
    the agentic retry loop can budget its attempts within the job timeout.

    Returns:
        Float deadline timestamp, or None if unset / invalid.
    """
    val = os.environ.get("PDD_JOB_DEADLINE")
    if val:
        try:
            return float(val)
        except (ValueError, TypeError):
            return None
    return None


# GitHub State Markers
GITHUB_STATE_MARKER_START = "<!-- PDD_WORKFLOW_STATE:"
GITHUB_STATE_MARKER_END = "-->"

@dataclass
class Pricing:
    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 1.0

# Pricing Configuration
# Gemini: Based on test expectations (Flash: $0.35/$1.05, Cached 50%)
GEMINI_PRICING_BY_FAMILY = {
    "flash": Pricing(0.35, 1.05, 0.5),
    "pro": Pricing(3.50, 10.50, 0.5), # Placeholder for Pro
}

# Codex: Based on test expectations ($1.50/$6.00, Cached 25%)
CODEX_PRICING = Pricing(1.50, 6.00, 0.25)

# Anthropic Claude: Token-based fallback pricing when total_cost_usd is unavailable
# Cache read is 90% discount, cache write is 25% premium over input
ANTHROPIC_PRICING_BY_FAMILY = {
    "opus": Pricing(15.0, 75.0, 0.1),       # Claude Opus 4
    "sonnet": Pricing(3.0, 15.0, 0.1),      # Claude Sonnet 4
    "haiku": Pricing(0.80, 4.0, 0.1),       # Claude Haiku 3.5
}

console = Console()


# ---------------------------------------------------------------------------
# Agentic Debug Logging
# ---------------------------------------------------------------------------

AGENTIC_LOG_DIR = ".pdd/agentic-logs"
_AGENTIC_SESSION_ID: Optional[str] = None


_PROVIDER_MODEL_ENV: Dict[str, str] = {
    "anthropic": "CLAUDE_MODEL",
    "google": "GEMINI_MODEL",
    "openai": "CODEX_MODEL",
    "opencode": "OPENCODE_MODEL",
}


def _get_provider_model(provider: str) -> Optional[str]:
    """Return the requested model for *provider* from its env var.

    Returns ``None`` when the env var is unset, empty, or the provider is
    unknown, signalling "provider default" in the audit log.
    """
    env_var = _PROVIDER_MODEL_ENV.get(provider)
    if not env_var:
        return None
    value = os.environ.get(env_var) or ""
    return value.strip() or None


def _log_agentic_interaction(
    label: str,
    prompt: str,
    response: str,
    cost: float,
    provider: str,
    success: bool,
    duration: float,
    cwd: Path,
    *,
    model: Optional[str] = None,
    false_positive: bool = False,
    include_bodies: bool = True,
) -> None:
    """
    Append one record per provider attempt to ``.pdd/agentic-logs/session_*.jsonl``.

    Issue #1376: every attempt (success, failure, false-positive) leaves a
    record so the log answers "which provider/model produced step N's output"
    without ``--verbose``. ``include_bodies=False`` writes a summary-only
    record (omits ``prompt``/``response``) to keep file size manageable when
    the same prompt repeats across many successful steps.

    Args:
        label: Step identifier (e.g., ``"step1"``).
        prompt: Full prompt text sent to the agent.
        response: Full response text from the agent.
        cost: Cost in USD for this interaction.
        provider: Provider name (``"anthropic"``, ``"google"``, ``"openai"``).
        success: Whether the run-level outcome was a success.
        duration: Duration in seconds.
        cwd: Working directory for the task.
        model: Requested model (e.g., ``"claude-opus-4-7"``) or ``None`` for
            "provider default".
        false_positive: True when the provider call returned but the PDD
            heuristic rejected the output (e.g., short ``"Done."`` reply).
            Pairs with ``success=False``.
        include_bodies: When True, include the full ``prompt`` and ``response``
            text. When False, omit them but keep ``prompt_length`` and
            ``response_length`` so downstream tooling can still gauge size.
    """
    global _AGENTIC_SESSION_ID

    try:
        # Ensure log directory exists
        log_dir = Path(cwd) / AGENTIC_LOG_DIR
        log_dir.mkdir(parents=True, exist_ok=True)

        # Initialize session ID on first call (one file per workflow run)
        if _AGENTIC_SESSION_ID is None:
            _AGENTIC_SESSION_ID = datetime.now().strftime("%Y%m%d_%H%M%S")

        log_file = log_dir / f"session_{_AGENTIC_SESSION_ID}.jsonl"

        entry: Dict[str, Any] = {
            "timestamp": datetime.now().isoformat(),
            "label": label,
            "cwd": str(cwd),
            "provider": provider,
            "model": model,
            "success": success,
            "false_positive": false_positive,
            "cost_usd": cost,
            "duration_seconds": round(duration, 2),
            "prompt_length": len(prompt),
            "response_length": len(response),
        }
        if include_bodies:
            entry["prompt"] = prompt
            entry["response"] = response

        with open(log_file, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
    except Exception:
        pass  # Don't break workflow for logging errors


# ---------------------------------------------------------------------------
# CLI Discovery (addresses GitHub issue #234: Claude not found during agentic fallback)
# ---------------------------------------------------------------------------


def _load_agentic_config() -> Dict[str, Any]:
    """
    Load agentic CLI configuration from .pddrc.

    Looks for an 'agentic' section in .pddrc with CLI path overrides:

        agentic:
          claude_path: /path/to/claude
          codex_path: /path/to/codex
          gemini_path: /path/to/gemini

    Returns empty dict if no config found.
    """
    import yaml

    # Search for .pddrc in current dir and parent dirs
    search_path = Path.cwd()
    pddrc_path: Optional[Path] = None
    for _ in range(MAX_PDDRC_SEARCH_DEPTH):
        candidate = search_path / ".pddrc"
        if candidate.is_file():
            pddrc_path = candidate
            break
        parent = search_path.parent
        if parent == search_path:
            break
        search_path = parent

    # Also check home directory
    if not pddrc_path:
        home_pddrc = Path.home() / ".pddrc"
        if home_pddrc.is_file():
            pddrc_path = home_pddrc

    if not pddrc_path:
        return {}

    try:
        with open(pddrc_path, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
        if isinstance(config, dict):
            return config.get("agentic", {}) or {}
    except Exception:
        pass

    return {}


def _find_cli_binary(name: str, config: Optional[Dict[str, Any]] = None) -> Optional[str]:
    """
    Find a CLI binary using multiple strategies.

    This function addresses a common issue where CLI tools like 'claude' are
    installed and runnable from the user's shell, but not found by shutil.which()
    when pdd runs. This happens because shell profiles (.bashrc, .zshrc) may add
    directories to PATH that aren't available in the pdd process environment.

    Strategies (in order):
        1. Check for explicit path override in .pddrc agentic config
        2. Try shutil.which() for standard PATH lookup
        3. Search common installation directories

    Args:
        name: CLI binary name (e.g., "claude", "codex", "gemini")
        config: Optional pre-loaded agentic config dict (avoids repeated file reads)

    Returns:
        Full path to the binary if found, None otherwise
    """
    # Strategy 1: Check .pddrc config override
    if config is None:
        config = _load_agentic_config()

    config_key = f"{name}_path"
    if config_key in config:
        custom_path = Path(config[config_key])
        if custom_path.exists() and os.access(custom_path, os.X_OK):
            return str(custom_path)

    # Strategy 2: Standard PATH lookup
    path_result = shutil.which(name)
    if path_result:
        return path_result

    # Strategy 3: Search common installation directories. Home-relative paths
    # are added at runtime because tests and embedding environments may patch
    # Path.home() after this module has already been imported.
    for path in _iter_common_cli_paths(name):
        # Handle nvm-style paths that need glob expansion
        # nvm installs to ~/.nvm/versions/node/vX.Y.Z/bin/
        if "nvm" in str(path) and path.name == "node":
            # Glob for all node versions and check for the CLI in each
            try:
                for version_dir in path.glob("*/bin"):
                    cli_path = version_dir / name
                    if cli_path.exists() and os.access(cli_path, os.X_OK):
                        return str(cli_path)
            except Exception:
                pass
        elif path.exists() and os.access(path, os.X_OK):
            return str(path)

    return None


def _iter_common_cli_paths(name: str) -> List[Path]:
    """Return common CLI paths, including runtime-expanded home paths.

    ``_COMMON_CLI_PATHS`` is intentionally kept as a mutable module-level table
    for tests and .pddrc-style overrides, but entries containing ``Path.home()``
    are evaluated when the module is imported. Add an equivalent runtime set so
    discovery still honors the current home directory.
    """
    paths = list(_COMMON_CLI_PATHS.get(name, []))
    if name in {"claude", "codex", "gemini", "opencode"}:
        home = Path.home()
        paths.extend([
            home / ".npm-global" / "bin" / name,
            home / ".local" / "bin" / name,
            home / "bin" / name,
            home / ".nvm" / "versions" / "node",
        ])

    seen: set[str] = set()
    unique_paths: List[Path] = []
    for path in paths:
        key = str(path)
        if key in seen:
            continue
        seen.add(key)
        unique_paths.append(path)
    return unique_paths


def _get_cli_diagnostic_info(name: str) -> str:
    """
    Generate diagnostic information for CLI discovery failures.

    Returns a helpful message for troubleshooting when a CLI binary cannot be found.
    """
    lines = [
        f"CLI '{name}' not found. Troubleshooting steps:",
        "",
        f"1. Check installation: which {name}",
        f"2. Common installation paths searched:",
    ]

    for path in _iter_common_cli_paths(name):
        lines.append(f"   - {path}")

    lines.extend([
        "",
        "3. Configure custom path in .pddrc:",
        f"   agentic:",
        f"     {name}_path: /path/to/{name}",
        "",
        f"4. Current PATH: {os.environ.get('PATH', 'not set')[:MAX_PATH_DISPLAY_LENGTH]}...",
    ])

    return "\n".join(lines)


def get_available_agents() -> List[str]:
    """
    Returns list of available provider names based on CLI existence and API key configuration.

    Uses _find_cli_binary() for robust CLI discovery that searches:
    1. .pddrc config overrides
    2. Standard PATH (shutil.which)
    3. Common installation directories
    """
    available = []

    # 1. Anthropic (Claude)
    # Available if 'claude' CLI exists. API key not strictly required (subscription auth).
    if _find_cli_binary("claude"):
        available.append("anthropic")

    # 2. Google (Gemini)
    # Available if 'gemini' CLI exists AND any supported non-interactive auth
    # path is configured. The Gemini CLI can run headless from its stored OAuth
    # credentials even when GOOGLE_API_KEY/GEMINI_API_KEY are unset.
    has_gemini_cli = _find_cli_binary("gemini") is not None
    has_google_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    has_vertex_auth = (
        os.environ.get("GOOGLE_GENAI_USE_VERTEXAI") == "true"
        and (
            os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
            or os.environ.get("GOOGLE_CLOUD_PROJECT")  # ADC on GCP VMs
        )
    )
    has_gemini_oauth = _has_gemini_oauth_credentials()

    if has_gemini_cli and (has_google_key or has_vertex_auth or has_gemini_oauth):
        available.append("google")

    # 3. OpenAI (Codex)
    # Available if 'codex' CLI exists AND any supported auth path is present:
    #   - OPENAI_API_KEY env (direct API auth)
    #   - PDD_CODEX_AUTH_AVAILABLE (cloud waterfall signal)
    #   - ~/.codex/auth.json with a token (local `codex login` ChatGPT auth).
    # Issue #813 round-6 follow-up: keep the runtime check aligned with
    # `pdd setup`'s detection (`_has_provider_oauth("openai")`) so a user
    # with only the file-based login isn't told Codex is configured during
    # setup but then silently dropped from the runtime preference list.
    has_codex_oauth = _has_codex_auth_file()
    if _find_cli_binary("codex") and (
        os.environ.get("OPENAI_API_KEY")
        or os.environ.get("PDD_CODEX_AUTH_AVAILABLE")
        or has_codex_oauth
    ):
        available.append("openai")

    # 4. OpenCode (multi-provider CLI)
    # Available if 'opencode' CLI exists AND at least one usable credential
    # signal is present: stored OpenCode auth.json with provider data, an
    # OpenCode config source declaring a provider, or any provider credential
    # env var represented in pdd/data/llm_model.csv. OPENCODE_MODEL alone is
    # NOT a credential — it's a model knob.
    if _find_cli_binary("opencode") and _has_opencode_credentials():
        available.append("opencode")

    return available


def _has_gemini_oauth_credentials() -> bool:
    """Return True when Gemini CLI stored OAuth credentials are present.

    Gemini CLI supports first-party OAuth auth stored under ~/.gemini. Treating
    API keys and Vertex env as the only available auth paths makes PDD skip a
    working local Gemini CLI and fall into broken providers.
    """
    creds_path = Path.home() / ".gemini" / "oauth_creds.json"
    try:
        data = json.loads(creds_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    return bool(data.get("refresh_token") or data.get("access_token"))


def _has_codex_auth_file() -> bool:
    """Return True when Codex CLI stored ChatGPT login is present.

    Codex CLI persists its ChatGPT/OAuth token at ``~/.codex/auth.json``
    (created by ``codex login``). Treating ``OPENAI_API_KEY`` and
    ``PDD_CODEX_AUTH_AVAILABLE`` as the only auth signals makes PDD skip
    a working local Codex CLI when the user has only the file-based login,
    and (Issue #813 round-6 follow-up) creates a UX inconsistency where
    ``pdd setup`` calls Codex configured via this same file but
    ``get_available_agents()`` then drops it from the runtime preference
    list.
    """
    auth_path = Path.home() / ".codex" / "auth.json"
    try:
        data = json.loads(auth_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    return bool(
        data.get("token")
        or data.get("tokens")
        or data.get("OPENAI_API_KEY")
    )

# ---------------------------------------------------------------------------
# OpenCode helpers (auth detection, model resolution, JSONL parsing)
# ---------------------------------------------------------------------------

# Provider credential env vars used by OpenCode-backed providers, derived from
# pdd/data/llm_model.csv. Any one of these being set is treated as a usable
# credential signal for OpenCode availability detection.
_OPENCODE_PROVIDER_ENV_KEYS: Tuple[str, ...] = (
    "ANTHROPIC_API_KEY",
    "OPENAI_API_KEY",
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    "OPENROUTER_API_KEY",
    "GITHUB_TOKEN",
    "XAI_API_KEY",
    "DEEPSEEK_API_KEY",
    "MISTRAL_API_KEY",
    "COHERE_API_KEY",
    "MOONSHOT_API_KEY",
    "AZURE_API_KEY",
    "AZURE_AI_API_KEY",
    "AWS_ACCESS_KEY_ID",
    "GROQ_API_KEY",
    "TOGETHERAI_API_KEY",
    "FIREWORKS_AI_API_KEY",
    "FIREWORKS_API_KEY",
    "PERPLEXITYAI_API_KEY",
    "REPLICATE_API_KEY",
    "DEEPINFRA_API_KEY",
    "ZAI_API_KEY",
    "DASHSCOPE_API_KEY",
    "MINIMAX_API_KEY",
    "OLLAMA_HOST",
    "LMSTUDIO_HOST",
)


def _opencode_auth_file_has_credentials(path: Path) -> bool:
    """Return True when ``path`` is an OpenCode auth.json with usable provider data.

    OpenCode CLI persists provider credentials at
    ``~/.local/share/opencode/auth.json`` as ``{provider: {...}, ...}``. Any
    non-empty provider entry counts as a usable credential signal.
    """
    try:
        if not path.exists() or path.stat().st_size == 0:
            return False
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict) or not data:
        return False
    # Any provider entry that is a non-empty dict or non-empty string counts.
    for value in data.values():
        if isinstance(value, dict) and value:
            return True
        if isinstance(value, str) and value.strip():
            return True
    return False


def _opencode_config_paths(cwd: Optional[Path] = None) -> List[Path]:
    """Return candidate OpenCode config file locations (existing files only).

    Order: explicit ``OPENCODE_CONFIG`` env var, project ``opencode.json``
    walking up from ``cwd``, then global ``~/.config/opencode/opencode.json``.
    """
    paths: List[Path] = []
    explicit = os.environ.get("OPENCODE_CONFIG", "").strip()
    if explicit:
        p = Path(explicit)
        if p.is_file():
            paths.append(p)
    start = cwd or Path.cwd()
    try:
        cur = start.resolve()
    except OSError:
        cur = start
    for _ in range(MAX_PDDRC_SEARCH_DEPTH):
        candidate = cur / "opencode.json"
        if candidate.is_file():
            paths.append(candidate)
            break
        parent = cur.parent
        if parent == cur:
            break
        cur = parent
    global_cfg = Path.home() / ".config" / "opencode" / "opencode.json"
    if global_cfg.is_file():
        paths.append(global_cfg)
    # Deduplicate while preserving order
    seen: set[str] = set()
    unique: List[Path] = []
    for p in paths:
        key = str(p)
        if key in seen:
            continue
        seen.add(key)
        unique.append(p)
    return unique


# Field names within an OpenCode ``provider.<id>`` mapping that carry the
# secret material. Compared case-insensitively after stripping ``-``/``_``.
_OPENCODE_PROVIDER_CREDENTIAL_FIELDS = frozenset(
    {"apikey", "key", "token", "bearer", "bearertoken", "accesstoken", "secret"}
)


# Tokenizer for stripping JSONC comments while preserving string contents.
# A naive ``re.sub(r"//[^\n]*", "", text)`` mangles valid configs that
# contain ``"baseURL": "https://..."`` inside JSON strings — the ``//``
# inside the URL gets eaten along with the rest of the line. This pattern
# matches a complete double-quoted JSON string (with backslash escapes)
# OR a block comment OR a line comment, in that priority order; strings
# pass through untouched while comments are dropped.
_JSONC_TOKEN_RE = re.compile(
    r'"(?:\\.|[^"\\])*"'   # double-quoted JSON string with escape support
    r'|/\*[\s\S]*?\*/'      # /* block comment */
    r'|//[^\n]*'            # // line comment
)


def _strip_jsonc_comments(text: str) -> str:
    """Strip JSONC line/block comments while preserving string contents.

    The previous implementation used ``re.sub(r"//[^\\n]*", "", text)`` which
    silently deleted ``https://...`` inside JSON string values, so a normal
    OpenCode provider config with ``baseURL`` plus ``apiKey`` failed JSON
    parsing and was reported unconfigured.
    """
    def _repl(match: "re.Match[str]") -> str:
        token = match.group(0)
        if token.startswith("//") or token.startswith("/*"):
            return ""
        return token
    return _JSONC_TOKEN_RE.sub(_repl, text)


def _parse_opencode_config_text(text: str) -> Optional[Dict[str, Any]]:
    """Parse a JSON/JSONC OpenCode config payload to a dict, or ``None``."""
    if not text:
        return None
    try:
        data = json.loads(_strip_jsonc_comments(text))
    except (json.JSONDecodeError, ValueError):
        return None
    return data if isinstance(data, dict) else None


def _opencode_data_declares_provider(data: Optional[Dict[str, Any]]) -> bool:
    """Return True when parsed OpenCode config declares usable provider auth."""
    if not isinstance(data, dict):
        return False
    provider = data.get("provider")
    if isinstance(provider, dict):
        for value in provider.values():
            if _opencode_provider_value_has_usable_credential(value):
                return True
    return False


def _iter_opencode_config_texts(cwd: Optional[Path] = None) -> List[str]:
    """Yield raw config text from all OpenCode config sources.

    Includes both file-backed sources (``OPENCODE_CONFIG``, project
    ``opencode.json``, global ``~/.config/opencode/opencode.json``) and the
    ``OPENCODE_CONFIG_CONTENT`` env var, which the prompt contract treats as
    an inline config payload equivalent to a discovered file.
    """
    texts: List[str] = []
    for cfg in _opencode_config_paths(cwd):
        try:
            texts.append(cfg.read_text(encoding="utf-8"))
        except OSError:
            continue
    inline = os.environ.get("OPENCODE_CONFIG_CONTENT", "")
    if inline and inline.strip():
        texts.append(inline)
    return texts

# Containers within a provider mapping that may nest credential fields.
_OPENCODE_PROVIDER_CREDENTIAL_CONTAINERS = frozenset({"options", "auth", "headers"})


def _resolve_opencode_template_value(value: Any) -> Optional[str]:
    """Resolve an OpenCode config template ``{env:VAR}`` / ``{file:PATH}``.

    Returns the resolved non-empty string, or ``None`` when the template
    cannot be resolved (env var unset, file missing/empty). Plain strings
    pass through after stripping; non-strings return ``None``.
    """
    if not isinstance(value, str):
        return None
    s = value.strip()
    if not s:
        return None
    m = re.fullmatch(r"\{env:([^}]+)\}", s)
    if m:
        v = os.environ.get(m.group(1).strip())
        return v.strip() if v and v.strip() else None
    m = re.fullmatch(r"\{file:([^}]+)\}", s)
    if m:
        try:
            text = Path(m.group(1).strip()).expanduser().read_text(encoding="utf-8").strip()
        except OSError:
            return None
        return text or None
    # Plain string with no template: treat as a literal credential value.
    return s


def _opencode_provider_value_has_usable_credential(value: Any) -> bool:
    """Return True when an OpenCode ``provider.<id>`` value carries usable auth.

    OpenCode config files frequently contain provider preferences (model
    name, options) without credentials, including unresolved
    ``{env:VAR}`` / ``{file:PATH}`` references. This walks one level deep
    into the value, looking only for credential-shaped fields whose
    resolved string is non-empty.
    """
    if isinstance(value, str):
        return _resolve_opencode_template_value(value) is not None
    if not isinstance(value, dict):
        return False
    for key, sub in value.items():
        if not isinstance(key, str):
            continue
        normalized = key.lower().replace("-", "").replace("_", "")
        if normalized in _OPENCODE_PROVIDER_CREDENTIAL_FIELDS:
            if isinstance(sub, str):
                if _resolve_opencode_template_value(sub) is not None:
                    return True
            elif isinstance(sub, dict):
                for v in sub.values():
                    if isinstance(v, str) and _resolve_opencode_template_value(v) is not None:
                        return True
            continue
        if normalized in _OPENCODE_PROVIDER_CREDENTIAL_CONTAINERS and isinstance(sub, dict):
            if _opencode_provider_value_has_usable_credential(sub):
                return True
    return False


def _opencode_config_declares_provider(path: Path) -> bool:
    """Return True when an OpenCode config file declares usable provider auth.

    A bare ``model`` preference or an empty ``provider`` mapping is
    diagnostic-only — it must not flip availability. A ``provider`` entry
    qualifies only when it contains a credential-shaped field (apiKey, key,
    token, bearer, ...) whose resolved value is non-empty. Unresolved
    ``{env:VAR}`` / ``{file:PATH}`` references with the env var unset or
    the file missing do not qualify.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return False
    # OpenCode supports JSONC. ``_parse_opencode_config_text`` strips
    # comments without eating ``//`` that appears inside string values
    # (e.g. ``"baseURL": "https://..."``).
    return _opencode_data_declares_provider(_parse_opencode_config_text(text))


def _has_opencode_credentials(cwd: Optional[Path] = None) -> bool:
    """Return True when any OpenCode credential signal is present.

    Signals (any one is sufficient):
      - ``~/.local/share/opencode/auth.json`` parses to non-empty provider data
      - An OpenCode config source declares a provider/model
      - Any provider credential env var from llm_model.csv is set
    """
    auth_path = Path.home() / ".local" / "share" / "opencode" / "auth.json"
    if _opencode_auth_file_has_credentials(auth_path):
        return True
    # File-backed configs and the inline ``OPENCODE_CONFIG_CONTENT`` env var
    # both qualify per the prompt contract.
    for text in _iter_opencode_config_texts(cwd):
        if _opencode_data_declares_provider(_parse_opencode_config_text(text)):
            return True
    for key in _OPENCODE_PROVIDER_ENV_KEYS:
        val = os.environ.get(key)
        if val and val.strip():
            return True
    return False


def _translate_to_opencode_model(model_id: str) -> str:
    """Translate LiteLLM-oriented model IDs to OpenCode ``provider/model`` form.

    Rules:
      * ``github_copilot/X`` -> ``github-copilot/X``
      * ``gemini/X`` -> ``google/X``
      * Bare ``claude-...`` -> ``anthropic/claude-...``
      * Bare ``gpt-...`` -> ``openai/gpt-...``
      * IDs already in ``provider/model`` form pass through unchanged.
    """
    if not model_id:
        return model_id
    mid = model_id.strip()
    if mid.startswith("github_copilot/"):
        return "github-copilot/" + mid[len("github_copilot/"):]
    if mid.startswith("gemini/"):
        return "google/" + mid[len("gemini/"):]
    if "/" in mid:
        return mid
    if mid.startswith("claude-"):
        return f"anthropic/{mid}"
    if mid.startswith("gpt-"):
        return f"openai/{mid}"
    return mid


def _opencode_configured_providers(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> set:
    """Return the OpenCode provider IDs that have a usable credential source.

    Used by the CSV-based model fallback to filter candidate rows to providers
    OpenCode can actually route to. Sources (any one is sufficient):

      * Top-level keys in ``~/.local/share/opencode/auth.json``
      * ``provider`` mapping keys in OpenCode config files (project, global,
        ``OPENCODE_CONFIG``, or inline ``OPENCODE_CONFIG_CONTENT``)
      * CSV rows in ``pdd/data/llm_model.csv`` whose *full* ``api_key`` env
        var set is satisfied in ``env`` — pipe-delimited multi-var entries
        like ``AZURE_API_KEY|AZURE_API_BASE|AZURE_API_VERSION`` MUST all be
        set; partial credentials must not flip a provider to "configured"
        because OpenCode cannot actually route to it.
    """
    src = env if env is not None else os.environ
    providers: set = set()

    auth_path = Path.home() / ".local" / "share" / "opencode" / "auth.json"
    try:
        if auth_path.exists() and auth_path.stat().st_size > 0:
            data = json.loads(auth_path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                for key, value in data.items():
                    if isinstance(value, dict) and value:
                        providers.add(key)
                    elif isinstance(value, str) and value.strip():
                        providers.add(key)
    except (OSError, json.JSONDecodeError):
        pass

    for text in _iter_opencode_config_texts(cwd):
        cfg_data = _parse_opencode_config_text(text)
        if not isinstance(cfg_data, dict):
            continue
        provider_dict = cfg_data.get("provider")
        if isinstance(provider_dict, dict):
            for k, v in provider_dict.items():
                # Only count provider entries that actually carry usable
                # auth — a bare options/model preference or an unresolved
                # ``{env:VAR}`` reference does not constitute a credential.
                if _opencode_provider_value_has_usable_credential(v):
                    providers.add(k)

    # Walk the CSV catalog and add a provider only when *every* env var in
    # its pipe-delimited ``api_key`` field is set. Mapping the CSV row to an
    # OpenCode provider ID goes through ``_translate_to_opencode_model`` so
    # the rules stay in lockstep with how the fallback labels rows.
    try:
        df = _load_model_data(None)
    except Exception:
        df = None
    if df is not None and not getattr(df, "empty", True):
        for _, row in df.iterrows():
            api_key_field = str(row.get("api_key") or "").strip()
            if not api_key_field:
                # Empty ``api_key`` (no-key/device-flow rows like
                # ``github_copilot/...``) cannot make a provider configured
                # via env vars; auth.json / opencode.json handle those.
                continue
            keys = [k.strip() for k in api_key_field.split("|") if k.strip()]
            if not keys:
                continue
            if not all((src.get(k) or "").strip() for k in keys):
                continue
            model_id = str(row.get("model") or "").strip()
            if not model_id:
                continue
            translated = _translate_to_opencode_model(model_id)
            prefix = translated.split("/", 1)[0] if "/" in translated else translated
            if prefix:
                providers.add(prefix)

    return providers


def _resolve_opencode_csv_fallback(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> Optional[str]:
    """Pick an OpenCode model from ``llm_model.csv`` using auth-aware filtering.

    Walks the CSV rows in descending ELO order and returns the first row whose
    ``api_key`` env vars are all set AND whose ``_translate_to_opencode_model``
    output has a provider prefix in the configured-provider set. Returns
    ``None`` when no row qualifies (caller surfaces an actionable error).
    """
    src = env if env is not None else os.environ
    try:
        df = _load_model_data(None)
    except Exception:
        return None
    if df is None or getattr(df, "empty", True):
        return None

    configured = _opencode_configured_providers(env=src, cwd=cwd)
    if not configured:
        return None

    try:
        sorted_df = df.sort_values("coding_arena_elo", ascending=False)
    except Exception:
        return None

    # A row qualifies when its translated provider prefix is in the
    # configured-provider set. ``configured`` already merges signals from
    # ``~/.local/share/opencode/auth.json``, OpenCode config files, and
    # provider env vars, so a user who ran ``opencode auth login`` for a
    # provider — or who set its API key env var — gets CSV-driven fallback
    # without also having to set both. This intentionally lets no-key /
    # device-flow rows like ``github_copilot/...`` participate when
    # OpenCode has the ``github-copilot`` provider configured, instead of
    # being skipped before translation.
    for _, row in sorted_df.iterrows():
        model_id = str(row.get("model") or "").strip()
        if not model_id:
            continue
        translated = _translate_to_opencode_model(model_id)
        prefix = translated.split("/", 1)[0] if "/" in translated else translated
        if prefix in configured:
            return translated
    return None


def _opencode_csv_cost(model_id: Optional[str], tokens: Optional[Dict[str, Any]]) -> float:
    """Compute USD cost for an OpenCode run from the CSV pricing row.

    Falls back here when OpenCode JSONL omits ``step_finish.part.cost`` so
    successful runs are not silently reported as ``$0.00``. ``model_id`` may
    be either the OpenCode ``provider/model`` form or a bare CSV model name;
    we match against the CSV ``model`` column directly. Returns ``0.0`` when
    we cannot match the row or no token counts are available.

    Pricing in ``llm_model.csv`` is per-million tokens. The Anthropic
    conventions used elsewhere (cache_read 90% off, cache_write 25% premium
    over input) are applied uniformly here for parity with the existing
    `ANTHROPIC_PRICING_BY_FAMILY` formula — backends without cache events
    just see those counters at zero.
    """
    if not model_id:
        return 0.0
    if not isinstance(tokens, dict):
        return 0.0
    try:
        df = _load_model_data(None)
    except Exception:
        return 0.0
    if df is None or getattr(df, "empty", True):
        return 0.0
    # Try matching the model id verbatim, then with any leading provider/
    # prefix stripped — OpenCode IDs like ``anthropic/claude-sonnet-4-6``
    # usually match the CSV row by suffix.
    candidates = [model_id]
    if "/" in model_id:
        candidates.append(model_id.split("/", 1)[1])
        candidates.append(model_id.rsplit("/", 1)[1])
    row = None
    for cand in candidates:
        match = df[df["model"] == cand]
        if not match.empty:
            row = match.iloc[0]
            break
    if row is None:
        return 0.0
    try:
        input_per_m = float(row.get("input") or 0.0)
        output_per_m = float(row.get("output") or 0.0)
    except (TypeError, ValueError):
        return 0.0
    input_tokens = int(tokens.get("input") or 0)
    output_tokens = int(tokens.get("output") or 0)
    cache_read = int(tokens.get("cache_read") or 0)
    cache_write = int(tokens.get("cache_write") or 0)
    if input_tokens <= 0 and output_tokens <= 0 and cache_read <= 0 and cache_write <= 0:
        return 0.0
    new_input = max(0, input_tokens - cache_read - cache_write)
    cost = (
        new_input * input_per_m / 1_000_000
        + output_tokens * output_per_m / 1_000_000
        + cache_read * input_per_m * 0.1 / 1_000_000
        + cache_write * input_per_m * 1.25 / 1_000_000
    )
    return float(cost)


def _resolve_opencode_model(env: Optional[Dict[str, str]] = None) -> Optional[str]:
    """Resolve the OpenCode model from ``OPENCODE_MODEL`` only.

    Returns the env var value verbatim (including nested slashes such as
    ``openrouter/openai/gpt-5.3-codex``), or ``None`` when unset. CSV-based
    fallback resolution lives in :func:`_resolve_opencode_model_for_run` so
    callers that only want the env-var view (tests, diagnostics) are not
    coupled to filesystem probes.
    """
    src = env if env is not None else os.environ
    raw = (src.get("OPENCODE_MODEL") or "").strip()
    if raw:
        return raw
    return None


def _resolve_opencode_model_for_run(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> Optional[str]:
    """Resolve the OpenCode model with auth-aware CSV fallback.

    Order per the prompt contract: (1) ``OPENCODE_MODEL`` env var, kept
    verbatim; (2) auth-filtered ``llm_model.csv`` row whose translated
    ``provider/model`` identifier maps to a configured OpenCode provider.
    """
    src = env if env is not None else os.environ
    raw = (src.get("OPENCODE_MODEL") or "").strip()
    if raw:
        return raw
    return _resolve_opencode_csv_fallback(env=src, cwd=cwd)


def _parse_opencode_jsonl(stdout: str) -> Dict[str, Any]:
    """Parse OpenCode JSONL output into a normalized accounting dict.

    OpenCode emits one JSON object per line (``--format json``) with events
    such as ``step_start``, ``step_finish``, ``text``, ``tool_use``, and
    ``error``. Returns a dict with keys:

      * ``text``: concatenated visible text payloads
      * ``cost``: summed ``step_finish.part.cost`` values (USD)
      * ``cost_reported``: True iff any cost field appeared
      * ``model``: model name surfaced by the run (empty when absent)
      * ``error``: first error message encountered (empty when none)
      * ``tokens``: dict with ``input``, ``output``, ``reasoning``,
        ``cache_read``, ``cache_write`` counters
    """
    text_parts: List[str] = []
    cost_total: float = 0.0
    cost_reported = False
    model_names: List[str] = []
    error_msg = ""
    tokens = {"input": 0, "output": 0, "reasoning": 0, "cache_read": 0, "cache_write": 0}

    if not stdout:
        return {
            "text": "",
            "cost": 0.0,
            "cost_reported": False,
            "model": "",
            "error": "",
            "tokens": tokens,
        }

    def _add_model(name: Any) -> None:
        if isinstance(name, str) and name.strip() and name not in model_names:
            model_names.append(name.strip())

    def _accumulate_tokens(usage: Any) -> None:
        if not isinstance(usage, dict):
            return
        for src_key, dst_key in (
            ("input", "input"),
            ("input_tokens", "input"),
            ("prompt_tokens", "input"),
            ("output", "output"),
            ("output_tokens", "output"),
            ("completion_tokens", "output"),
            ("reasoning", "reasoning"),
            ("reasoning_tokens", "reasoning"),
        ):
            v = usage.get(src_key)
            if isinstance(v, (int, float)):
                tokens[dst_key] += int(v)
        cache = usage.get("cache")
        if isinstance(cache, dict):
            for src_key, dst_key in (
                ("read", "cache_read"),
                ("write", "cache_write"),
            ):
                v = cache.get(src_key)
                if isinstance(v, (int, float)):
                    tokens[dst_key] += int(v)

    for raw_line in stdout.splitlines():
        line = raw_line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(event, dict):
            continue

        ev_type = event.get("type", "")

        # Capture model from any event that carries it.
        _add_model(event.get("model"))
        for nested_key in ("session", "message", "part"):
            nested = event.get(nested_key)
            if isinstance(nested, dict):
                _add_model(nested.get("model"))

        if ev_type == "error":
            msg = event.get("message") or event.get("error") or ""
            if isinstance(msg, dict):
                msg = msg.get("message") or msg.get("error") or ""
            if msg and not error_msg:
                error_msg = str(msg)
            continue

        if ev_type in ("step_start", "tool_use"):
            continue

        if ev_type == "step_finish":
            part = event.get("part")
            if isinstance(part, dict):
                cost_val = part.get("cost")
                if isinstance(cost_val, (int, float)):
                    cost_total += float(cost_val)
                    cost_reported = True
                _accumulate_tokens(part.get("usage") or part.get("tokens"))
            _accumulate_tokens(event.get("usage") or event.get("tokens"))
            continue

        if ev_type == "text":
            part = event.get("part")
            if isinstance(part, dict) and isinstance(part.get("text"), str):
                text_parts.append(part["text"])
            elif isinstance(event.get("text"), str):
                text_parts.append(event["text"])
            elif isinstance(event.get("content"), str):
                text_parts.append(event["content"])
            continue

        # Tolerate top-level cost on unknown events for forward compatibility.
        cost_val = event.get("cost")
        if isinstance(cost_val, (int, float)):
            cost_total += float(cost_val)
            cost_reported = True

    model_str = "+".join(sorted(model_names)) if len(model_names) > 1 else (model_names[0] if model_names else "")

    return {
        "text": "".join(text_parts),
        "cost": cost_total,
        "cost_reported": cost_reported,
        "model": model_str,
        "error": error_msg,
        "tokens": tokens,
    }


def _calculate_gemini_cost(stats: Dict[str, Any]) -> float:
    """Calculates cost for Gemini based on token stats."""
    total_cost = 0.0
    models = stats.get("models", {})
    
    for model_name, data in models.items():
        tokens = data.get("tokens", {})
        prompt = tokens.get("prompt", 0)
        candidates = tokens.get("candidates", 0)
        cached = tokens.get("cached", 0)
        
        # Determine pricing family
        family = "flash" if "flash" in model_name.lower() else "pro"
        pricing = GEMINI_PRICING_BY_FAMILY.get(family, GEMINI_PRICING_BY_FAMILY["flash"])
        
        # Logic: new_input = max(0, prompt - cached)
        # Assuming 'prompt' is total input tokens
        new_input = max(0, prompt - cached)
        
        input_cost = (new_input / 1_000_000) * pricing.input_per_million
        cached_cost = (cached / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
        output_cost = (candidates / 1_000_000) * pricing.output_per_million
        
        total_cost += input_cost + cached_cost + output_cost
        
    return total_cost

def _calculate_codex_cost(usage: Dict[str, Any]) -> float:
    """Calculates cost for Codex based on usage stats."""
    input_tokens = usage.get("input_tokens", 0)
    output_tokens = usage.get("output_tokens", 0)
    cached_tokens = usage.get("cached_input_tokens", 0)
    
    pricing = CODEX_PRICING
    
    # Logic: new_input = max(0, input - cached)
    new_input = max(0, input_tokens - cached_tokens)
    
    input_cost = (new_input / 1_000_000) * pricing.input_per_million
    cached_cost = (cached_tokens / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    output_cost = (output_tokens / 1_000_000) * pricing.output_per_million
    
    return input_cost + cached_cost + output_cost


def _calculate_anthropic_cost(data: Dict[str, Any]) -> float:
    """Calculate cost from Claude Code JSON when total_cost_usd is missing.

    Tries modelUsage per-model costUSD first, then falls back to token-based
    estimation from the usage field.
    """
    # Try 1: Sum costUSD from modelUsage (most accurate)
    model_usage = data.get("modelUsage", {})
    if model_usage:
        total = sum(
            float(info.get("costUSD", 0.0))
            for info in model_usage.values()
            if isinstance(info, dict)
        )
        if total > 0:
            return total

    # Try 2: Token-based estimation from usage field
    usage = data.get("usage", {})
    if not usage:
        return 0.0

    input_tokens = usage.get("input_tokens", 0)
    output_tokens = usage.get("output_tokens", 0)
    cache_read = usage.get("cache_read_input_tokens", 0)
    cache_creation = usage.get("cache_creation_input_tokens", 0)

    # Determine pricing family from modelUsage keys or default to sonnet
    family = "sonnet"  # default
    for model_name in model_usage.keys():
        name_lower = model_name.lower()
        if "opus" in name_lower:
            family = "opus"
            break
        elif "haiku" in name_lower:
            family = "haiku"
            break

    pricing = ANTHROPIC_PRICING_BY_FAMILY.get(family, ANTHROPIC_PRICING_BY_FAMILY["sonnet"])

    # new_input = total input minus cached reads and cache creation (those tokens are billed separately)
    new_input = max(0, input_tokens - cache_read - cache_creation)
    input_cost = (new_input / 1_000_000) * pricing.input_per_million
    cache_read_cost = (cache_read / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    cache_write_cost = (cache_creation / 1_000_000) * pricing.input_per_million * 1.25
    output_cost = (output_tokens / 1_000_000) * pricing.output_per_million

    return input_cost + cache_read_cost + cache_write_cost + output_cost


def run_agentic_task(
    instruction: str,
    cwd: Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
    label: str = "",
    timeout: Optional[float] = None,
    max_retries: int = 1,
    retry_delay: float = DEFAULT_RETRY_DELAY,
    deadline: Optional[float] = None,
    use_playwright: bool = False,
    reasoning_time: Optional[float] = None,
) -> Tuple[bool, str, float, str]:
    """
    Runs an agentic task using available providers in preference order.

    Args:
        instruction: The task instruction
        cwd: Working directory
        verbose: Show detailed output
        quiet: Suppress all non-error output
        label: Task label for logging
        timeout: Optional timeout override
        max_retries: Number of attempts per provider before fallback (default: 1 = no retries)
        retry_delay: Base delay in seconds for exponential backoff (default: DEFAULT_RETRY_DELAY)
        deadline: Optional Unix timestamp for job-level time budgeting
        use_playwright: Enable constrained tool access mode for browser-based testing
        time: Reasoning-allocation float in [0.0, 1.0] forwarded from the
            top-level ``pdd --time`` flag. When provided, overrides the
            ``PDD_REASONING_EFFORT`` env var for argv injection. ``None``
            means "fall back to env" so unplumbed call sites keep working.

    Returns:
        (success, output_text, cost_usd, provider_used)
    """
    agents = get_available_agents()

    # Filter agents based on preference order
    candidates = [p for p in get_agent_provider_preference() if p in agents]

    if not candidates:
        msg = "No agent providers are available (check CLI installation and API keys)"
        if not quiet:
            console.print(f"[bold red]{msg}[/bold red]")
        return False, msg, 0.0, ""

    effective_timeout = timeout if timeout is not None else DEFAULT_TIMEOUT_SECONDS
    effective_deadline = deadline if deadline is not None else get_job_deadline()
    task_start_time = time.time()
    # Issue #902: Cap total time across all providers to prevent 150min burn
    aggregate_deadline = task_start_time + (2 * effective_timeout)

    # Create a unique temp file for the prompt
    prompt_filename = f".agentic_prompt_{uuid.uuid4().hex[:8]}.txt"
    prompt_path = cwd / prompt_filename

    # Inject user feedback from GitHub issue comments (set by GitHub App executor)
    user_feedback = os.environ.get("PDD_USER_FEEDBACK")
    feedback_section = ""
    if user_feedback:
        feedback_section = (
            "\n\n## User Feedback\n"
            "The user provided the following feedback from a previous execution attempt. "
            "Factor this into your response:\n"
            f"{user_feedback}\n"
        )

    full_instruction = (
        f"{instruction}{feedback_section}\n\n"
        f"Read the file {prompt_filename} for instructions. "
        "You have full file access to explore and modify files as needed."
    )

    try:
        # Write prompt to file
        with open(prompt_path, "w", encoding="utf-8") as f:
            f.write(full_instruction)

        provider_errors: List[str] = []

        for provider in candidates:
            if verbose:
                console.print(f"[dim]Attempting provider: {provider} for task '{label}'[/dim]")

            # Issue #902: Check aggregate budget before starting new provider
            if time.time() > aggregate_deadline:
                if verbose:
                    console.print(f"[yellow]Aggregate step timeout exceeded. Skipping {provider}.[/yellow]")
                break

            last_output = ""
            deadline_exhausted = False
            # Issue #1376 codex round 4: tracks "ANY attempt was logged inline
            # for this provider". Stays True once set — must NOT reset per
            # attempt, because a budget-skipped attempt 2 after a logged
            # attempt 1 would otherwise let the bottom block re-log attempt
            # 1's stale data as a fake second row. Round-2 inline logging
            # already covers per-attempt records (success, FP, and failure),
            # so the bottom block now only needs to fire when zero attempts
            # ran for this provider (budget exhausted before first attempt).
            any_attempt_logged_inside = False
            # Issue #1376 P2: actual model from the last attempt's response
            # (used by both inside-loop logs and the bottom failure log).
            actual_model: Optional[str] = None
            effective_model: Optional[str] = _get_provider_model(provider)
            for attempt in range(1, max_retries + 1):
                # Deadline-aware budget check before each attempt
                now = time.time()
                budgets = []
                if effective_deadline is not None:
                    budgets.append(effective_deadline - now - JOB_TIMEOUT_MARGIN_SECONDS)
                # Issue #902: Honor aggregate step budget
                budgets.append(aggregate_deadline - now)
                
                remaining = min(budgets)
                if remaining < MIN_ATTEMPT_TIMEOUT_SECONDS:
                    if verbose:
                        console.print(
                            f"[yellow]Budget exhausted "
                            f"({remaining:.0f}s remaining < {MIN_ATTEMPT_TIMEOUT_SECONDS}s min). "
                            f"Skipping attempt {attempt}.[/yellow]"
                        )
                    deadline_exhausted = True
                    break
                
                attempt_timeout = min(effective_timeout, remaining)

                if verbose and attempt > 1:
                    console.print(f"[dim]Retry {attempt}/{max_retries} for {provider} (task: {label})[/dim]")

                success, output, cost, actual_model = _run_with_provider(
                    provider, prompt_path, cwd, attempt_timeout, verbose, quiet,
                    use_playwright=use_playwright,
                    reasoning_time=reasoning_time,
                )
                last_output = output
                # Issue #1376: prefer the model the provider actually reported;
                # fall back to the requested model from env vars when the JSON
                # didn't surface one (e.g. early-error returns).
                effective_model = actual_model or _get_provider_model(provider)

                # False Positive Detection
                # Issue #249: Empty output should ALWAYS be detected as false positive,
                # regardless of cost. Claude may consume tokens running tools but produce
                # no text response, which means the task wasn't actually completed.
                # Issue #902: Error-like content with cost > 0 is also a false positive,
                # but only when the output STARTS with "Error:" (genuine terse provider
                # error response, e.g., "Error: rate limit exceeded" or a long
                # single-line CLI error).
                # Issue #1232: Substantive output that merely mentions "Error:" mid-text
                # (e.g., describing error-raising functions) must NOT be demoted. A
                # multi-paragraph findings doc that happens to start with "Error:"
                # also survives via the newline-count gate (`MAX_ERROR_RESPONSE_NEWLINES`).
                if success:
                    stripped_output = output.strip()
                    output_length = len(stripped_output)
                    is_false_positive = (
                        output_length == 0 or  # Empty output is always a false positive
                        (cost == 0.0 and output_length < MIN_VALID_OUTPUT_LENGTH) or  # Zero cost with short output
                        (
                            cost > 0.0
                            and stripped_output.startswith("Error:")
                            and stripped_output.count("\n") < MAX_ERROR_RESPONSE_NEWLINES
                            and output_length < 4000
                        )  # Issue #902/#1232: leading "Error:" with few newlines (terse error, not findings doc)
                    )

                    if is_false_positive:
                        if not quiet:
                            console.print(f"[yellow]Provider '{provider}' returned false positive (attempt {attempt}/{max_retries})[/yellow]")
                        # Issue #1376: log false-positive provider replies so the
                        # heuristic-rejection path leaves the same audit trail
                        # as outright failures (was previously silent).
                        _log_agentic_interaction(
                            label=label,
                            prompt=full_instruction,
                            response=output,
                            cost=cost,
                            provider=provider,
                            success=False,
                            duration=time.time() - task_start_time,
                            cwd=cwd,
                            model=effective_model,
                            false_positive=True,
                        )
                        any_attempt_logged_inside = True
                        # Multi-provider configs (default): fall through to the
                        # next provider instead of burning retries on the same
                        # known-broken one.
                        # Single-provider configs (cloud one-session sync runs
                        # anthropic-only) have nowhere to fall through to —
                        # an immediate `break` means zero retries and one
                        # transient empty response fails the whole sync. Retry
                        # on the same provider with backoff up to max_retries.
                        if len(candidates) == 1 and attempt < max_retries:
                            base_backoff = retry_delay * (2 ** (attempt - 1))
                            jitter = random.uniform(0, retry_delay)
                            backoff = min(base_backoff + jitter, MAX_RETRY_DELAY)
                            # Issue #1384: when the false-positive payload
                            # itself looks like a 429 ("Error: api_error_status:
                            # 429 rate limit exceeded"), apply the same 60s
                            # floor as the not-success retry path below.
                            # Without this, a 429 surfaced through the
                            # successful-but-Error-prefixed path retries on
                            # the default 1s/2s/4s schedule, which burns the
                            # retry budget before the per-minute window clears.
                            if _is_rate_limited(stripped_output or ""):
                                backoff = max(backoff, RATE_LIMIT_BACKOFF_FLOOR)
                                if verbose:
                                    console.print(
                                        f"[yellow]Rate-limited (HTTP 429); raising "
                                        f"backoff floor to {RATE_LIMIT_BACKOFF_FLOOR:.0f}s[/yellow]"
                                    )
                            if not quiet:
                                console.print(f"[dim]Single-provider config: retrying in {backoff:.0f}s...[/dim]")
                            time.sleep(backoff)
                            continue
                        break
                    else:
                        # Check for suspicious files (C, E, T)
                        suspicious = []
                        for name in ["C", "E", "T"]:
                            if (cwd / name).exists():
                                suspicious.append(name)

                        if suspicious:
                            console.print(f"[bold red]SUSPICIOUS FILES DETECTED: {', '.join(['- ' + s for s in suspicious])}[/bold red]")

                        # Issue #1376: always emit a summary record so the audit
                        # log answers "which provider/model produced step N?"
                        # without --verbose. Full prompt+response bodies stay
                        # behind verbose to avoid bloating the file with the
                        # same large prompt repeated across every step.
                        _log_agentic_interaction(
                            label=label,
                            prompt=full_instruction,
                            response=output,
                            cost=cost,
                            provider=provider,
                            success=True,
                            duration=time.time() - task_start_time,
                            cwd=cwd,
                            model=effective_model,
                            include_bodies=verbose,
                        )
                        return True, output, cost, provider

                # Issue #902: Skip retries for permanent errors (auth, parameters)
                # Issue #1376 codex round 2: log each failed attempt inside
                # the loop so the audit trail captures every retry, not just
                # the final one. Without this, max_retries=3 with 3 failures
                # produces only one JSONL row — exactly the audit-trail gap
                # this PR set out to close.
                if not success:
                    _log_agentic_interaction(
                        label=label,
                        prompt=full_instruction,
                        response=output,
                        cost=cost,
                        provider=provider,
                        success=False,
                        duration=time.time() - task_start_time,
                        cwd=cwd,
                        model=effective_model,
                    )
                    any_attempt_logged_inside = True

                if not success and _is_permanent_error(output):
                    if verbose:
                        console.print(f"[yellow]Permanent error from {provider}, skipping retries.[/yellow]")
                    break

                # Failed - retry with backoff if attempts remain
                if attempt < max_retries:
                    # Issue #902: Exponential backoff with additive jitter and cap
                    # Delay = base * 2^(attempt-1) + random_jitter
                    base_backoff = retry_delay * (2 ** (attempt - 1))
                    jitter = random.uniform(0, retry_delay)
                    backoff = min(base_backoff + jitter, MAX_RETRY_DELAY)
                    # If the previous attempt was rate-limited, raise the
                    # floor so we wait long enough for the limit to clear
                    # instead of burning the next attempt on the same 429.
                    if _is_rate_limited(last_output or ""):
                        backoff = max(backoff, RATE_LIMIT_BACKOFF_FLOOR)
                        if verbose:
                            console.print(
                                f"[yellow]Rate-limited (HTTP 429); raising "
                                f"backoff floor to {RATE_LIMIT_BACKOFF_FLOOR:.0f}s[/yellow]"
                            )

                    if verbose:
                        console.print(f"[dim]Waiting {backoff:.1f}s before retry...[/dim]")
                    time.sleep(backoff)

            # All retries exhausted (or deadline budget exhausted) for this provider
            provider_errors.append(f"{provider}: {last_output[:MAX_ERROR_SNIPPET_LENGTH]}")
            if verbose:
                console.print(f"[yellow]Provider {provider} failed after {max_retries} attempts: {last_output}[/yellow]")
            # Issue #1072 / #1376 (codex round 2): inline per-attempt logging
            # above already emits one record per provider attempt (success,
            # FP, or failure). This bottom block now only covers the
            # budget-exhausted-before-first-attempt case where no inline log
            # ran — any_attempt_logged_inside stays False from
            # initialization in that path, and we still want a record
            # documenting the provider was skipped.
            if not any_attempt_logged_inside:
                _log_agentic_interaction(
                    label=label,
                    prompt=full_instruction,
                    response=last_output,
                    cost=0.0,
                    provider=provider,
                    success=False,
                    duration=time.time() - task_start_time,
                    cwd=cwd,
                    model=effective_model,
                )
            # If deadline was exhausted, don't try other providers either
            if deadline_exhausted or time.time() > aggregate_deadline:
                break

        return False, f"All agent providers failed: {'; '.join(provider_errors)}", 0.0, ""

    finally:
        # Cleanup prompt file
        if prompt_path.exists():
            try:
                os.remove(prompt_path)
            except OSError:
                pass


import logging as _logging
_scope_guard_logger = _logging.getLogger(__name__ + ".scope_guard")


def _revert_out_of_scope_changes(
    cwd: Path,
    allowed_paths: set[Path],
) -> List[Path]:
    """
    Revert any git-tracked file changes outside the allowed set.

    After an agentic task, this function detects deletions and modifications
    to files not in *allowed_paths* and restores them to their ``HEAD`` state.

    Skips silently when *cwd* is not a git repo, when git is unavailable,
    or when none of the *allowed_paths* reside under *cwd*.

    Args:
        cwd: Root of the git repository.
        allowed_paths: Set of resolved absolute paths the agent is permitted
            to modify.

    Returns:
        List of paths that were reverted.
    """
    cwd_str = str(cwd.resolve())
    if not any(str(p).startswith(cwd_str) for p in allowed_paths):
        return []
    try:
        result = subprocess.run(
            ["git", "-C", str(cwd), "status", "--porcelain", "-uno"],
            capture_output=True, text=True, timeout=30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as exc:
        _scope_guard_logger.warning("Scope guard: git status failed: %s", exc)
        return []
    if result.returncode != 0:
        _scope_guard_logger.warning(
            "Scope guard: git status returned %d: %s",
            result.returncode, result.stderr.strip(),
        )
        return []
    reverted: List[Path] = []
    to_restore: List[str] = []
    for line in result.stdout.splitlines():
        if len(line) < 4:
            continue
        rel_path = line[3:].strip()
        full_path = (cwd / rel_path).resolve()
        if full_path not in allowed_paths:
            to_restore.append(rel_path)
            reverted.append(full_path)
    if to_restore:
        try:
            subprocess.run(
                ["git", "-C", str(cwd), "checkout", "HEAD", "--"] + to_restore,
                capture_output=True, timeout=30,
            )
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as exc:
            _scope_guard_logger.warning(
                "Scope guard: git checkout failed for %d file(s): %s",
                len(to_restore), exc,
            )
            reverted.clear()
        else:
            if reverted:
                _scope_guard_logger.info(
                    "Scope guard reverted %d out-of-scope file(s): %s",
                    len(reverted),
                    ", ".join(str(p.name) for p in reverted[:10]),
                )
    return reverted

_CLAUDE_OAUTH_PROBE_TIMEOUT_SECONDS = 10
_ANTHROPIC_KEY_STRIP_NOTICE_LOGGED: Dict[str, bool] = {}


@functools.lru_cache(maxsize=1)
def _probe_claude_auth_status() -> Dict[str, Any]:
    """Cached `claude auth status` output for OAuth detection (Issue #813).

    Returns ``{}`` on any failure (CLI missing, timeout, non-zero exit, parse
    error, missing subcommand on older Claude Code). Callers must treat that as
    'no OAuth detected' and leave the API key in place.

    Probe runs with ANTHROPIC_API_KEY/ANTHROPIC_AUTH_TOKEN popped to avoid an
    env-supplied key shadowing the OAuth signal in the JSON payload, and uses
    ``subprocess.run`` directly (not ``_subprocess_run``) so it isn't
    intercepted by mocks for the main provider call site.
    """
    cli_path = _find_cli_binary("claude")
    if not cli_path:
        return {}

    probe_env = os.environ.copy()
    probe_env.pop("ANTHROPIC_API_KEY", None)
    probe_env.pop("ANTHROPIC_AUTH_TOKEN", None)

    # Claude Code documents `claude auth status` as the JSON-producing probe.
    # Some versions accepted/required `--json`, while others reject that flag.
    # Try the documented shape first, then fall back to the flag form so either
    # CLI version can still report the stored OAuth credential.
    probe_commands = (
        [cli_path, "auth", "status"],
        [cli_path, "auth", "status", "--json"],
    )

    for command in probe_commands:
        try:
            result = subprocess.run(
                command,
                env=probe_env,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                timeout=_CLAUDE_OAUTH_PROBE_TIMEOUT_SECONDS,
                check=False,
            )
        except (subprocess.TimeoutExpired, OSError):
            return {}

        if result.returncode != 0:
            continue

        try:
            data = json.loads((result.stdout or "").strip())
        except json.JSONDecodeError:
            continue

        if isinstance(data, dict):
            return data

    return {}


_CLAUDE_OAUTH_AUTH_METHODS = frozenset({
    # Local interactive `claude auth login` — keychain-backed Max/Pro OAuth.
    "claude.ai",
    # Env-supplied OAuth (CLAUDE_CODE_OAUTH_TOKEN) — used by the cloud
    # GitHub App executor's waterfall, where the token comes from
    # Secret Manager rather than a keychain login.
    #
    # Caveat: `claude auth status` does not validate the token, so a
    # bogus or stale CLAUDE_CODE_OAUTH_TOKEN still reports loggedIn:true and
    # will trigger our pop. We accept this — the resulting "invalid OAuth
    # token" error is more actionable than the silent shadowing the pop
    # protects against. The cloud waterfall isolates each attempt to one
    # credential type, so the conjunction (bogus token + valid API key)
    # shouldn't arise in production.
    "oauth_token",
})


def _claude_has_oauth_login() -> bool:
    """True when Claude Code has a usable first-party OAuth credential.

    Drives the ANTHROPIC_API_KEY pop in ``_run_with_provider`` (Issue #813).
    ``subscriptionType`` is intentionally not required: API-credit OAuth users
    leave that field null but still want OAuth to win over a stale env key.

    Both keychain OAuth (``authMethod == "claude.ai"``) and env OAuth
    (``authMethod == "oauth_token"``, e.g. ``CLAUDE_CODE_OAUTH_TOKEN``) count
    as OAuth here. Empirical: with both ``CLAUDE_CODE_OAUTH_TOKEN`` and
    ``ANTHROPIC_API_KEY`` set under ``CI=1`` the API key still wins the
    real call (Issue #813's shadowing pattern), so the cloud waterfall
    pattern needs the same protection as local Max users.

    Bedrock/Vertex routes report ``apiProvider != "firstParty"`` and are
    correctly excluded here.
    """
    info = _probe_claude_auth_status()
    return (
        bool(info.get("loggedIn"))
        and info.get("authMethod") in _CLAUDE_OAUTH_AUTH_METHODS
        and info.get("apiProvider") == "firstParty"
    )


def _strip_anthropic_creds_for_claude_subprocess(
    env: Dict[str, str], *, verbose: bool = False, quiet: bool = False
) -> bool:
    """Pop stale ANTHROPIC_API_KEY / ANTHROPIC_AUTH_TOKEN when claude has OAuth.

    Issue #813: PDD always sets ``CI=1`` to keep the claude CLI non-interactive.
    Under ``CI=1``, Claude Code prefers ``ANTHROPIC_API_KEY`` over the user's
    stored OAuth credential, so a depleted key in the parent shell silently
    routes every call to the API tier and fails with 'Credit balance is too
    low' even though ``claude auth status`` still reports the Max account.

    Pop only when an OAuth login is confirmed, so users without OAuth (pure
    API-key setups, including the GitHub App executor that injects keys from
    Secret Manager) keep working unchanged.

    Returns True iff something was popped (for tests and the one-shot notice).

    Provider-scope note: codex/gemini have analogous shadowing risks
    (``codex login status``, ``_has_gemini_oauth_credentials``). They are out
    of scope for this fix; extend here when the symptom is empirically
    reproduced for those providers.
    """
    if env.get("CLAUDE_CODE_USE_BEDROCK") or env.get("CLAUDE_CODE_USE_VERTEX"):
        return False

    # Match common truthy spellings only ("1", "true", "yes", "on" — case-
    # insensitive). Bare-presence checks misread `PDD_KEEP_ANTHROPIC_API_KEY=0`
    # or `=false` as opt-in, defeating the fix in environments where the var
    # is set to a disabling value.
    if (env.get("PDD_KEEP_ANTHROPIC_API_KEY") or "").strip().lower() in {
        "1", "true", "yes", "on",
    }:
        return False

    if not (env.get("ANTHROPIC_API_KEY") or env.get("ANTHROPIC_AUTH_TOKEN")):
        return False

    if not _claude_has_oauth_login():
        return False

    env.pop("ANTHROPIC_API_KEY", None)
    env.pop("ANTHROPIC_AUTH_TOKEN", None)

    # ``quiet`` suppresses both the one-shot notice and the verbose echo to
    # honor the orchestrator's "no non-error output" contract — scripted
    # workflows redirect / parse stdout and a stray dim line breaks them.
    if quiet:
        return True

    if not _ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.get("done"):
        console.print(
            "[dim]Issue #813: dropped ANTHROPIC_API_KEY/AUTH_TOKEN from claude "
            "subprocess env — local OAuth login detected. Set "
            "PDD_KEEP_ANTHROPIC_API_KEY=1 to override.[/dim]"
        )
        _ANTHROPIC_KEY_STRIP_NOTICE_LOGGED["done"] = True
    elif verbose:
        console.print(
            "[dim]Issue #813: dropped ANTHROPIC_API_KEY/AUTH_TOKEN from claude "
            "subprocess env (OAuth detected).[/dim]"
        )
    return True


def _subprocess_run(cmd, *, cwd=None, env=None, input=None, capture_output=False,
                    text=False, timeout=None, start_new_session=False, **kwargs):
    """Wrapper around subprocess that uses Popen for proper process group cleanup.

    Provides a subprocess.run-compatible interface but uses Popen internally
    so we can reliably kill the process group on timeout (Issue #830).
    """
    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        env=env,
        stdin=subprocess.PIPE if input is not None or capture_output else None,
        stdout=subprocess.PIPE if capture_output else None,
        stderr=subprocess.PIPE if capture_output else None,
        text=text,
        start_new_session=start_new_session,
    )
    try:
        stdout, stderr = proc.communicate(input=input, timeout=timeout)
    except subprocess.TimeoutExpired:
        if start_new_session:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (ProcessLookupError, OSError):
                pass
        proc.kill()
        proc.wait(timeout=5)
        raise

    result = subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)
    return result


def _run_with_provider(
    provider: str,
    prompt_path: Path,
    cwd: Path,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
    verbose: bool = False,
    quiet: bool = False,
    cli_path: Optional[str] = None,
    label: str = "",
    use_playwright: bool = False,
    reasoning_time: Optional[float] = None,
) -> Tuple[bool, str, float, Optional[str]]:
    """
    Internal helper to run a specific provider's CLI.
    Returns (success, output_or_error, cost, actual_model).

    Issue #1376: ``actual_model`` is the model name extracted from the
    provider's JSON response (e.g. ``claude-sonnet-4-6``,
    ``gemini-3-flash-preview``, ``gpt-5``). ``None`` when the response did
    not surface a model name (early-exit error paths) — callers blend with
    env-var lookup for "actual or requested" semantics.

    Args:
        provider: Provider name (anthropic, google, openai)
        prompt_path: Path to the prompt file
        cwd: Working directory
        timeout: Timeout in seconds
        verbose: Verbose output
        quiet: Suppress output
        cli_path: Optional explicit CLI path (if None, uses _find_cli_binary)
        label: Task label for heartbeat messages
        use_playwright: Enable constrained tool access for browser testing
        time: Reasoning-allocation float in [0.0, 1.0]. When provided,
            takes precedence over the ``PDD_REASONING_EFFORT`` env var.
            ``None`` means "fall back to env" so unplumbed call sites
            keep receiving the signal via the global variable set by
            ``pdd/core/cli.py``.
    """

    # Prepare Environment
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    env.pop("PDD_OUTPUT_COST_PATH", None)
    # Force CLI agents to stay in the worktree instead of following
    # the .git file pointer back to the main repo (Issue #894).
    env["GIT_WORK_TREE"] = str(cwd)

    # Issue #813: under CI=1 the claude CLI prefers ANTHROPIC_API_KEY over the
    # user's stored OAuth (Max/Pro) credential. Drop a stale key only when an
    # OAuth login is confirmed so API-key-only setups (e.g. GitHub App
    # executor with Secret-Manager-injected keys) still work.
    if provider == "anthropic":
        _strip_anthropic_creds_for_claude_subprocess(env, verbose=verbose, quiet=quiet)

    # Get CLI binary name for this provider
    cli_name = CLI_COMMANDS.get(provider)
    if not cli_name:
        return False, f"Unknown provider {provider}", 0.0, None

    # Find CLI binary path (use explicit path if provided)
    if cli_path is None:
        cli_path = _find_cli_binary(cli_name)
    if not cli_path:
        return False, f"CLI '{cli_name}' not found. {_get_cli_diagnostic_info(cli_name)}", 0.0, None

    cmd: List[str] = []

    # Read prompt content for providers that pipe via stdin
    prompt_content = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else ""

    # Reasoning-effort plumbing. Three input paths converge here, in
    # precedence order:
    # 1. ``CODEX_REASONING_EFFORT`` env var — Codex-specific override, accepts
    #    ``low|medium|high|xhigh`` (xhigh is Codex-only, used by the cloud
    #    worker for GPT-5.4 routing). Only consulted when provider == "openai".
    # 2. Explicit ``reasoning_time`` kwarg threaded down from a command that
    #    saw ``--time`` on argv (cli.py only forwards when ``time_explicit`` is
    #    True, so a default ``ctx.obj["time"]`` does NOT reach here).
    # 3. ``PDD_REASONING_EFFORT`` env var set by pdd/core/cli.py for call
    #    sites that don't thread the kwarg (sync, split, test_generate,
    #    update, verify, crash, etc.).
    # ``CODEX_REASONING_EFFORT`` only fires for the openai branch below; the
    # generic ``reasoning_effort`` resolved here covers paths 2 and 3 and is
    # what the anthropic/gemini logging notices read.
    if reasoning_time is not None:
        from .reasoning import time_to_effort_level
        reasoning_effort = time_to_effort_level(reasoning_time)
    else:
        reasoning_effort = (env.get("PDD_REASONING_EFFORT") or "").strip().lower()
        if reasoning_effort not in {"low", "medium", "high"}:
            reasoning_effort = ""

    # Construct Command using discovered cli_path (Issue #234 fix)
    if provider == "anthropic":
        # Use -p - to pipe prompt as direct user message via stdin.
        # This prevents Claude from interpreting file-discovered instructions
        # as "automated bot workflow" and refusing to execute.
        if use_playwright:
            # Playwright mode: constrained tool access with cost ceiling
            cmd = [
                cli_path,
                "-p", "-",
                "--allowedTools", "Bash", "Read", "Write",
                "--max-turns", "30",
                "--output-format", "json",
            ]
        else:
            cmd = [
                cli_path,
                "-p", "-",
                "--dangerously-skip-permissions",
                "--output-format", "json",
            ]
        # Allow model override via CLAUDE_MODEL env var (Issue #318)
        claude_model = env.get("CLAUDE_MODEL")
        if claude_model:
            cmd.extend(["--model", claude_model])
        if reasoning_effort and not quiet:
            # Always surface outside --quiet mode — silently dropping the user's
            # reasoning signal is a support-ticket generator. The Claude Code CLI
            # has no --reasoning-effort flag today, so clarify that the effort
            # applies to LiteLLM-invoked steps (analysis/verification) but not
            # to this code-writing subprocess.
            console.print(
                f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but Claude Code CLI "
                "has no reasoning-effort flag; applies to llm_invoke steps only, "
                "not this subprocess.[/dim]"
            )
    elif provider == "google":
        # Do NOT use -p flag for Gemini. The -p flag passes text literally,
        # so passing a file path gives Gemini the path string instead of content.
        # Instead, pass a short instruction as positional argument telling Gemini
        # to read the prompt file (matches old _run_google_variants pattern).
        cmd = [
            cli_path,
            f"Read the file {prompt_path.name} for your full instructions and execute them.",
            "--yolo",
            "--output-format", "json"
        ]
        # Allow model override via GEMINI_MODEL env var (mirrors CLAUDE_MODEL for anthropic)
        gemini_model = env.get("GEMINI_MODEL")
        if gemini_model:
            cmd.extend(["--model", gemini_model])
        if reasoning_effort and not quiet:
            # See Claude Code branch above for rationale — same constraint applies.
            console.print(
                f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but Gemini CLI "
                "has no reasoning-effort flag; applies to llm_invoke steps only, "
                "not this subprocess.[/dim]"
            )
    elif provider == "openai":
        # --full-auto sets --sandbox workspace-write (Landlock+seccomp), which
        # panics on gVisor (Cloud Run) and Docker-on-macOS. Since the PDD worker
        # container IS the sandbox boundary, use danger-full-access instead.
        # Ref: https://github.com/openai/codex/issues/6828
        sandbox_mode = env.get("CODEX_SANDBOX_MODE", "danger-full-access")
        cmd = [cli_path]
        # Codex accepts -c / --config only as a top-level flag before the
        # subcommand; appending after "exec" is silently ignored.
        # Codex-specific override: CODEX_REASONING_EFFORT takes precedence
        # over the generic reasoning_effort (kwarg / PDD_REASONING_EFFORT)
        # and additionally accepts ``xhigh`` for GPT-5.4 routing — the
        # cloud worker sets this env var directly when promoting Codex to
        # an extra-high reasoning budget regardless of the user's --time.
        codex_effort = (env.get("CODEX_REASONING_EFFORT") or "").strip().lower()
        if codex_effort in {"low", "medium", "high", "xhigh"}:
            effective_codex_effort: Optional[str] = codex_effort
        elif reasoning_effort:
            effective_codex_effort = reasoning_effort
        else:
            effective_codex_effort = None
        if effective_codex_effort:
            cmd.extend(["-c", f"model_reasoning_effort={effective_codex_effort}"])
        cmd.extend([
            "exec",
            "--sandbox", sandbox_mode,
            "--json",
            str(prompt_path)
        ])
        # Allow model override via CODEX_MODEL env var (mirrors CLAUDE_MODEL for anthropic)
        codex_model = env.get("CODEX_MODEL")
        if codex_model:
            cmd.extend(["--model", codex_model])
    elif provider == "opencode":
        # OpenCode is a multi-provider routing CLI: a single binary that
        # delegates to whichever backend (Anthropic, OpenAI, GitHub Copilot,
        # OpenRouter, etc.) the resolved ``provider/model`` identifier names.
        # Routing requires a model identifier — without it OpenCode has no
        # deterministic default we can rely on, so fail fast with an
        # actionable message instead of letting the CLI surface a generic
        # error far from the configuration source.
        model_id = _resolve_opencode_model_for_run(env, cwd=cwd)
        if not model_id:
            return False, (
                "Cannot resolve an OpenCode model: OPENCODE_MODEL is not set "
                "and no llm_model.csv row matches a configured OpenCode "
                "provider. Set OPENCODE_MODEL to a 'provider/model' identifier "
                "(e.g., 'anthropic/claude-sonnet-4-6', "
                "'openrouter/openai/gpt-5', 'github-copilot/gpt-5'), configure "
                "a provider via `opencode auth login`, or set a backend "
                "provider env var (ANTHROPIC_API_KEY, OPENAI_API_KEY, "
                "GEMINI_API_KEY, OPENROUTER_API_KEY, GITHUB_TOKEN, ...)."
            ), 0.0, None
        translated_model = _translate_to_opencode_model(model_id)
        cmd = [
            cli_path,
            "run",
            "--dir", str(cwd),
            "--format", "json",
            "--dangerously-skip-permissions",
            "--model", translated_model,
        ]
        agent_name = (env.get("OPENCODE_AGENT") or "").strip()
        if agent_name:
            cmd.extend(["--agent", agent_name])
        variant_name = (env.get("OPENCODE_VARIANT") or "").strip()
        if variant_name:
            cmd.extend(["--variant", variant_name])
        # The OpenCode CLI requires a positional ``message`` argument for
        # ``opencode run`` (https://opencode.ai/docs/cli/) — earlier revisions
        # passed only ``--`` and piped the prompt body on stdin, which the CLI
        # does not consume in non-interactive mode. The full prompt is in
        # ``prompt_path``; pass only a short directive on argv so large issue
        # prompts cannot exceed OS argv limits while OpenCode still receives a
        # valid trailing message. Using ``--`` first ensures the directive is
        # parsed as the message and not a flag.
        cmd.append("--")
        cmd.append(
            f"Read the file {prompt_path.name} for your full instructions and execute them."
        )
    else:
        return False, f"Unknown provider {provider}", 0.0, None

    # For anthropic, pipe prompt content via stdin; others use file path in cmd.
    # OpenCode reads the prompt from the file referenced in the trailing
    # message argv, so it does NOT receive the body via stdin.
    stdin_content = prompt_content if provider == "anthropic" else None

    try:
        result = _subprocess_run(
            cmd,
            cwd=cwd,
            env=env,
            input=stdin_content,
            capture_output=True,
            text=True,
            timeout=timeout,
            start_new_session=True,
        )
    except subprocess.TimeoutExpired:
        return False, "Timeout expired", 0.0, None
    except Exception as e:
        return False, str(e), 0.0, None

    if result.returncode != 0:
        error_detail = result.stderr or result.stdout[:500]
        if provider == "openai":
            combined_error = "\n".join(
                part for part in [
                    result.stderr or "",
                    (result.stdout or "")[:MAX_ERROR_SNIPPET_LENGTH],
                ]
                if part
            )
            codex_auth_message = _codex_auth_failure_message(combined_error)
            if codex_auth_message:
                return False, codex_auth_message, 0.0, None
        return False, f"Exit code {result.returncode}: {error_detail}", 0.0, None

    # OpenCode: parse JSONL output via the dedicated parser. OpenCode emits a
    # different event schema than Codex/Claude (step_start, text, step_finish,
    # error...) and routes cost via ``step_finish.part.cost``, so it doesn't
    # belong in the shared single-JSON / Codex-NDJSON path below.
    if provider == "opencode":
        parsed = _parse_opencode_jsonl(result.stdout)
        actual_model = parsed.get("model") or None
        err = parsed.get("error") or ""
        # Cost: prefer JSONL-reported cost; fall back to CSV pricing when
        # OpenCode did not surface a cost field (some backends/sessions omit
        # ``step_finish.part.cost``). Returning $0.00 for a successful run
        # silently breaks cost-accounting acceptance.
        if parsed.get("cost_reported"):
            cost = float(parsed.get("cost") or 0.0)
        else:
            tokens = parsed.get("tokens") or {}
            csv_model_id = actual_model or _resolve_opencode_model_for_run(env, cwd=cwd)
            cost = _opencode_csv_cost(csv_model_id, tokens)
        if err:
            # An error event with returncode==0 still represents a routing /
            # provider failure inside OpenCode (e.g., "provider not
            # configured"). Surface as failure, but keep cost and any
            # captured model so callers can audit partial spend.
            return False, str(err), cost, actual_model
        return (
            True,
            str(parsed.get("text") or ""),
            cost,
            actual_model,
        )

    # Diagnostic: capture when CLI exits 0 with empty / whitespace-only stdout.
    # Cloud one-session sync runs hit "All agent providers failed: anthropic: "
    # with a blank provider error and no log trail. Stderr tail + prompt size
    # + auth-key presence is usually enough to tell apart auth failures, rate
    # limits, and genuine empty responses.
    if not result.stdout.strip():
        auth_keys_present = sorted(
            k for k in env
            if ("TOKEN" in k or "API_KEY" in k) and env.get(k)
        )
        stderr_tail = (result.stderr or "")[-500:]
        console.print(
            f"[bold red]Provider {provider} returned exit 0 with EMPTY stdout[/bold red]"
        )
        console.print(
            f"[dim]stderr_tail={stderr_tail!r} prompt_chars={len(stdin_content or '')} "
            f"auth_keys={auth_keys_present} cwd={cwd}[/dim]"
        )

    # Parse JSON Output
    try:
        # Handle JSONL output (Codex sometimes streams)
        output_str = result.stdout.strip()
        data = {}
        
        if provider == "openai" and "\n" in output_str:
            # Parse NDJSON, collecting both the agent response and usage stats
            lines = output_str.splitlines()
            agent_message_data = None
            session_end = None
            for line in lines:
                try:
                    item = json.loads(line)
                    # Legacy Codex format: single event contains both text and usage
                    if item.get("type") == "result":
                        data = item
                        break
                    # Modern Codex CLI (0.104.0+): text in item.completed agent_message
                    if (item.get("type") == "item.completed"
                            and isinstance(item.get("item"), dict)
                            and item["item"].get("type") == "agent_message"):
                        agent_message_data = item
                    # usage/cost stats are in session.end or turn.completed
                    # (Codex CLI 0.105.0+ uses turn.completed instead of session.end)
                    if item.get("type") in ("session.end", "turn.completed"):
                        session_end = item
                except json.JSONDecodeError:
                    continue
            if not data:
                if agent_message_data is not None:
                    # Merge usage AND model from session.end so cost calculation
                    # works AND the audit log captures the actual model name
                    # (Issue #1376 codex round 3: previously only `usage` was
                    # carried over, so default-model Codex runs logged
                    # `model: null` because session.end.model was discarded).
                    if session_end is not None:
                        merged: Dict[str, Any] = {**agent_message_data}
                        if "usage" in session_end:
                            merged["usage"] = session_end.get("usage", {})
                        if "model" in session_end:
                            merged["model"] = session_end.get("model")
                        data = merged
                    else:
                        data = agent_message_data
                elif session_end is not None:
                    data = session_end
                elif lines:
                    try:
                        data = json.loads(lines[-1])
                    except:
                        pass
        else:
            # Claude Code may emit non-JSON text to stdout (npm warnings,
            # upgrade prompts) alongside the JSON result.  Try parsing as
            # single JSON first, then fall back to line-by-line extraction.
            try:
                data = json.loads(output_str)
            except json.JSONDecodeError:
                data = _extract_json_from_output(output_str)

        success, text, cost, actual_model = _parse_provider_json(provider, data)
        if cost == 0.0 and verbose and isinstance(data, dict):
            console.print(
                f"[dim]Warning: {provider} returned $0 cost. "
                f"JSON keys: {sorted(data.keys())}[/dim]"
            )
        return success, text, cost, actual_model
    except json.JSONDecodeError:
        # Fallback if CLI didn't output valid JSON (sometimes happens on crash)
        return False, f"Invalid JSON output: {result.stdout[:MAX_ERROR_SNIPPET_LENGTH]}...", 0.0, None


def _extract_json_from_output(output_str: str) -> dict:
    """Extract a JSON object from output that may contain non-JSON text.

    Claude Code may emit non-JSON text to stdout (npm warnings, upgrade
    prompts) alongside the JSON result.  Try line-by-line extraction first,
    then fall back to brace-depth matching on the full string.

    Raises ``json.JSONDecodeError`` if no valid JSON object can be found.
    """
    # Try each line individually
    for line in output_str.splitlines():
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            return json.loads(line)
        except json.JSONDecodeError:
            continue

    # Fallback: brace-depth matching to find the first complete JSON object
    depth = 0
    start_index: Optional[int] = None
    in_string = False
    escape = False

    for i, ch in enumerate(output_str):
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue

        if ch == '"':
            in_string = True
            continue

        if ch == "{":
            if depth == 0:
                start_index = i
            depth += 1
        elif ch == "}" and depth > 0:
            depth -= 1
            if depth == 0 and start_index is not None:
                candidate = output_str[start_index : i + 1]
                try:
                    return json.loads(candidate)
                except json.JSONDecodeError:
                    start_index = None
                    continue

    raise json.JSONDecodeError(
        "No valid JSON object found in output", output_str[:200], 0
    )


def _extract_provider_model_from_data(provider: str, data: Dict[str, Any]) -> Optional[str]:
    """Extract the actual model name from a provider's JSON response.

    Issue #1376 codex review (P2): supplements ``_get_provider_model`` (env-var
    only) so the audit log can record the model the provider *actually* used,
    not just the one the user asked for. Falls back to ``None`` when the JSON
    doesn't expose a model name; callers blend with env-var lookup for a
    "actual or requested" view.

    - Anthropic: keys of ``modelUsage`` (Claude Code emits one entry per model
      it routed through; if multiple, joins with ``+`` for transparency).
    - Google: keys of ``stats.models`` (Gemini CLI emits one entry per model).
    - OpenAI: ``data["model"]`` (Codex CLI surfaces it on the result envelope).
    """
    if not isinstance(data, dict):
        return None
    try:
        if provider == "anthropic":
            usage = data.get("modelUsage")
            if isinstance(usage, dict) and usage:
                names = [str(k) for k in usage.keys() if k]
                if names:
                    return "+".join(sorted(names)) if len(names) > 1 else names[0]
        elif provider == "google":
            models = (data.get("stats") or {}).get("models")
            if isinstance(models, dict) and models:
                names = [str(k) for k in models.keys() if k]
                if names:
                    return "+".join(sorted(names)) if len(names) > 1 else names[0]
        elif provider == "openai":
            model = data.get("model")
            if isinstance(model, str) and model:
                return model
            # Fallback: some Codex schemas place model on session.end / item
            for nested_key in ("session", "item"):
                nested = data.get(nested_key)
                if isinstance(nested, dict):
                    nm = nested.get("model")
                    if isinstance(nm, str) and nm:
                        return nm
    except Exception:
        return None
    return None


def _parse_provider_json(
    provider: str, data: Dict[str, Any]
) -> Tuple[bool, str, float, Optional[str]]:
    """
    Extracts (success, text_response, cost_usd, actual_model) from provider JSON.

    Issue #1376: returns the model the provider actually used (when the JSON
    response carries it) so the audit log can answer "which provider/model
    produced step N?" without relying on env-var overrides.
    """
    cost = 0.0
    output_text = ""
    actual_model = _extract_provider_model_from_data(provider, data)

    try:
        if provider == "anthropic":
            # Use total_cost_usd if available, otherwise estimate from token usage
            cost = float(data.get("total_cost_usd", 0.0))
            if cost == 0.0:
                cost = _calculate_anthropic_cost(data)
            # Result might be in 'result' or 'response'
            output_text = data.get("result") or data.get("response") or ""
            # Claude Code JSON includes is_error when the session failed
            # (auth, refusal, crash). Propagate as failure so callers can
            # retry or fall through instead of treating it as success.
            if data.get("is_error"):
                return False, str(output_text) or "CLI reported is_error with no message", cost, actual_model

        elif provider == "google":
            stats = data.get("stats", {})
            cost = _calculate_gemini_cost(stats)
            output_text = data.get("result") or data.get("response") or data.get("output") or ""

        elif provider == "openai":
            usage = data.get("usage", {})
            cost = _calculate_codex_cost(usage)
            # Modern Codex CLI (0.104.0+): text at data["item"]["text"]
            item = data.get("item", {})
            if isinstance(item, dict) and item.get("type") == "agent_message":
                output_text = item.get("text", "")
            else:
                output_text = data.get("result") or data.get("output") or ""

        return True, str(output_text), cost, actual_model

    except Exception as e:
        return False, f"Error parsing {provider} JSON: {e}", 0.0, actual_model


# --- GitHub State Persistence ---

def _build_state_marker(workflow_type: str, issue_number: int) -> str:
    return f"{GITHUB_STATE_MARKER_START}{workflow_type}:issue-{issue_number}"

def _serialize_state_comment(workflow_type: str, issue_number: int, state: Dict) -> str:
    marker = _build_state_marker(workflow_type, issue_number)
    json_str = json.dumps(state, indent=2)
    return f"{marker}\n{json_str}\n{GITHUB_STATE_MARKER_END}"

def _parse_state_from_comment(body: str, workflow_type: str, issue_number: int) -> Optional[Dict]:
    marker = _build_state_marker(workflow_type, issue_number)
    if marker not in body:
        return None
    
    try:
        # Extract content between marker and end marker
        start_idx = body.find(marker) + len(marker)
        end_idx = body.find(GITHUB_STATE_MARKER_END, start_idx)
        
        if end_idx == -1:
            return None
            
        json_str = body[start_idx:end_idx].strip()
        return json.loads(json_str)
    except (json.JSONDecodeError, ValueError):
        return None

def _find_state_comment(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    cwd: Path
) -> Optional[Tuple[int, Dict]]:
    """
    Returns (comment_id, state_dict) if found, else None.
    """
    if not _find_cli_binary("gh"):
        return None

    try:
        # List comments
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
            "--method", "GET",
            "--paginate"
        ]
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        if result.returncode != 0:
            return None
            
        comments = json.loads(result.stdout)
        marker = _build_state_marker(workflow_type, issue_number)
        
        for comment in comments:
            body = comment.get("body", "")
            if marker in body:
                state = _parse_state_from_comment(body, workflow_type, issue_number)
                if state:
                    return comment["id"], state
                    
        return None
    except Exception:
        return None

def github_save_state(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    state: Dict, 
    cwd: Path, 
    comment_id: Optional[int] = None
) -> Optional[int]:
    """
    Creates or updates a GitHub comment with the state. Returns new/existing comment_id.
    """
    if not _find_cli_binary("gh"):
        return None

    body = _serialize_state_comment(workflow_type, issue_number, state)
    
    try:
        if comment_id:
            # PATCH existing
            cmd = [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
                "-X", "PATCH",
                "-f", f"body={body}"
            ]
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            if res.returncode == 0:
                return comment_id
        else:
            # POST new
            cmd = [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
                "-X", "POST",
                "-f", f"body={body}"
            ]
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            if res.returncode == 0:
                data = json.loads(res.stdout)
                return data.get("id")
                
        return None
    except Exception:
        return None

def github_load_state(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    cwd: Path
) -> Tuple[Optional[Dict], Optional[int]]:
    """
    Wrapper to find state. Returns (state, comment_id).
    """
    result = _find_state_comment(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if result:
        return result[1], result[0]
    return None, None

def github_clear_state(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    cwd: Path
) -> bool:
    """
    Deletes the state comment if it exists.
    """
    result = _find_state_comment(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if not result:
        return True # Already clear
        
    comment_id = result[0]
    try:
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
            "-X", "DELETE"
        ]
        subprocess.run(cmd, cwd=cwd, capture_output=True)
        return True
    except Exception:
        return False

def _should_use_github_state(use_github_state: bool) -> bool:
    if not use_github_state:
        return False
    if os.environ.get("PDD_NO_GITHUB_STATE") == "1":
        return False
    return True

# --- Cached State Validation (Issue #467) ---

def validate_cached_state(
    last_completed_step: Union[int, float],
    step_outputs: Dict[str, str],
    step_order: Optional[List[Union[int, float]]] = None,
    quiet: bool = False,
) -> Union[int, float]:
    """Validate cached state and return actual last successful step.

    Scans step_outputs for entries with "FAILED:" prefix and corrects
    last_completed_step to the actual last successfully completed step.
    This prevents the "blind resume" bug (Issue #467) where the orchestrator
    trusts a corrupted last_completed_step and skips failed steps.

    Args:
        last_completed_step: The stored last_completed_step value.
        step_outputs: Dict mapping step number strings to output strings.
        step_order: Ordered list of step numbers. If None, derived from
            step_outputs keys sorted numerically.
        quiet: If False, prints a warning when correction is applied.

    Returns:
        The corrected last_completed_step value.
    """
    if not step_outputs:
        return last_completed_step

    if step_order is None:
        # Derive order from keys, sorted numerically
        # Filter out non-numeric keys (e.g. "1b", "2b", "7b", "9b") that
        # are informational intermediate-step outputs — only numeric keys
        # (e.g. "1", "1.5", "2", "7.5") participate in validation ordering.
        numeric_keys = []
        for k in step_outputs.keys():
            try:
                float(k)
                numeric_keys.append(k)
            except ValueError:
                continue
        step_order = sorted(numeric_keys, key=lambda k: float(k))
    else:
        # Convert to string keys for lookup
        step_order = [str(s) if not isinstance(s, str) else s for s in step_order]

    actual_last_success: Union[int, float] = 0
    for sn in step_order:
        key = str(sn)
        output_val = step_outputs.get(key, "")
        if not output_val:
            break
        if str(output_val).startswith("FAILED:"):
            break
        # Parse back to numeric for comparison
        try:
            actual_last_success = float(key) if "." in key else int(key)
        except ValueError:
            actual_last_success = 0

    if actual_last_success < last_completed_step:
        if not quiet:
            console.print(
                f"[yellow]State validation: correcting last_completed_step "
                f"from {last_completed_step} to {actual_last_success} "
                f"(found FAILED steps in cache)[/yellow]"
            )
        return actual_last_success

    return last_completed_step


# --- High Level State Wrappers ---

def load_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True
) -> Tuple[Optional[Dict], Optional[int]]:
    """
    Loads state from GitHub (priority) or local file.
    Returns (state_dict, github_comment_id).
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    # Try GitHub first
    if _should_use_github_state(use_github_state):
        gh_state, gh_id = github_load_state(repo_owner, repo_name, issue_number, workflow_type, cwd)
        if gh_state:
            # Cache locally
            try:
                state_dir.mkdir(parents=True, exist_ok=True)
                with open(local_file, "w") as f:
                    json.dump(gh_state, f, indent=2)
            except Exception:
                pass # Ignore local cache errors
            return gh_state, gh_id
    # Fallback to local
    if local_file.exists():
        try:
            with open(local_file, "r") as f:
                return json.load(f), None
        except Exception:
            pass
            
    return None, None

def save_workflow_state(
    cwd: Path, 
    issue_number: int, 
    workflow_type: str, 
    state: Dict, 
    state_dir: Path, 
    repo_owner: str, 
    repo_name: str, 
    use_github_state: bool = True, 
    github_comment_id: Optional[int] = None
) -> Optional[int]:
    """
    Saves state to local file and GitHub.
    Returns updated github_comment_id.
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"
    
    # 1. Save Local (atomic: write to tmp then rename)
    try:
        state_dir.mkdir(parents=True, exist_ok=True)
        tmp_file = local_file.with_suffix(".json.tmp")
        with open(tmp_file, "w") as f:
            json.dump(state, f, indent=2)
        tmp_file.replace(local_file)  # atomic on POSIX
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to save local state: {e}[/yellow]")

    # 2. Save GitHub
    if _should_use_github_state(use_github_state):
        new_id = github_save_state(
            repo_owner, repo_name, issue_number, workflow_type, state, cwd, github_comment_id
        )
        if new_id:
            return new_id
        else:
            console.print("[dim]Warning: Failed to sync state to GitHub[/dim]")
            return None

    return github_comment_id

def clear_workflow_state(
    cwd: Path, 
    issue_number: int, 
    workflow_type: str, 
    state_dir: Path, 
    repo_owner: str, 
    repo_name: str, 
    use_github_state: bool = True
) -> None:
    """
    Clears local and GitHub state.
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"
    
    # Clear Local
    if local_file.exists():
        try:
            os.remove(local_file)
        except Exception:
            pass

    # Clear GitHub
    if _should_use_github_state(use_github_state):
        github_clear_state(repo_owner, repo_name, issue_number, workflow_type, cwd)


def post_step_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    step_num: int,
    total_steps: int,
    description: str,
    output: str,
    cwd: Path,
) -> bool:
    """
    Post a fallback comment on a GitHub issue when a step fails.

    When the LLM agent fails (e.g., all providers unavailable), the agent never
    runs and therefore never posts its own step comment. This function posts a
    fallback comment so users can see which steps failed and why.

    Args:
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        issue_number: Issue number to comment on
        step_num: Current step number
        total_steps: Total number of steps in the workflow
        description: Human-readable step description
        output: Error output / failure details
        cwd: Working directory for subprocess

    Returns:
        True if comment was posted successfully, False otherwise
    """
    if not _find_cli_binary("gh"):
        return False

    # Truncate output to avoid exceeding GitHub comment size limits
    error_detail = output[:1000] if len(output) > 1000 else output

    body = (
        f"## Step {step_num}/{total_steps}: {description}\n\n"
        f"**Status:** FAILED\n\n"
        f"### Error Details\n"
        f"```\n{error_detail}\n```\n\n"
        f"---\n"
        f"*Automated fallback comment — agent did not execute for this step.*"
    )

    try:
        result = subprocess.run(
            [
                "gh", "issue", "comment", str(issue_number),
                "--repo", f"{repo_owner}/{repo_name}",
                "--body", body,
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            console.print(f"[yellow]Warning: Failed to post fallback comment for step {step_num}: {result.stderr}[/yellow]")
            return False
        return True
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to post fallback comment for step {step_num}: {e}[/yellow]")
        return False


def post_pr_comment(
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    body: str,
    cwd: Path,
) -> bool:
    """
    Post a comment on a pull request.

    Args:
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        pr_number: Pull request number to comment on
        body: Comment body
        cwd: Working directory for subprocess

    Returns:
        True if comment was posted successfully, False otherwise
    """
    if not _find_cli_binary("gh"):
        return False

    try:
        result = subprocess.run(
            [
                "gh", "pr", "comment", str(pr_number),
                "--repo", f"{repo_owner}/{repo_name}",
                "--body", body,
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            console.print(f"[yellow]Warning: Failed to post PR comment: {result.stderr}[/yellow]")
            return False
        return True
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to post PR comment: {e}[/yellow]")
        return False


def post_final_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    reason: str,
    total_cost: float,
    steps_completed: int,
    total_steps: int,
    cwd: Path,
) -> bool:
    """
    Post a final status comment when the workflow stops early.

    Unlike post_step_comment (which is for step-level failures where the agent
    didn't execute), this is for workflow-level outcomes: NOT_A_BUG, max cycles
    exhausted, missing loop control token, etc.

    Args:
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        issue_number: Issue number to comment on
        reason: Human-readable reason the workflow stopped
        total_cost: Total LLM cost incurred
        steps_completed: Last completed step number
        total_steps: Total number of steps in the workflow
        cwd: Working directory for subprocess

    Returns:
        True if comment was posted successfully, False otherwise
    """
    if not _find_cli_binary("gh"):
        return False

    body = (
        f"## Workflow Stopped\n\n"
        f"**Reason:** {reason}\n\n"
        f"**Progress:** Completed through step {steps_completed}/{total_steps}\n"
        f"**Total cost:** ${total_cost:.4f}\n\n"
        f"---\n"
        f"*Automated status comment — pdd-fix workflow exited early.*"
    )

    try:
        result = subprocess.run(
            [
                "gh", "issue", "comment", str(issue_number),
                "--repo", f"{repo_owner}/{repo_name}",
                "--body", body,
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            console.print(f"[yellow]Warning: Failed to post final comment: {result.stderr}[/yellow]")
            return False
        return True
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to post final comment: {e}[/yellow]")
        return False
