from __future__ import annotations

import os
import sys
import json
import time
import random
import signal
import uuid

import shutil
import socket
import subprocess
import re
import glob
import hashlib
from pathlib import Path
from datetime import datetime, timezone
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any, Tuple, Union, Set

from rich.console import Console

from .reasoning import time_to_effort_level

console = Console()

# -----------------------------------------------------------------------------
# Constants
# -----------------------------------------------------------------------------

DEFAULT_TIMEOUT_SECONDS: float = 600.0
MIN_VALID_OUTPUT_LENGTH: int = 50
DEFAULT_MAX_RETRIES: int = 3
DEFAULT_RETRY_DELAY: float = 5.0
MAX_RETRY_DELAY: float = 120.0
JOB_TIMEOUT_MARGIN_SECONDS: float = 120.0
MIN_ATTEMPT_TIMEOUT_SECONDS: float = 60.0
MAX_ERROR_SNIPPET_LENGTH: int = 2000
MAX_ERROR_RESPONSE_NEWLINES: int = 3
_SEMANTIC_TAIL_LINES: int = 30
AGENTIC_LOG_DIR: str = ".pdd/agentic-logs"

_DEFAULT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai", "opencode"]

_PROVIDER_TO_CLI: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
    "opencode": "opencode",
}
CLI_COMMANDS: Dict[str, str] = dict(_PROVIDER_TO_CLI)

_AUTH_KEY_HINTS: Tuple[str, ...] = ("TOKEN", "API_KEY")

class _CliPathRegistry(list):
    """List-like common path registry with per-CLI test override support."""

    def __init__(self, paths: List[str]) -> None:
        super().__init__(paths)
        self._overrides: Dict[str, List[str]] = {}

    def get(self, name: str, default: Optional[List[str]] = None) -> List[str]:
        if name in self._overrides:
            return list(self._overrides[name])
        if isinstance(default, list):
            return list(default)
        return list(self)

    def __setitem__(self, key: Union[int, slice, str], value: Any) -> None:
        if isinstance(key, str):
            vals = value if isinstance(value, list) else [value]
            self._overrides[key] = [str(v) for v in vals]
            return
        super().__setitem__(key, value)

    def __delitem__(self, key: Union[int, slice, str]) -> None:
        if isinstance(key, str):
            self._overrides.pop(key, None)
            return
        super().__delitem__(key)

    def paths_for(self, name: str) -> List[str]:
        return self.get(name, list(self))


_COMMON_CLI_PATHS: _CliPathRegistry = _CliPathRegistry([
    "/usr/local/bin",
    "/usr/bin",
    "/opt/homebrew/bin",
    str(Path.home() / ".local" / "bin"),
    str(Path.home() / ".npm-global" / "bin"),
    str(Path.home() / "node_modules" / ".bin"),
])
_OPENCODE_AUTH_PATH: Path = Path.home() / ".local" / "share" / "opencode" / "auth.json"

# Add nvm bin paths via glob
try:
    _COMMON_CLI_PATHS.extend(
        sorted(glob.glob(str(Path.home() / ".nvm" / "versions" / "node" / "*" / "bin")))
    )
except Exception:
    pass


# -----------------------------------------------------------------------------
# Pricing
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Pricing:
    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 1.0


GEMINI_PRICING: Dict[str, Pricing] = {
    "flash": Pricing(0.35, 1.05, 0.5),
    "pro": Pricing(3.50, 10.50, 0.5),
}
CODEX_PRICING: Pricing = Pricing(1.50, 6.00, 0.25)
ANTHROPIC_PRICING: Dict[str, Pricing] = {
    "opus": Pricing(15.0, 75.0, 0.1),
    "sonnet": Pricing(3.0, 15.0, 0.1),
    "haiku": Pricing(0.8, 4.0, 0.1),
}
GEMINI_PRICING_BY_FAMILY: Dict[str, Pricing] = GEMINI_PRICING
ANTHROPIC_PRICING_BY_FAMILY: Dict[str, Pricing] = ANTHROPIC_PRICING


def _estimate_cost(input_tokens: int, output_tokens: int, pricing: Pricing,
                   cached_tokens: int = 0, cache_write_tokens: int = 0,
                   anthropic: bool = False) -> float:
    if anthropic:
        new_input = max(0, input_tokens - cached_tokens - cache_write_tokens)
        cost = (
            new_input * pricing.input_per_million / 1_000_000
            + cached_tokens * pricing.input_per_million * pricing.cached_input_multiplier / 1_000_000
            + cache_write_tokens * pricing.input_per_million * 1.25 / 1_000_000
            + output_tokens * pricing.output_per_million / 1_000_000
        )
    else:
        new_input = max(0, input_tokens - cached_tokens)
        cost = (
            new_input * pricing.input_per_million / 1_000_000
            + cached_tokens * pricing.input_per_million * pricing.cached_input_multiplier / 1_000_000
            + output_tokens * pricing.output_per_million / 1_000_000
        )
    return cost


def _estimate_tokens_from_text(text: str) -> int:
    """Crude estimation: ~4 chars per token."""
    return max(1, len(text) // 4)


def _coerce_int(value: Any) -> int:
    try:
        return int(value or 0)
    except (TypeError, ValueError):
        return 0


def _first_int(mapping: Dict[str, Any], *keys: str) -> int:
    for key in keys:
        if key in mapping:
            return _coerce_int(mapping.get(key))
    return 0


def _pricing_family(model_name: str, pricing_table: Dict[str, Pricing], default: str) -> Pricing:
    lower = (model_name or "").lower()
    for family, pricing in pricing_table.items():
        if family in lower:
            return pricing
    return pricing_table[default]


def _calculate_gemini_cost(stats: Dict[str, Any]) -> float:
    models = stats.get("models") if isinstance(stats, dict) else None
    if not isinstance(models, dict):
        return 0.0
    cost = 0.0
    for model_name, model_stats in models.items():
        if not isinstance(model_stats, dict):
            continue
        explicit_cost = model_stats.get("cost")
        if explicit_cost is not None:
            try:
                cost += float(explicit_cost)
                continue
            except (TypeError, ValueError):
                pass
        tokens = model_stats.get("tokens") or {}
        if not isinstance(tokens, dict):
            continue
        input_tokens = int(tokens.get("input", tokens.get("prompt", 0)) or 0)
        output_tokens = int(tokens.get("output", tokens.get("candidates", 0)) or 0)
        cached_tokens = int(tokens.get("cached", tokens.get("cached_input_tokens", 0)) or 0)
        pricing = _pricing_family(str(model_name), GEMINI_PRICING, "flash")
        cost += _estimate_cost(input_tokens, output_tokens, pricing, cached_tokens=cached_tokens)
    return cost


def _calculate_codex_cost(usage: Dict[str, Any]) -> float:
    if not isinstance(usage, dict):
        return 0.0
    input_tokens = _first_int(usage, "input_tokens", "prompt_tokens", "input")
    output_tokens = _first_int(usage, "output_tokens", "completion_tokens", "output")
    cached_tokens = _first_int(usage, "cached_input_tokens", "cached_tokens", "cached")
    return _estimate_cost(input_tokens, output_tokens, CODEX_PRICING, cached_tokens=cached_tokens)


def _calculate_anthropic_cost(data: Dict[str, Any]) -> float:
    if not isinstance(data, dict):
        return 0.0
    direct_cost = data.get("total_cost_usd")
    if direct_cost is not None:
        try:
            parsed_direct_cost = float(direct_cost)
            # Claude subscription auth reports 0 even when token usage is present.
            if parsed_direct_cost > 0:
                return parsed_direct_cost
        except (TypeError, ValueError):
            pass

    model_usage = data.get("modelUsage") or {}
    model_family = "sonnet"
    cost = 0.0
    estimated_model_usage_cost = 0.0
    saw_model_usage_tokens = False
    if isinstance(model_usage, dict):
        for model_name, usage in model_usage.items():
            model_text = str(model_name).lower()
            model_family = "opus" if "opus" in model_text else (
                "haiku" if "haiku" in model_text else model_family
            )
            if not isinstance(usage, dict):
                continue

            explicit = usage.get("costUSD", usage.get("cost"))
            if explicit is not None:
                try:
                    cost += float(explicit)
                    continue
                except (TypeError, ValueError):
                    pass

            input_tokens = _first_int(usage, "inputTokens", "input_tokens", "promptTokens", "prompt_tokens")
            output_tokens = _first_int(usage, "outputTokens", "output_tokens", "completionTokens", "completion_tokens")
            cache_read = _first_int(
                usage,
                "cacheReadInputTokens",
                "cache_read_input_tokens",
                "cache_read_tokens",
            )
            cache_write = _first_int(
                usage,
                "cacheCreationInputTokens",
                "cache_creation_input_tokens",
                "cache_write_tokens",
            )
            if input_tokens or output_tokens or cache_read or cache_write:
                saw_model_usage_tokens = True
                pricing = _pricing_family(str(model_name), ANTHROPIC_PRICING, "sonnet")
                estimated_model_usage_cost += _estimate_cost(
                    input_tokens,
                    output_tokens,
                    pricing,
                    cached_tokens=cache_read,
                    cache_write_tokens=cache_write,
                    anthropic=True,
                )
        if cost:
            return cost

    usage = data.get("usage") or {}
    if isinstance(usage, dict):
        input_tokens = _first_int(usage, "input_tokens", "inputTokens")
        output_tokens = _first_int(usage, "output_tokens", "outputTokens")
        cache_read = _first_int(usage, "cache_read_input_tokens", "cacheReadInputTokens")
        cache_write = _first_int(usage, "cache_creation_input_tokens", "cacheCreationInputTokens")
        if input_tokens or output_tokens or cache_read or cache_write:
            pricing = ANTHROPIC_PRICING[model_family]
            return _estimate_cost(
                input_tokens,
                output_tokens,
                pricing,
                cached_tokens=cache_read,
                cache_write_tokens=cache_write,
                anthropic=True,
            )

    if saw_model_usage_tokens:
        return estimated_model_usage_cost
    return 0.0


# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

def _load_agentic_config() -> Dict[str, Any]:
    """Load .pddrc agentic section if present."""
    config: Dict[str, Any] = {}
    pddrc_path = Path.cwd() / ".pddrc"
    if not pddrc_path.exists():
        pddrc_path = Path.home() / ".pddrc"
    if not pddrc_path.exists():
        return config
    try:
        try:
            import yaml  # type: ignore
            with open(pddrc_path, "r", encoding="utf-8") as f:
                data = yaml.safe_load(f) or {}
        except ImportError:
            with open(pddrc_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        if isinstance(data, dict):
            config = data.get("agentic", {}) or {}
    except Exception:
        pass
    return config


def _resolve_model_csv_path() -> Path:
    """Return the active llm_model.csv path using PDD's catalog precedence.

    Mirrors ``llm_invoke``'s resolution: prefer ``~/.pdd/llm_model.csv``,
    then ``<cwd>/.pdd/llm_model.csv``, otherwise fall back to the bundled
    ``pdd/data/llm_model.csv``. This lets users who ran ``pdd setup`` or who
    maintain custom pricing/provider rows have those models considered when
    PDD resolves an OpenCode model.
    """
    user_csv = Path.home() / ".pdd" / "llm_model.csv"
    if user_csv.is_file():
        return user_csv
    try:
        project_csv = Path.cwd() / ".pdd" / "llm_model.csv"
    except Exception:
        project_csv = None  # type: ignore[assignment]
    if project_csv is not None and project_csv.is_file():
        return project_csv
    return Path(__file__).parent / "data" / "llm_model.csv"


def _load_model_data(path: Optional[Union[str, Path]] = None) -> Optional[List[Dict[str, str]]]:
    """Load model CSV metadata when available.

    When ``path`` is ``None`` the catalog is resolved using
    :func:`_resolve_model_csv_path` so that user/project overrides at
    ``~/.pdd/llm_model.csv`` or ``<cwd>/.pdd/llm_model.csv`` win over the
    bundled default, matching ``llm_invoke``'s precedence.
    """
    try:
        import csv
        csv_path = Path(path) if path is not None else _resolve_model_csv_path()
        if not csv_path.is_file():
            return None
        with open(csv_path, "r", encoding="utf-8") as f:
            return list(csv.DictReader(f))
    except Exception:
        return None


def get_agent_provider_preference() -> List[str]:
    """Read PDD_AGENTIC_PROVIDER env or default."""
    env = os.environ.get("PDD_AGENTIC_PROVIDER", "").strip()
    if env:
        items = [p.strip().lower() for p in env.split(",") if p.strip()]
        items = [p for p in items if p in _PROVIDER_TO_CLI]
        if items:
            return items
    return list(_DEFAULT_PROVIDER_PREFERENCE)


# -----------------------------------------------------------------------------
# CLI Discovery
# -----------------------------------------------------------------------------

def _find_cli_binary(name: str, config: Optional[Dict[str, Any]] = None) -> Optional[str]:
    """Locate CLI binary via .pddrc override, PATH, or common paths."""
    config = config if config is not None else _load_agentic_config()
    override = config.get(f"{name}_path")
    if override and Path(override).is_file() and os.access(override, os.X_OK):
        return str(override)

    found = shutil.which(name)
    if found:
        return found

    for base in _COMMON_CLI_PATHS.paths_for(name):
        base_path = Path(base).expanduser()
        if base_path.is_file() and base_path.name == name and os.access(base_path, os.X_OK):
            return str(base_path)

        candidates: List[Path] = []
        if "*" in str(base_path):
            candidates.extend(Path(p) / name for p in glob.glob(str(base_path)))
        elif base_path.name == "node":
            candidates.extend(Path(p) / name for p in glob.glob(str(base_path / "*" / "bin")))
        else:
            candidates.append(base_path / name)

        for candidate in candidates:
            if candidate.is_file() and os.access(candidate, os.X_OK):
                return str(candidate)
    return None


def _get_cli_diagnostic_info(name: str) -> str:
    """Diagnostic string for missing CLI."""
    paths_checked = [shutil.which(name) or "(PATH miss)"] + _COMMON_CLI_PATHS.paths_for(name)
    override_key = f"agentic.{name}_path"
    return (
        f"CLI '{name}' not found. Run `which {name}` to verify installation, "
        f"or set `{override_key}` in .pddrc. Checked: {paths_checked[:8]}"
    )


# -----------------------------------------------------------------------------
# Availability
# -----------------------------------------------------------------------------

def _has_gemini_oauth() -> bool:
    return (Path.home() / ".gemini" / "oauth_creds.json").is_file()


def _has_gemini_oauth_credentials() -> bool:
    return _has_gemini_oauth()


def _has_opencode_auth() -> bool:
    return Path(_OPENCODE_AUTH_PATH).is_file()


def _has_any_provider_key() -> bool:
    keys = (
        "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GEMINI_API_KEY",
        "GOOGLE_API_KEY", "OPENROUTER_API_KEY", "GITHUB_TOKEN", "GROQ_API_KEY",
    )
    return any(os.environ.get(k) for k in keys)


def _is_provider_available(provider: str) -> bool:
    cli_name = _PROVIDER_TO_CLI.get(provider)
    if not cli_name:
        return False
    if not _find_cli_binary(cli_name):
        return False

    if provider == "anthropic":
        return True
    if provider == "google":
        vertex_enabled = os.environ.get("GOOGLE_GENAI_USE_VERTEXAI", "").lower() in {"1", "true", "yes"}
        if (os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
                or vertex_enabled or _has_gemini_oauth_credentials()):
            return True
        return False
    if provider == "openai":
        if os.environ.get("OPENAI_API_KEY") or os.environ.get("PDD_CODEX_AUTH_AVAILABLE"):
            return True
        return False
    if provider == "opencode":
        if _has_any_provider_key() or _has_opencode_auth():
            return True
        return False
    return False


def get_available_agents() -> List[str]:
    """Return list of available providers in preference order."""
    preference = get_agent_provider_preference()
    return [p for p in preference if _is_provider_available(p)]


# -----------------------------------------------------------------------------
# Logging
# -----------------------------------------------------------------------------

_SESSION_LOG_PATH: Optional[Path] = None
_SESSION_LOG_BASE_CWD: Optional[Path] = None
_AGENTIC_SESSION_ID: Optional[str] = None


def _get_session_log_path(cwd: Optional[Union[str, Path]] = None) -> Path:
    global _SESSION_LOG_PATH, _SESSION_LOG_BASE_CWD, _AGENTIC_SESSION_ID
    base_cwd = Path(cwd or ".").resolve()
    if _AGENTIC_SESSION_ID is None:
        _AGENTIC_SESSION_ID = datetime.now().strftime("%Y%m%d_%H%M%S")
        _SESSION_LOG_PATH = None

    if _SESSION_LOG_PATH is None or _SESSION_LOG_BASE_CWD != base_cwd:
        log_dir = base_cwd / AGENTIC_LOG_DIR
        try:
            log_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            log_dir = Path("/tmp")
        _SESSION_LOG_BASE_CWD = base_cwd
        _SESSION_LOG_PATH = log_dir / f"session_{_AGENTIC_SESSION_ID}.jsonl"
    return _SESSION_LOG_PATH


def _log_agentic_interaction(
    record: Optional[Dict[str, Any]] = None,
    force: bool = False,
    verbose: bool = False,
    **kwargs: Any,
) -> None:
    """Log to JSONL. Success logging is verbose-only; failures may be forced."""
    if record is None:
        record = {}
    if kwargs:
        prompt = str(kwargs.get("prompt", ""))
        response = str(kwargs.get("response", ""))
        record.update({
            "label": kwargs.get("label", ""),
            "prompt": prompt,
            "response": response,
            "cost_usd": kwargs.get("cost", kwargs.get("cost_usd", 0.0)),
            "provider": kwargs.get("provider", ""),
            "success": kwargs.get("success", True),
            "duration_seconds": kwargs.get("duration", kwargs.get("duration_seconds", 0.0)),
            "prompt_length": len(prompt),
            "response_length": len(response),
            "cwd": str(kwargs.get("cwd", ".")),
        })

    success = bool(record.get("success", True))
    should_log = force or verbose or not success
    if not should_log:
        return
    try:
        path = _get_session_log_path(record.get("cwd"))
        record.setdefault("timestamp", datetime.now(timezone.utc).isoformat())
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record, default=str) + "\n")
    except Exception:
        pass


def _collect_auth_env_keys() -> List[str]:
    return sorted(
        k for k, v in os.environ.items()
        if v and any(h in k for h in _AUTH_KEY_HINTS)
    )


# -----------------------------------------------------------------------------
# Control Token Detection
# -----------------------------------------------------------------------------

@dataclass
class TokenMatch:
    tier: str
    token: Optional[str] = None
    pattern: Optional[str] = None
    cost: Optional[float] = None

    def __bool__(self) -> bool:
        return True


SEMANTIC_PATTERNS: Dict[str, List[str]] = {
    "ALL_TESTS_PASS": [
        r"\ball\s+(\d+\s+)?tests?\s+pass(ed|ing)?\b",
        r"\ball\s+tests?\s+(are\s+)?passing\b",
        r"\bboth\s+pass(ed|ing)?\b",
        r"\b\d+\s+passed,?\s+0\s+failed\b",
        r"\btest\s+suite\s+pass(ed|es)\b",
    ],
    "NOT_A_BUG": [
        r"\bnot\s+a\s+bug\b",
        r"\bworking\s+as\s+intended\b",
        r"\bexpected\s+behavior\b",
        r"\bno\s+bug\s+found\b",
    ],
    "MAX_CYCLES_REACHED": [
        r"\bmax(imum)?\s+cycles?\s+reached\b",
        r"\bcycle\s+limit\s+(reached|exceeded)\b",
    ],
    "CONTINUE_CYCLE": [
        r"\btests?\s+still\s+failing\b",
        r"\bcontinue\s+cycle\b",
        r"\bneed(s)?\s+(another|more)\s+(iteration|cycle)\b",
    ],
    "TASK_COMPLETE": [
        r"\btask\s+complete(d)?\b",
        r"\bdone\b",
        r"\bfinished\s+successfully\b",
    ],
    "NEEDS_REVIEW": [
        r"\bneeds?\s+review\b",
        r"\bhuman\s+review\s+required\b",
    ],
}


def detect_control_token(output: str, token: str,
                         tail_lines: int = _SEMANTIC_TAIL_LINES) -> Optional[TokenMatch]:
    """3-tier detection: exact, case-insensitive, semantic."""
    if not output or not token:
        return None

    # Tier 1: exact substring
    if token in output:
        return TokenMatch(tier="exact", token=token)

    # Tier 2: case-insensitive
    if token.lower() in output.lower():
        return TokenMatch(tier="case_insensitive", token=token)

    # Tier 3: semantic regex on tail (use splitlines for portability)
    patterns = SEMANTIC_PATTERNS.get(token, [])
    if not patterns:
        return None

    lines = output.splitlines()
    tail = "\n".join(lines[-tail_lines:]) if lines else ""
    for pattern in patterns:
        try:
            if re.search(pattern, tail, re.IGNORECASE):
                return TokenMatch(tier="semantic", token=token, pattern=pattern)
        except re.error:
            continue
    return None


def classify_step_output(output: str, tokens: List[str],
                         quiet: bool = False) -> Optional[str]:
    """Tier-4: cheap LLM classification. Returns matched token or None."""
    if not output or not tokens:
        return None

    for token in tokens:
        match = detect_control_token(output, token)
        if match:
            return match.token

    try:
        # Local relative import assumes this is part of a larger package
        from .llm_invoke import llm_invoke
    except ImportError:
        if not quiet:
            console.print("[yellow]LLM classification unavailable[/yellow]")
        return None

    try:
        from pydantic import BaseModel  # type: ignore

        class ClassificationResult(BaseModel):
            token: Optional[str]
            confidence: float

        prompt = (
            "Classify the following agentic output by selecting the single best matching control token "
            "from this list (or null if none match):\n{tokens}\n\nOutput:\n{output}\n\n"
            "Return JSON: {\"token\": \"<one of the tokens or null>\", \"confidence\": 0.0-1.0}"
        )
        # Truncate output for classification
        snippet = output[-4000:] if len(output) > 4000 else output
        response = llm_invoke(
            prompt=prompt,
            input_json={"tokens": ", ".join(tokens), "output": snippet},
            strength=0.2,
            temperature=0.0,
            output_pydantic=ClassificationResult,
        )
        result = response.get("result")
        if result and getattr(result, "token", None) in tokens and getattr(result, "confidence", 0) >= 0.6:
            return result.token
    except Exception as e:
        if not quiet:
            console.print(f"[yellow]LLM classification failed: {e}[/yellow]")
    return None


# -----------------------------------------------------------------------------
# Error classification
# -----------------------------------------------------------------------------

_PERMANENT_ERROR_PATTERNS: List[str] = [
    r"authentication\s+fail",
    r"authentication[_\s-]*error",
    r"access\s+token\s+could\s+not\s+be\s+refreshed",
    r"please\s+sign\s+in\s+again",
    r"not\s+logged\s+in",
    r"please\s+run\s+/login",
    r"invalid\s+bearer\s+token",
    r"invalid\s+(api[_\s]?key|token|credential)",
    r"unauthorized",
    r"401\b",
    r"403\b",
    r"model\s+not\s+found",
    r"unknown\s+model",
    r"unsupported\s+(feature|parameter|model)",
    r"invalid\s+parameter",
    r"quota\s+(exhausted|exceeded)",
    r"daily\s+quota",
    r"TerminalQuotaError",
    r"provider\s+not\s+configured",
    r"invalid\s+model\s+id",
    r"no\s+provider\s+for\s+model",
    r"permission\s+denied",
    r"auth\.json",
    r"temperature.*(not\s+supported|invalid|unsupported)",
    r"invalid\s+value\s+for\s+temperature",
]


def _is_permanent_error(error_msg: str) -> bool:
    if not error_msg:
        return False
    low = error_msg.lower()
    for pat in _PERMANENT_ERROR_PATTERNS:
        try:
            if re.search(pat, low, re.IGNORECASE):
                return True
        except re.error:
            continue
    return False


def _is_opencode_permanent_error(error_msg: str) -> bool:
    return _is_permanent_error(error_msg)


def _codex_auth_failure_message(error_detail: str) -> Optional[str]:
    """Detect Codex stale-login errors and return user-friendly guidance."""
    if not error_detail:
        return None
    text = error_detail.lower()
    auth_signals = (
        "access token could not be refreshed",
        "please sign in again",
        "chatgpt.com/backend-api/codex",
        "codex/responses",
    )
    has_auth_signal = any(sig in text for sig in auth_signals)
    has_unauth = ("401" in text or "unauthorized" in text or "sign in" in text or "sign-in" in text)
    if has_auth_signal and has_unauth:
        return (
            "Codex CLI authentication failed (stale ChatGPT login). "
            "Please run `codex login` (or `codex login --device-auth`) to refresh your session. "
            "For API-key auth, run `codex login --with-api-key`."
        )
    return None


# -----------------------------------------------------------------------------
# Subprocess
# -----------------------------------------------------------------------------

def _sanitize_env(cwd: Optional[Union[str, Path]] = None) -> Dict[str, str]:
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    if cwd is not None:
        env["GIT_WORK_TREE"] = str(cwd)
    env.pop("PDD_OUTPUT_COST_PATH", None)
    return env


def _subprocess_run(cmd: List[str], cwd: Optional[Union[str, Path]] = None,
                    timeout: Optional[float] = None,
                    env: Optional[Dict[str, str]] = None,
                    stdin_data: Optional[str] = None,
                    input: Optional[str] = None,
                    start_new_session: bool = True,
                    capture_output: bool = True,
                    text: bool = True,
                    **_: Any) -> Tuple[int, str, str]:
    """Run subprocess with process-group kill on timeout."""
    env = env or _sanitize_env(cwd)
    stdin_payload = stdin_data if stdin_data is not None else input
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd) if cwd is not None else None,
            env=env,
            stdin=subprocess.PIPE if stdin_payload is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=start_new_session,
            text=text,
        )
    except FileNotFoundError as e:
        return 127, "", f"File not found: {e}"
    except Exception as e:
        return 1, "", f"Failed to start process: {e}"

    try:
        stdout, stderr = proc.communicate(input=stdin_payload, timeout=timeout)
        return proc.returncode, stdout or "", stderr or ""
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, OSError):
            try:
                proc.kill()
            except Exception:
                pass
        try:
            stdout, stderr = proc.communicate(timeout=5)
        except Exception:
            pass
        raise
    except Exception as e:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except Exception:
            pass
        return 1, "", f"Subprocess error: {e}"


def _normalize_subprocess_result(result: Any) -> Tuple[int, str, str]:
    if isinstance(result, tuple) and len(result) >= 3:
        return int(result[0]), str(result[1] or ""), str(result[2] or "")
    return (
        int(getattr(result, "returncode", 1) or 0),
        str(getattr(result, "stdout", "") or ""),
        str(getattr(result, "stderr", "") or ""),
    )


# -----------------------------------------------------------------------------
# Reasoning effort resolution
# -----------------------------------------------------------------------------

_VALID_REASONING_LEVELS = {"low", "medium", "high"}
_VALID_CODEX_REASONING_LEVELS = {"low", "medium", "high", "xhigh"}


def _resolve_reasoning_effort(reasoning_time: Optional[float],
                              codex: bool = False) -> Optional[str]:
    if codex:
        codex_env = os.environ.get("CODEX_REASONING_EFFORT", "").strip().lower()
        if codex_env in _VALID_CODEX_REASONING_LEVELS:
            return codex_env

    if reasoning_time is not None:
        return time_to_effort_level(reasoning_time)

    env = os.environ.get("PDD_REASONING_EFFORT", "").strip().lower()
    if env in _VALID_REASONING_LEVELS:
        return env
    return None


# -----------------------------------------------------------------------------
# Model resolution
# -----------------------------------------------------------------------------

def _normalize_opencode_model_id(model: str) -> str:
    return model.replace("github_copilot/", "github-copilot/")


# Maps the CSV ``provider`` column to the OpenCode provider id used in the
# ``provider/model`` identifier passed to ``opencode run --model``.
_OPENCODE_PROVIDER_BY_CSV: Dict[str, str] = {
    "openai": "openai",
    "anthropic": "anthropic",
    "google": "google",
    "xai": "xai",
    "deepseek": "deepseek",
    "mistral": "mistral",
    "groq": "groq",
    "moonshot": "moonshot",
    "ollama": "ollama",
    "azure": "azure",
    "meta": "meta",
    "qwen": "qwen",
    "cohere": "cohere",
    "openrouter": "openrouter",
    "github-copilot": "github-copilot",
}


# Env vars that, when set, make a CSV provider routable through OpenCode.
# Keys are the lowercased CSV ``provider`` column. Values include OpenCode
# providers that don't have a CSV row of their own (e.g. ``github-copilot``)
# but are nonetheless documented as valid OpenCode auth paths.
_OPENCODE_PROVIDER_AUTH_ENV: Dict[str, Tuple[str, ...]] = {
    "openai": ("OPENAI_API_KEY",),
    "anthropic": ("ANTHROPIC_API_KEY",),
    "google": ("GEMINI_API_KEY", "GOOGLE_API_KEY"),
    "xai": ("XAI_API_KEY",),
    "deepseek": ("DEEPSEEK_API_KEY",),
    "mistral": ("MISTRAL_API_KEY",),
    "groq": ("GROQ_API_KEY",),
    "moonshot": ("MOONSHOT_API_KEY",),
    "cohere": ("COHERE_API_KEY",),
    "ollama": ("OLLAMA_API_KEY",),
    "azure": ("AZURE_OPENAI_API_KEY",),
    "openrouter": ("OPENROUTER_API_KEY",),
    "github-copilot": ("GITHUB_TOKEN", "GH_TOKEN"),
}


def _opencode_authed_providers(source: Dict[str, str]) -> Set[str]:
    """Return the set of OpenCode provider ids the user has auth for.

    Combines provider env vars (``ANTHROPIC_API_KEY`` etc.) with the providers
    stored in ``~/.local/share/opencode/auth.json`` (whose top-level keys are
    OpenCode provider ids such as ``anthropic`` or ``github-copilot``).
    """
    available: Set[str] = set()
    for csv_provider, env_keys in _OPENCODE_PROVIDER_AUTH_ENV.items():
        if any(source.get(k) for k in env_keys):
            opencode_id = _OPENCODE_PROVIDER_BY_CSV.get(csv_provider)
            if opencode_id:
                available.add(opencode_id)
    try:
        with open(_OPENCODE_AUTH_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            for key in data.keys():
                if isinstance(key, str) and key.strip():
                    available.add(key.strip().lower())
    except (OSError, json.JSONDecodeError):
        pass
    return available


def _resolve_opencode_model(env: Optional[Dict[str, str]] = None) -> Optional[str]:
    """Resolve OpenCode model from env or CSV defaults.

    OpenCode requires a ``provider/model`` identifier. When OPENCODE_MODEL is
    not set we walk the CSV catalog and combine the CSV ``provider`` column
    with the ``model`` column, filtered by the providers the user has auth for
    (provider env vars + OpenCode's ``auth.json``). Rows whose model already
    contains ``/`` are skipped because those identifiers route through a
    sub-provider (e.g. ``moonshotai/kimi-k2-instruct`` served on Groq) and
    cannot be passed to OpenCode verbatim.
    """
    source = env if env is not None else os.environ
    explicit = source.get("OPENCODE_MODEL", "").strip()
    if explicit:
        return _normalize_opencode_model_id(explicit)

    if env is not None:
        return None

    authed = _opencode_authed_providers(source)

    # Try to derive from CSV metadata if present, mapping CSV provider to
    # OpenCode provider id and filtering to providers the user can route to.
    try:
        rows = _load_model_data()
        if rows:
            fallback: Optional[str] = None
            for row in rows:
                provider = (row.get("provider") or "").strip().lower()
                model = (row.get("model") or row.get("model_id") or "").strip()
                if not provider or not model or "/" in model:
                    continue
                opencode_provider = _OPENCODE_PROVIDER_BY_CSV.get(provider)
                if not opencode_provider:
                    continue
                candidate = _normalize_opencode_model_id(f"{opencode_provider}/{model}")
                if not authed:
                    # No auth signal at all: behave like the previous fallback
                    # and just take the first OpenCode-mappable row.
                    return candidate
                if opencode_provider in authed:
                    return candidate
                if fallback is None:
                    fallback = candidate
            if fallback is not None and not authed:
                return fallback
    except Exception:
        pass

    # Last-resort defaults keyed off whichever provider the user can reach.
    # ``openrouter`` and ``github-copilot`` don't have CSV rows in the bundled
    # catalog, so a default is the only way to produce a routable model id
    # for users whose only auth is ``OPENROUTER_API_KEY`` or ``GITHUB_TOKEN``.
    default_by_provider: Dict[str, str] = {
        "anthropic": "anthropic/claude-sonnet-4-5",
        "openai": "openai/gpt-5.1",
        "google": "google/gemini-2.5-pro",
        "xai": "xai/grok-4-0709",
        "deepseek": "deepseek/deepseek-chat",
        "groq": "groq/llama-3.3-70b-versatile",
        "openrouter": "openrouter/anthropic/claude-sonnet-4.5",
        "github-copilot": "github-copilot/claude-sonnet-4.5",
    }
    for provider in (
        "anthropic", "openai", "google", "xai", "deepseek", "groq",
        "openrouter", "github-copilot",
    ):
        if provider in authed and provider in default_by_provider:
            return default_by_provider[provider]
    return "anthropic/claude-sonnet-4-5"


# -----------------------------------------------------------------------------
# Provider JSON parsing
# -----------------------------------------------------------------------------

def _extract_json_from_output(raw: str) -> Dict[str, Any]:
    """Extract the first JSON object from noisy CLI output."""
    if not raw:
        raise json.JSONDecodeError("No JSON object found", raw, 0)

    try:
        data = json.loads(raw)
        if isinstance(data, dict):
            return data
    except json.JSONDecodeError:
        pass

    decoder = json.JSONDecoder()
    for index, char in enumerate(raw):
        if char != "{":
            continue
        try:
            data, _ = decoder.raw_decode(raw[index:])
        except json.JSONDecodeError:
            continue
        if isinstance(data, dict):
            return data
    raise json.JSONDecodeError("No JSON object found", raw, 0)


def _parse_anthropic_output(stdout: str) -> Tuple[bool, str, float]:
    text = ""
    success = True
    try:
        data = _extract_json_from_output(stdout)
    except json.JSONDecodeError:
        return True, stdout, 0.0

    if isinstance(data, dict):
        if data.get("is_error"):
            text = str(data.get("result") or data.get("response") or stdout)
            return False, text, _calculate_anthropic_cost(data)

        text = str(data.get("result") or data.get("response") or "")
        cost = _calculate_anthropic_cost(data)
    return success, text, cost


def _parse_google_output(stdout: str) -> Tuple[bool, str, float]:
    try:
        data = _extract_json_from_output(stdout)
    except json.JSONDecodeError:
        return True, stdout, 0.0

    text = ""
    cost = 0.0
    if isinstance(data, dict):
        text = str(data.get("result") or data.get("response") or data.get("output") or "")
        stats = data.get("stats") or {}
        cost = _calculate_gemini_cost(stats)
    return True, text, cost


def _extract_openai_text(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        parts: List[str] = []
        for part in value:
            text = _extract_openai_text(part)
            if text:
                parts.append(text)
        return "".join(parts)
    if isinstance(value, dict):
        for key in ("text", "output_text", "content", "result", "output"):
            if key in value:
                text = _extract_openai_text(value.get(key))
                if text:
                    return text
        message = value.get("message")
        if isinstance(message, dict):
            return _extract_openai_text(message)
    return ""


def _usage_counts(usage: Dict[str, Any]) -> Tuple[int, int, int]:
    return (
        _first_int(usage, "input_tokens", "prompt_tokens", "input"),
        _first_int(usage, "output_tokens", "completion_tokens", "output"),
        _first_int(usage, "cached_input_tokens", "cached_tokens", "cached"),
    )


def _parse_openai_output(stdout: str) -> Tuple[bool, str, float]:
    text_parts: List[str] = []
    cost = 0.0
    last_text = ""
    input_tokens = 0
    output_tokens = 0
    cached_tokens = 0
    saw_ndjson = False
    session_usage: Optional[Tuple[int, int, int]] = None

    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            evt = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(evt, dict):
            continue

        evt_type = evt.get("type") or ""
        if not evt_type:
            continue
        saw_ndjson = True
        item = evt.get("item") or {}

        if evt_type == "item.completed" and isinstance(item, dict):
            if item.get("type") == "agent_message":
                t = _extract_openai_text(item)
                if t:
                    last_text = str(t)
                    text_parts.append(str(t))

        if evt_type == "message" and evt.get("role") == "assistant":
            t = _extract_openai_text(evt)
            if t:
                last_text = str(t)
                text_parts.append(str(t))

        if evt_type == "result":
            t = _extract_openai_text(evt)
            if t:
                last_text = str(t)
                text_parts.append(str(t))
            usage = evt.get("usage") or {}
            if isinstance(usage, dict):
                in_tok, out_tok, cache_tok = _usage_counts(usage)
                input_tokens += in_tok
                output_tokens += out_tok
                cached_tokens += cache_tok

        if evt_type in ("session.end", "turn.completed"):
            usage = evt.get("usage") or {}
            if isinstance(usage, dict):
                counts = _usage_counts(usage)
                if evt_type == "session.end":
                    session_usage = counts
                else:
                    in_tok, out_tok, cache_tok = counts
                    input_tokens += in_tok
                    output_tokens += out_tok
                    cached_tokens += cache_tok
            c = evt.get("cost") or evt.get("total_cost_usd")
            if c is not None:
                try:
                    cost += float(c)
                except (TypeError, ValueError):
                    pass

    if not saw_ndjson:
        try:
            data = _extract_json_from_output(stdout)
            if isinstance(data, dict):
                item = data.get("item") or {}
                if isinstance(item, dict) and item.get("type") == "agent_message":
                    last_text = _extract_openai_text(item)
                else:
                    last_text = _extract_openai_text(data)
                usage = data.get("usage") or {}
                if isinstance(usage, dict):
                    input_tokens, output_tokens, cached_tokens = _usage_counts(usage)
        except json.JSONDecodeError:
            last_text = stdout

    text = last_text or "\n".join(text_parts)

    if session_usage is not None:
        input_tokens, output_tokens, cached_tokens = session_usage

    if cost == 0 and (input_tokens or output_tokens):
        cost = _estimate_cost(input_tokens, output_tokens, CODEX_PRICING,
                              cached_tokens=cached_tokens)

    return True, text, cost


def _parse_opencode_output(stdout: str) -> Tuple[bool, str, float]:
    """Parse OpenCode JSONL events.

    Backwards-compatible 3-tuple wrapper around :func:`_parse_opencode_jsonl`.
    Used by :func:`_parse_provider_json`; ``_run_with_provider`` calls the
    underlying parser directly so it can apply CSV-based pricing for the
    resolved OpenCode model.
    """
    ok, text, cost, error_msg, info = _parse_opencode_jsonl(stdout)
    if not ok:
        return False, error_msg or text, cost
    # When no cost was reported and we have token counts, fall back to a
    # generic per-million estimate so this convenience wrapper still produces
    # a non-zero cost. The richer CSV-based fallback runs in
    # ``_run_with_provider``.
    if cost == 0 and not info.get("cost_reported"):
        in_tok = int(info.get("input_tokens") or 0)
        out_tok = int(info.get("output_tokens") or 0)
        cache_tok = int(info.get("cached_tokens") or 0)
        if in_tok or out_tok:
            cost = _estimate_cost(in_tok, out_tok, CODEX_PRICING,
                                  cached_tokens=cache_tok)
    return True, text, cost


def _parse_opencode_jsonl(
    stdout: str,
) -> Tuple[bool, str, float, Optional[str], Dict[str, Any]]:
    """Parse an ``opencode run --format json`` JSONL stream.

    Returns ``(ok, text, cost, error_msg, info)`` where ``info`` carries the
    extra signals ``_run_with_provider`` needs to apply a CSV-based cost
    fallback for the resolved OpenCode model:

    * ``cost_reported`` — ``True`` if any event surfaced a numeric ``cost``.
    * ``input_tokens`` / ``output_tokens`` / ``cached_tokens`` — accumulated
      usage counts; zero when OpenCode emitted only text events.
    """
    text_parts: List[str] = []
    cost = 0.0
    error_msg: Optional[str] = None
    saw_event = False
    saw_text_or_step = False
    saw_cost = False
    input_tokens = 0
    output_tokens = 0
    cached_tokens = 0

    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            evt = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(evt, dict):
            continue
        saw_event = True
        evt_type = evt.get("type") or ""

        if evt_type == "text":
            # ``opencode run --format json`` emits text events with the actual
            # content nested under ``part.text``. Older/stub event shapes used
            # a top-level ``text``/``content`` field, which we still accept for
            # backwards compatibility.
            part = evt.get("part") or {}
            t = ""
            if isinstance(part, dict):
                t = part.get("text") or part.get("content") or ""
            if not t:
                t = evt.get("text") or evt.get("content") or ""
            if t:
                text_parts.append(str(t))
                saw_text_or_step = True
        elif evt_type == "step_finish":
            saw_text_or_step = True
            part = evt.get("part") or {}
            if isinstance(part, dict):
                c = part.get("cost")
                if c is not None:
                    saw_cost = True
                    try:
                        cost += float(c)
                    except (TypeError, ValueError):
                        pass
                usage = part.get("usage") or part.get("tokens") or {}
                if isinstance(usage, dict):
                    in_tok, out_tok, cache_tok = _usage_counts(usage)
                    input_tokens += in_tok
                    output_tokens += out_tok
                    cached_tokens += cache_tok
            c = evt.get("cost")
            if c is not None:
                saw_cost = True
                try:
                    cost += float(c)
                except (TypeError, ValueError):
                    pass
            usage = evt.get("usage") or evt.get("tokens") or {}
            if isinstance(usage, dict):
                in_tok, out_tok, cache_tok = _usage_counts(usage)
                input_tokens += in_tok
                output_tokens += out_tok
                cached_tokens += cache_tok
        elif evt_type == "error":
            error_msg = str(evt.get("message") or evt.get("error") or "OpenCode error")

    info: Dict[str, Any] = {
        "cost_reported": saw_cost,
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "cached_tokens": cached_tokens,
    }

    if error_msg:
        return False, "", cost, error_msg, info

    if not saw_event or not saw_text_or_step:
        return False, "", 0.0, None, info

    text = "".join(text_parts)
    return True, text, cost, None, info


def _opencode_pricing_for_model(model: Optional[str]) -> Optional[Pricing]:
    """Resolve a :class:`Pricing` for an OpenCode ``provider/model`` id.

    Reads the active model catalog (user/project/package, in that order) and
    returns ``None`` when the model isn't priced in any catalog. ``input``/
    ``output`` columns are interpreted as USD per million tokens, matching
    the rest of PDD.
    """
    if not model or "/" not in model:
        return None
    try:
        rows = _load_model_data()
    except Exception:
        rows = None
    if not rows:
        return None

    opencode_provider, _, model_name = model.partition("/")
    opencode_provider = opencode_provider.strip().lower()
    model_name = model_name.strip()
    if not opencode_provider or not model_name:
        return None

    for row in rows:
        csv_provider = (row.get("provider") or "").strip().lower()
        csv_model = (row.get("model") or "").strip()
        if not csv_provider or not csv_model:
            continue
        mapped = _OPENCODE_PROVIDER_BY_CSV.get(csv_provider)
        if mapped != opencode_provider:
            continue
        if csv_model != model_name:
            continue
        try:
            input_per_million = float(row.get("input") or 0.0)
            output_per_million = float(row.get("output") or 0.0)
        except (TypeError, ValueError):
            return None
        if input_per_million <= 0 and output_per_million <= 0:
            return None
        return Pricing(input_per_million, output_per_million)
    return None


def _estimate_opencode_cost(
    info: Dict[str, Any],
    *,
    model: Optional[str],
    prompt_text: str,
    response_text: str,
) -> float:
    """Estimate an OpenCode invocation cost when the CLI didn't report one.

    Prefers CSV pricing for the resolved OpenCode model. Falls back to
    ``CODEX_PRICING`` only when the catalog has no entry. When OpenCode emits
    only ``text`` events (no ``usage`` block), token counts are estimated
    from prompt and response text length so subscription-style auth paths
    still produce a non-zero cost approximation.
    """
    pricing = _opencode_pricing_for_model(model) or CODEX_PRICING

    in_tok = int(info.get("input_tokens") or 0)
    out_tok = int(info.get("output_tokens") or 0)
    cache_tok = int(info.get("cached_tokens") or 0)
    if not (in_tok or out_tok):
        in_tok = _estimate_tokens_from_text(prompt_text or "")
        out_tok = _estimate_tokens_from_text(response_text or "")
        cache_tok = 0
    if not (in_tok or out_tok):
        return 0.0
    return _estimate_cost(in_tok, out_tok, pricing, cached_tokens=cache_tok)


def _parse_provider_json(provider: str, data_or_stdout: Union[str, Dict[str, Any]]) -> Tuple[bool, str, float]:
    """Parse one provider JSON object/string into success, text, cost."""
    if provider == "anthropic":
        if isinstance(data_or_stdout, dict):
            return _parse_anthropic_output(json.dumps(data_or_stdout))
        return _parse_anthropic_output(data_or_stdout)
    if provider == "google":
        if isinstance(data_or_stdout, dict):
            return _parse_google_output(json.dumps(data_or_stdout))
        return _parse_google_output(data_or_stdout)
    if provider == "openai":
        if isinstance(data_or_stdout, dict):
            return _parse_openai_output(json.dumps(data_or_stdout))
        return _parse_openai_output(data_or_stdout)
    if provider == "opencode":
        if isinstance(data_or_stdout, dict):
            return _parse_opencode_output(json.dumps(data_or_stdout))
        return _parse_opencode_output(data_or_stdout)
    if isinstance(data_or_stdout, str):
        return True, data_or_stdout, 0.0
    return True, str(data_or_stdout), 0.0


# -----------------------------------------------------------------------------
# False positive detection
# -----------------------------------------------------------------------------

def _is_false_positive(output: str, cost: float) -> bool:
    if not output or not output.strip():
        return True
    stripped = output.strip()
    length = len(stripped)
    if cost == 0 and length < MIN_VALID_OUTPUT_LENGTH:
        return True
    if cost > 0 and stripped.startswith("Error:"):
        newlines = stripped.count("\n")
        if newlines < MAX_ERROR_RESPONSE_NEWLINES and length < 4000:
            return True
    return False


# -----------------------------------------------------------------------------
# Provider invocation builders
# -----------------------------------------------------------------------------

def _build_agent_instruction(prompt_file: Union[str, Path]) -> str:
    return (
        f"Read the file {prompt_file} for instructions. "
        "You have full file access to explore and modify files as needed."
    )


def _build_anthropic_cmd(cli_path: str, instruction: str, use_playwright: bool) -> Tuple[List[str], Optional[str]]:
    cmd = [cli_path, "-p", "-"]
    if use_playwright:
        cmd.extend(["--allowedTools", "Bash", "Read", "Write", "--max-turns", "30"])
    else:
        cmd.append("--dangerously-skip-permissions")
    cmd.extend(["--output-format", "json"])
    model = os.environ.get("CLAUDE_MODEL")
    if model:
        cmd.extend(["--model", model])
    return cmd, instruction


def _build_google_cmd(cli_path: str, instruction: str) -> List[str]:
    cmd = [cli_path, instruction, "--yolo", "--output-format", "json"]
    model = os.environ.get("GEMINI_MODEL")
    if model:
        cmd.extend(["--model", model])
    return cmd


def _build_openai_cmd(cli_path: str, instruction_arg: str,
                      reasoning_effort: Optional[str]) -> List[str]:
    sandbox = os.environ.get("CODEX_SANDBOX", "danger-full-access")
    cmd = [cli_path]
    if reasoning_effort:
        cmd.extend(["-c", f"model_reasoning_effort={reasoning_effort}"])
    cmd.extend(["exec", "--sandbox", sandbox, "--json", instruction_arg])
    model = os.environ.get("CODEX_MODEL")
    if model:
        cmd.extend(["--model", model])
    return cmd


def _build_opencode_cmd(cli_path: str, instruction: str, cwd: str) -> List[str]:
    model = _resolve_opencode_model()
    cmd = [cli_path, "run", "--dir", cwd, "--format", "json",
           "--dangerously-skip-permissions"]
    if model:
        cmd.extend(["--model", model])
    agent = os.environ.get("OPENCODE_AGENT", "").strip()
    if agent:
        cmd.extend(["--agent", agent])
    variant = os.environ.get("OPENCODE_VARIANT", "").strip()
    if variant:
        cmd.extend(["--variant", variant])
    cmd.append(instruction)
    return cmd


def _coerce_prompt_file(
    instruction: Optional[Union[str, Path]],
    cwd: Union[str, Path],
    prompt_path: Optional[Union[str, Path]],
) -> Tuple[Path, bool]:
    cwd_path = Path(cwd)
    if prompt_path is not None:
        return Path(prompt_path), False
    if isinstance(instruction, Path):
        return instruction, False
    if isinstance(instruction, str):
        maybe_path = Path(instruction)
        if maybe_path.exists():
            return maybe_path, False

    prompt_file = cwd_path / f".agentic_prompt_{uuid.uuid4().hex}.txt"
    prompt_text = str(instruction or "")
    prompt_file.write_text(prompt_text, encoding="utf-8")
    return prompt_file, True


def _run_with_provider(
    provider: str,
    instruction: Optional[Union[str, Path]] = None,
    cwd: Union[str, Path] = ".",
    *,
    prompt_path: Optional[Union[str, Path]] = None,
    verbose: bool = False,
    quiet: bool = False,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
    use_playwright: bool = False,
    reasoning_time: Optional[float] = None,
    cli_path: Optional[str] = None,
) -> Tuple[bool, str, float]:
    """Run a single attempt with the given provider."""
    cli_name = _PROVIDER_TO_CLI.get(provider)
    if not cli_name:
        return False, f"Unknown provider: {provider}", 0.0

    resolved_cli_path = cli_path or _find_cli_binary(cli_name)
    if not resolved_cli_path:
        return False, _get_cli_diagnostic_info(cli_name), 0.0

    cwd_path = Path(cwd)
    env = _sanitize_env(cwd_path)

    stdin_data: Optional[str] = None
    cmd: List[str] = []
    owned_prompt = False

    try:
        prompt_file, owned_prompt = _coerce_prompt_file(instruction, cwd_path, prompt_path)
        agent_instruction = _build_agent_instruction(prompt_file)

        if provider == "anthropic":
            cmd, stdin_data = _build_anthropic_cmd(resolved_cli_path, agent_instruction, use_playwright)
        elif provider == "google":
            cmd = _build_google_cmd(resolved_cli_path, agent_instruction)
        elif provider == "openai":
            effort = _resolve_reasoning_effort(reasoning_time, codex=True)
            cmd = _build_openai_cmd(resolved_cli_path, str(prompt_file), effort)
        elif provider == "opencode":
            cmd = _build_opencode_cmd(resolved_cli_path, agent_instruction, str(cwd_path))
        else:
            return False, f"Unsupported provider: {provider}", 0.0

        if provider in ("anthropic", "google") and not quiet:
            effort_notice = _resolve_reasoning_effort(reasoning_time)
            if effort_notice is not None:
                console.print(
                    f"[dim]PDD_REASONING_EFFORT={effort_notice} requested, "
                    f"but {provider} CLI has no reasoning-effort flag; ignoring.[/dim]"
                )

        if verbose and not quiet:
            console.print(f"[dim]Running {provider}: {resolved_cli_path}[/dim]")

        try:
            result = _subprocess_run(
                cmd,
                cwd=cwd_path,
                timeout=timeout,
                env=env,
                input=stdin_data,
                stdin_data=stdin_data,
                start_new_session=True,
            )
            rc, stdout, stderr = _normalize_subprocess_result(result)
        except subprocess.TimeoutExpired as exc:
            return False, f"Timeout after {exc.timeout}s", 0.0

        if rc != 0:
            combined = (stderr or "") + "\n" + (stdout or "")
            if provider == "openai":
                auth_msg = _codex_auth_failure_message(combined)
                if auth_msg:
                    return False, auth_msg, 0.0
            err_snippet = (stderr or stdout or f"Exit code {rc}")[-MAX_ERROR_SNIPPET_LENGTH:]
            return False, f"Exit code {rc}: {err_snippet}", 0.0

        if provider == "opencode":
            ok, parsed_text, parsed_cost, error_msg, opencode_info = _parse_opencode_jsonl(stdout)
            success = ok
            text = parsed_text if ok else (error_msg or parsed_text)
            cost = parsed_cost
            # When OpenCode succeeded but didn't surface a cost (e.g. text-only
            # events or subscription auth), price the call against the
            # resolved OpenCode model's CSV pricing. Fall back to a
            # prompt/output text estimate when no usage tokens are present so
            # we still record a non-zero cost.
            if ok and not opencode_info.get("cost_reported") and cost == 0:
                resolved_model = _resolve_opencode_model()
                try:
                    prompt_text = (
                        prompt_file.read_text(encoding="utf-8")
                        if prompt_file.exists() else ""
                    )
                except OSError:
                    prompt_text = ""
                cost = _estimate_opencode_cost(
                    opencode_info,
                    model=resolved_model,
                    prompt_text=prompt_text,
                    response_text=parsed_text,
                )
        else:
            success, text, cost = _parse_provider_json(provider, stdout)

        if provider == "opencode" and not success and _is_opencode_permanent_error(text):
            text = (
                f"OpenCode configuration error: {text}. "
                "Check OPENCODE_MODEL and run `opencode auth login` or `opencode models`."
            )

        # Detect blank output success artifacts
        if not (text or "").strip():
            auth_keys = _collect_auth_env_keys()
            prompt_size = prompt_file.stat().st_size if prompt_file.exists() else 0
            msg = (
                f"[yellow]Provider {provider} returned empty output (rc=0). "
                f"stderr_tail={stderr[-500:]!r} prompt_size={prompt_size} "
                f"auth_keys={auth_keys} cwd={cwd_path}[/yellow]"
            )
            console.print(msg)
            _log_agentic_interaction({
                "provider": provider,
                "event": "empty_success",
                "success": False,
                "stderr_tail": (stderr or "")[-500:],
                "prompt_size": prompt_size,
                "auth_keys": auth_keys,
                "cwd": str(cwd_path),
            }, force=True)

        if not success:
            return False, text or "Provider reported failure", cost

        if _is_false_positive(text, cost):
            if not quiet:
                console.print(f"[yellow]Provider '{provider}' returned false positive[/yellow]")
            return False, text or "False positive (empty/error-like response)", cost

        return True, text, cost
    finally:
        if owned_prompt:
            try:
                prompt_file.unlink()
            except Exception:
                pass


# -----------------------------------------------------------------------------
# Deadline Management
# -----------------------------------------------------------------------------

def get_job_deadline() -> Optional[float]:
    val = os.environ.get("PDD_JOB_DEADLINE", "").strip()
    if not val:
        return None
    try:
        return float(val)
    except ValueError:
        return None


def _remaining_time(deadline: Optional[float]) -> Optional[float]:
    if deadline is None:
        return None
    return deadline - time.time()


# -----------------------------------------------------------------------------
# Template substitution
# -----------------------------------------------------------------------------

def substitute_template_variables(template: str, variables: Dict[str, Any]) -> str:
    """Safe substitution that doesn't fail on unmatched braces."""
    if not template:
        return template
    result = template
    for key, val in variables.items():
        result = result.replace("{" + key + "}", str(val))
    return result


# -----------------------------------------------------------------------------
# Progress tracking (Ctrl+C UX)
# -----------------------------------------------------------------------------

_PROGRESS_STATE: Optional[Dict[str, Any]] = None


def set_agentic_progress(workflow: str, current_step: int, total_steps: int,
                         step_name: str, completed_steps: List[str]) -> None:
    global _PROGRESS_STATE
    _PROGRESS_STATE = {
        "workflow": workflow,
        "current_step": current_step,
        "total_steps": total_steps,
        "step_name": step_name,
        "completed_steps": list(completed_steps),
        "timestamp": time.time(),
    }


def clear_agentic_progress() -> None:
    global _PROGRESS_STATE
    _PROGRESS_STATE = None


def get_and_clear_agentic_interrupt_context() -> Optional[Dict[str, Any]]:
    global _PROGRESS_STATE
    state = _PROGRESS_STATE
    _PROGRESS_STATE = None
    return state


# -----------------------------------------------------------------------------
# Main Entry: run_agentic_task
# -----------------------------------------------------------------------------

def run_agentic_task(
    instruction: str,
    cwd: Union[str, Path],
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
    """Run an agentic task across configured providers with retries."""
    if not instruction or not instruction.strip():
        return False, "Empty instruction", 0.0, ""

    cwd_path = Path(cwd)
    prompt_body = instruction
    user_feedback = os.environ.get("PDD_USER_FEEDBACK", "").strip()
    if user_feedback:
        prompt_body = f"{instruction.rstrip()}\n\nUser Feedback:\n{user_feedback}\n"

    effective_timeout = timeout or DEFAULT_TIMEOUT_SECONDS
    job_deadline = deadline if deadline is not None else get_job_deadline()
    using_job_deadline = job_deadline is not None
    step_deadline: Optional[float]
    if using_job_deadline:
        step_deadline = job_deadline
    else:
        step_deadline = time.time() + (2.0 * effective_timeout)

    candidates = get_available_agents()
    if not candidates:
        msg = "No agentic providers available. Install at least one: claude, gemini, codex, or opencode."
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, ""

    if not quiet and verbose:
        console.print(f"[dim]Available providers: {candidates}[/dim]")

    last_error = ""
    last_provider = ""
    prompt_file = cwd_path / f".agentic_prompt_{uuid.uuid4().hex}.txt"

    try:
        prompt_file.write_text(prompt_body, encoding="utf-8")
        for provider in candidates:
            last_provider = provider
            is_single_provider = (len(candidates) == 1)

            for attempt in range(1, max_retries + 1):
                # Check deadline and adjust timeout budget
                remaining = _remaining_time(step_deadline)
                if remaining is not None:
                    budget = remaining - JOB_TIMEOUT_MARGIN_SECONDS if using_job_deadline else remaining
                    if budget < MIN_ATTEMPT_TIMEOUT_SECONDS:
                        if not quiet:
                            console.print(f"[yellow]Skipping {provider}: insufficient time ({budget:.0f}s)[/yellow]")
                        last_error = "Deadline exceeded"
                        break
                    attempt_timeout = min(effective_timeout, budget)
                else:
                    attempt_timeout = effective_timeout

                if not quiet:
                    tag = f"[{label}] " if label else ""
                    console.print(f"[cyan]{tag}Attempt {attempt}/{max_retries} with {provider}[/cyan]")

                started = time.time()
                try:
                    success, output, cost = _run_with_provider(
                        provider,
                        prompt_path=prompt_file,
                        cwd=cwd_path,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=attempt_timeout,
                        use_playwright=use_playwright,
                        reasoning_time=reasoning_time,
                    )
                except KeyboardInterrupt:
                    raise
                except Exception as e:
                    success, output, cost = False, f"Exception: {e}", 0.0

                duration = time.time() - started
                if success:
                    if _is_false_positive(output, cost):
                        if not quiet:
                            console.print(f"[yellow]Provider '{provider}' returned false positive[/yellow]")
                        success = False
                        output = output or "False positive (empty/error-like response)"
                    else:
                        if verbose:
                            _log_agentic_interaction(
                                label=label,
                                prompt=prompt_body,
                                response=output,
                                cost=cost,
                                provider=provider,
                                success=True,
                                duration=duration,
                                cwd=cwd_path,
                            )
                        _detect_single_letter_files(str(cwd_path), quiet=quiet)
                        return True, output, cost, provider

                last_error = output or "Unknown error"
                _log_agentic_interaction(
                    label=label,
                    prompt=prompt_body,
                    response=last_error,
                    cost=cost,
                    provider=provider,
                    success=False,
                    duration=duration,
                    cwd=cwd_path,
                    force=True,
                )

                if not quiet:
                    console.print(f"[yellow]Attempt failed: {last_error[:200]}[/yellow]")

                # Permanent error: skip retries, move to next provider
                if _is_permanent_error(last_error):
                    if not quiet:
                        console.print(f"[red]Permanent error from {provider}; skipping retries.[/red]")
                    break

                # Multi-provider logic: break on fail to try next candidate unless it's the only one
                if not is_single_provider:
                    break

                # Single-provider logic: exponential backoff retries
                if attempt < max_retries:
                    backoff = retry_delay * (2 ** (attempt - 1)) + random.uniform(0, retry_delay)
                    backoff = min(backoff, MAX_RETRY_DELAY)
                    if not quiet:
                        console.print(f"[dim]Backing off {backoff:.1f}s...[/dim]")
                    time.sleep(backoff)
    finally:
        try:
            prompt_file.unlink()
        except Exception:
            pass

    msg = f"All agent providers failed. Last error from {last_provider}: {last_error[:500]}"
    return False, msg, 0.0, last_provider


def _detect_single_letter_files(cwd: str, quiet: bool = False) -> None:
    """Warn if single-letter files appeared (likely shell-redirect artifacts)."""
    try:
        for name in ("C", "E", "T"):
            p = Path(cwd) / name
            if p.is_file():
                if not quiet:
                    console.print(
                        f"[red]SUSPICIOUS FILES DETECTED: stray file '{name}' in {cwd} "
                        "(likely artifact)[/red]"
                    )
    except Exception:
        pass


# -----------------------------------------------------------------------------
# GitHub State Persistence
# -----------------------------------------------------------------------------

_STATE_MARKER_PREFIX = "<!-- PDD_WORKFLOW_STATE:"
_STATE_MARKER_SUFFIX = " -->"
GITHUB_STATE_MARKER_START: str = _STATE_MARKER_PREFIX
GITHUB_STATE_MARKER_END: str = _STATE_MARKER_SUFFIX


def _gh_available() -> bool:
    return shutil.which("gh") is not None


def _gh_run(args: List[str], cwd: Optional[str] = None,
            timeout: float = 60.0, input_data: Optional[str] = None
            ) -> Tuple[int, str, str]:
    if not _gh_available():
        return 127, "", "gh CLI not installed"
    try:
        result = subprocess.run(
            ["gh"] + args,
            cwd=cwd,
            input=input_data,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return -9, "", f"Timeout after {exc.timeout}s"
    except OSError as exc:
        return 1, "", str(exc)
    return result.returncode, result.stdout or "", result.stderr or ""


def _find_state_comment(repo_owner: str, repo_name: str, issue_number: int,
                        workflow_id: str, cwd: Optional[str] = None
                        ) -> Tuple[Optional[int], Optional[Dict[str, Any]]]:
    """Find the existing state marker comment. Returns (comment_id, state_dict)."""
    rc, stdout, stderr = _gh_run(
        ["api", "--paginate",
         f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments"],
        cwd=cwd, timeout=120.0,
    )
    if rc != 0:
        return None, None

    try:
        comments: List[Dict[str, Any]] = []
        decoder = json.JSONDecoder()
        idx = 0
        s = stdout.strip()
        while idx < len(s):
            while idx < len(s) and s[idx] in " \n\r\t":
                idx += 1
            if idx >= len(s):
                break
            obj, end = decoder.raw_decode(s, idx)
            if isinstance(obj, list):
                comments.extend(obj)
            idx = end
    except Exception:
        try:
            comments = json.loads(stdout)
        except json.JSONDecodeError:
            return None, None

    for comment in comments:
        body = comment.get("body", "") or ""
        markers = [
            f"{_STATE_MARKER_PREFIX}{workflow_id}:issue-{issue_number}:",
            f"{_STATE_MARKER_PREFIX}{workflow_id}:",
        ]
        marker = next((m for m in markers if m in body), "")
        if marker:
            start = body.find(marker) + len(marker)
            end = body.find(_STATE_MARKER_SUFFIX, start)
            if end > start:
                payload = body[start:end].strip()
                try:
                    state = json.loads(payload)
                    return comment.get("id"), state
                except json.JSONDecodeError:
                    return comment.get("id"), None
    return None, None


def _build_state_marker(workflow_type: str, issue_number: int) -> str:
    return f"{_STATE_MARKER_PREFIX}{workflow_type}:issue-{issue_number}"


def _serialize_state_comment(workflow_type: str, issue_number: int, state: Dict[str, Any]) -> str:
    payload = json.dumps(state, default=str)
    return f"{_build_state_marker(workflow_type, issue_number)}:{payload}{_STATE_MARKER_SUFFIX}"


def _parse_state_from_comment(body: str, workflow_type: str, issue_number: int) -> Optional[Dict[str, Any]]:
    marker = f"{_build_state_marker(workflow_type, issue_number)}:"
    if marker not in body:
        return None
    start = body.find(marker) + len(marker)
    end = body.find(_STATE_MARKER_SUFFIX, start)
    if end <= start:
        return None
    try:
        parsed = json.loads(body[start:end].strip())
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, dict) else None


def _should_use_github_state(use_github_state: bool = True) -> bool:
    if not use_github_state:
        return False
    return os.environ.get("PDD_NO_GITHUB_STATE", "").lower() not in {"1", "true", "yes"}


def _local_state_path(
    cwd: Optional[Union[str, Path]],
    workflow_id: str,
    issue_number: Optional[int] = None,
    state_dir: Optional[Union[str, Path]] = None,
) -> Path:
    if state_dir is not None:
        base = Path(state_dir)
        filename = f"{workflow_id}_state_{issue_number}.json" if issue_number is not None else f"{workflow_id}.json"
        return base / filename
    base_cwd = Path(cwd or ".")
    return base_cwd / ".pdd" / "workflow-state" / f"{workflow_id}.json"


def load_workflow_state(
    cwd: Optional[Union[str, Path]] = None,
    issue_number: int = 0,
    workflow_type: Optional[str] = None,
    state_dir: Optional[Union[str, Path]] = None,
    repo_owner: str = "",
    repo_name: str = "",
    use_github_state: bool = True,
    *,
    workflow_id: Optional[str] = None,
) -> Tuple[Optional[Dict[str, Any]], Optional[int]]:
    """Load workflow state from GitHub issue comments."""
    workflow = workflow_id or workflow_type or "workflow"
    if _should_use_github_state(use_github_state) and repo_owner and repo_name and issue_number:
        state, comment_id = github_load_state(repo_owner, repo_name, issue_number, workflow, cwd=cwd)
        if state is not None:
            return state, comment_id

    local_path = _local_state_path(cwd, workflow, issue_number or None, state_dir)
    try:
        if local_path.is_file():
            return json.loads(local_path.read_text(encoding="utf-8")), None
    except Exception:
        pass
    return None, None


def _save_local_state(
    workflow_id: str,
    state: Dict[str, Any],
    cwd: Optional[Union[str, Path]] = None,
    issue_number: Optional[int] = None,
    state_dir: Optional[Union[str, Path]] = None,
) -> None:
    try:
        path = _local_state_path(cwd, workflow_id, issue_number, state_dir)
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2, default=str)
    except Exception:
        pass


def github_load_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_id: str,
    cwd: Optional[Union[str, Path]] = None,
) -> Tuple[Optional[Dict[str, Any]], Optional[int]]:
    if not _gh_available():
        return None, None
    comment_id, state = _find_state_comment(
        repo_owner, repo_name, issue_number, workflow_id, cwd=str(cwd) if cwd is not None else None
    )
    return state, comment_id


def github_save_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_id: str,
    state: Dict[str, Any],
    comment_id: Optional[int] = None,
    cwd: Optional[Union[str, Path]] = None,
) -> Optional[int]:
    if not _gh_available():
        return None

    payload = json.dumps(state, default=str)
    body = (f"## PDD Workflow State\n\n"
            f"Workflow: `{workflow_id}`\n"
            f"Updated: {datetime.now(timezone.utc).isoformat()}\n\n"
            f"{_STATE_MARKER_PREFIX}{workflow_id}:{payload}{_STATE_MARKER_SUFFIX}")

    if comment_id is None:
        existing_id, _ = _find_state_comment(
            repo_owner, repo_name, issue_number, workflow_id,
            cwd=str(cwd) if cwd is not None else None,
        )
        comment_id = existing_id

    if comment_id:
        rc, stdout, stderr = _gh_run(
            ["api", "--method", "PATCH",
             f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
             "-f", f"body={body}"],
            cwd=str(cwd) if cwd is not None else None,
        )
        return comment_id if rc == 0 else None

    rc, stdout, stderr = _gh_run(
        ["api", "--method", "POST",
         f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
         "-f", f"body={body}"],
        cwd=str(cwd) if cwd is not None else None,
    )
    if rc != 0:
        return None
    try:
        data = json.loads(stdout)
    except json.JSONDecodeError:
        return None
    return data.get("id")


def save_workflow_state(
    cwd: Optional[Union[str, Path]] = None,
    issue_number: int = 0,
    workflow_type: Optional[str] = None,
    state: Optional[Dict[str, Any]] = None,
    state_dir: Optional[Union[str, Path]] = None,
    repo_owner: str = "",
    repo_name: str = "",
    use_github_state: bool = True,
    github_comment_id: Optional[int] = None,
    *,
    workflow_id: Optional[str] = None,
    comment_id: Optional[int] = None,
) -> Optional[int]:
    """Save state. Returns comment_id on success, None on GitHub failure."""
    workflow = workflow_id or workflow_type or "workflow"
    state = state or {}
    _save_local_state(workflow, state, cwd=cwd, issue_number=issue_number or None, state_dir=state_dir)

    if not _should_use_github_state(use_github_state):
        return comment_id if comment_id is not None else github_comment_id

    saved_id = github_save_state(
        repo_owner,
        repo_name,
        issue_number,
        workflow,
        state,
        comment_id=comment_id if comment_id is not None else github_comment_id,
        cwd=cwd,
    )
    if saved_id is None:
        console.print("[yellow]GitHub workflow state save failed; local state was written.[/yellow]")
    return saved_id


def clear_workflow_state(
    cwd: Optional[Union[str, Path]] = None,
    issue_number: int = 0,
    workflow_type: Optional[str] = None,
    state_dir: Optional[Union[str, Path]] = None,
    repo_owner: str = "",
    repo_name: str = "",
    use_github_state: bool = True,
    *,
    workflow_id: Optional[str] = None,
) -> None:
    """Delete the state comment and local cache."""
    workflow = workflow_id or workflow_type or "workflow"
    try:
        local_path = _local_state_path(cwd, workflow, issue_number or None, state_dir)
        if local_path.exists():
            local_path.unlink()
    except Exception:
        pass

    if not (_should_use_github_state(use_github_state) and _gh_available() and repo_owner and repo_name and issue_number):
        return
    comment_id, _ = _find_state_comment(
        repo_owner, repo_name, issue_number, workflow,
        cwd=str(cwd) if cwd is not None else None,
    )
    if comment_id:
        _gh_run(
            ["api", "--method", "DELETE",
             f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}"],
            cwd=str(cwd) if cwd is not None else None,
        )


def github_clear_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow_id: str,
    cwd: Optional[Union[str, Path]] = None,
) -> None:
    clear_workflow_state(
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        workflow_id=workflow_id,
        cwd=cwd,
        use_github_state=True,
    )


# -----------------------------------------------------------------------------
# State validation
# -----------------------------------------------------------------------------

def validate_cached_state(
    last_completed_step: Union[int, float],
    step_outputs: Dict[str, str],
    step_order: Optional[List[Union[str, int]]] = None,
    quiet: bool = False,
) -> Union[int, float]:
    """Scan step_outputs for FAILED markers; return corrected last completed step."""
    if not step_outputs:
        return last_completed_step

    corrected = last_completed_step
    if step_order:
        for idx, step_name in enumerate(step_order):
            key = str(step_name)
            output = step_outputs.get(key, step_outputs.get(step_name, ""))  # type: ignore[arg-type]
            if isinstance(output, str) and "FAILED:" in output:
                step_num: Union[int, float]
                try:
                    step_num = int(step_name)
                except (TypeError, ValueError):
                    step_num = idx + 1
                if step_num <= corrected:
                    if idx > 0:
                        try:
                            corrected = int(step_order[idx - 1])
                        except (TypeError, ValueError):
                            corrected = idx
                    else:
                        corrected = 0
                    if not quiet:
                        console.print(
                            f"[yellow]State validation: step '{key}' shows FAILED; "
                            f"rolling back to {corrected}[/yellow]"
                        )
                    break
    else:
        for key, output in step_outputs.items():
            if isinstance(output, str) and "FAILED:" in output:
                if not quiet:
                    console.print(
                        f"[yellow]State validation: step '{key}' shows FAILED[/yellow]"
                    )
                try:
                    match = re.search(r"\d+", key)
                    step_num = int(match.group()) if match else 0
                    if step_num <= corrected:
                        corrected = max(0, step_num - 1)
                except (AttributeError, ValueError):
                    pass
    return corrected


# -----------------------------------------------------------------------------
# GitHub Progress Comments
# -----------------------------------------------------------------------------

def post_step_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    step_num: int,
    total_steps: int,
    description: str,
    output: str,
    cwd: Optional[str] = None,
) -> bool:
    """Post per-step progress comment to GitHub issue."""
    if not _gh_available():
        return False
    snippet = output[-3000:] if len(output) > 3000 else output
    body = (f"### Step {step_num}/{total_steps}: {description}\n\n"
            f"```\n{snippet}\n```")
    rc, _, _ = _gh_run(
        ["issue", "comment", str(issue_number),
         "--repo", f"{repo_owner}/{repo_name}",
         "--body", body],
        cwd=cwd,
    )
    return rc == 0


def post_pr_comment(
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    body: str,
    cwd: Optional[str] = None,
) -> bool:
    """Post a comment to a PR."""
    if not _gh_available():
        return False
    rc, _, _ = _gh_run(
        ["pr", "comment", str(pr_number),
         "--repo", f"{repo_owner}/{repo_name}",
         "--body", body],
        cwd=cwd,
    )
    return rc == 0


def post_final_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    reason: str = "",
    cwd: Optional[Union[str, Path]] = None,
    *,
    total_cost: Optional[float] = None,
    steps_completed: Optional[int] = None,
    total_steps: Optional[int] = None,
    body: Optional[str] = None,
) -> bool:
    """Post final workflow summary comment to issue.

    Accepts either a pre-built ``body`` (used by simple callers/tests) or the
    structured ``reason`` / ``total_cost`` / ``steps_completed`` / ``total_steps``
    fields used by orchestrators that report workflow-level stop reasons.
    """
    if not _gh_available():
        return False

    if body is None:
        if total_cost is not None or steps_completed is not None or total_steps is not None:
            body = (
                f"## Workflow Stopped\n\n"
                f"**Reason:** {reason}\n\n"
                f"**Progress:** Completed through step "
                f"{steps_completed or 0}/{total_steps or 0}\n"
                f"**Total cost:** ${(total_cost or 0.0):.4f}\n\n"
                f"---\n"
                f"*Automated status comment — pdd-fix workflow exited early.*"
            )
        else:
            body = reason

    rc, _, _ = _gh_run(
        ["issue", "comment", str(issue_number),
         "--repo", f"{repo_owner}/{repo_name}",
         "--body", body],
        cwd=str(cwd) if cwd is not None else None,
    )
    return rc == 0


def _revert_out_of_scope_changes(cwd: Union[str, Path], allowed_files: Set[Path]) -> List[Path]:
    """Revert tracked and remove untracked files outside the allowed file set."""
    root = Path(cwd)
    allowed = {Path(p).resolve() for p in allowed_files}
    reverted: List[Path] = []
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "-u"],
            cwd=str(root),
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (subprocess.TimeoutExpired, OSError):
        return reverted
    if result.returncode != 0:
        return reverted

    for line in result.stdout.splitlines():
        if len(line) < 4:
            continue
        status = line[:2]
        raw_path = line[3:].strip().strip('"')
        if " -> " in raw_path:
            raw_path = raw_path.split(" -> ")[-1]
        rel_path = Path(raw_path)
        abs_path = (root / rel_path).resolve()
        if abs_path in allowed:
            continue

        if status == "??":
            try:
                abs_path.unlink()
                reverted.append(rel_path)
            except OSError:
                pass
            continue

        try:
            checkout = subprocess.run(
                ["git", "checkout", "HEAD", "--", raw_path],
                cwd=str(root),
                capture_output=True,
                text=True,
                timeout=30,
            )
            if checkout.returncode == 0:
                reverted.append(rel_path)
        except (subprocess.TimeoutExpired, OSError):
            pass
    return reverted
