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

_SEMANTIC_TAIL_LINES = 30

SEMANTIC_PATTERNS: Dict[str, List[str]] = {
    "ALL_TESTS_PASS": [
        r"\ball\b.*\btests?\b.*\bpass",
        r"\d+/\d+\s+pass",
        r"both\s+passed",
        r"all\s+tests?\s+(are\s+)?green",
        r"all\s+tests?\s+passed\s+successfully",
        r"tests?\s+suite\s+passed",
        r"100%\s+pass",
        r"\b\d+\s+passed\b(?!.*\b\d+\s+failed\b)",
        r"\bfix\b.*\bcomplete\b",
        r"\bverif(?:ied|ication)\b.*\bcleanly\b",
    ],
    "NOT_A_BUG": [
        r"\bnot\s+(?:actually\s+)?(?:a\s+)?(?:real\s+)?bug\b",
        r"(it\s+is\s+|already\s+)fixed",
        r"expected\s+behavio[u]?r",
        r"working\s+(as\s+)?(designed|intended|correctly|expected)",
        r"not\s+(actually\s+)?a\s+(code\s+)?issue",
    ],
    "CONTINUE_CYCLE": [
        r"tests?\s+still\s+fail",
        r"more\s+work\s+needed",
        r"not\s+yet\s+(fixed|resolved|passing)",
        r"continue\s+(to\s+)?(next\s+)?cycle",
    ],
    "MAX_CYCLES_REACHED": [
        r"max(imum)?\s+cycles?\s+(reached|exceeded|limit)",
        r"cycle\s+limit\s+(reached|exceeded)",
    ],
    "STOP_CONDITION": [
        r"awaiting\s+(architectural\s+)?decisions",
        r"clarification\s+(is\s+)?needed",
        r"need[s]?\s+clarification\s+(from|before)",
        r"need[s]?\s+more\s+info(rmation)?\s+(from|before)",
    ],
}


@dataclass
class TokenMatch:
    """Result of control token detection with tier and pattern info."""
    tier: str
    token: Optional[str] = None
    pattern: Optional[str] = None
    cost: Optional[float] = None

    def __bool__(self) -> bool:
        return True


def detect_control_token(
    output: Optional[str],
    token: str,
    tail_lines: int = _SEMANTIC_TAIL_LINES,
) -> Optional[TokenMatch]:
    """Detect a control token in LLM output with three-tier fallback."""
    if not output:
        return None

    if token in output:
        return TokenMatch(tier="exact", token=token)

    output_upper = output.upper()
    if token.upper() in output_upper:
        return TokenMatch(tier="case_insensitive", token=token)

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
    """Classify step output via LLM when regex-based detection fails."""
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
    """Safely substitute known {placeholders} without raising on unknown keys."""
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
    """Return provider preference order, overridable via PDD_AGENTIC_PROVIDER env var."""
    env_val = os.environ.get("PDD_AGENTIC_PROVIDER", "")
    if env_val:
        return [p.strip() for p in env_val.split(",") if p.strip()]
    return _DEFAULT_PROVIDER_PREFERENCE


CLI_COMMANDS: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
    "opencode": "opencode",
}

_COMMON_CLI_PATHS: Dict[str, List[Path]] = {
    "claude": [
        Path.home() / ".npm-global" / "bin" / "claude",
        Path.home() / ".local" / "bin" / "claude",
        Path.home() / "bin" / "claude",
        Path("/usr/local/bin/claude"),
        Path("/opt/homebrew/bin/claude"),
        Path("/home/linuxbrew/.linuxbrew/bin/claude"),
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

MAX_PDDRC_SEARCH_DEPTH: int = 10

DEFAULT_TIMEOUT_SECONDS: float = 600.0
MIN_VALID_OUTPUT_LENGTH: int = 50
DEFAULT_MAX_RETRIES: int = 3
DEFAULT_RETRY_DELAY: float = 5.0
MAX_RETRY_DELAY: float = 120.0
MAX_PATH_DISPLAY_LENGTH: int = 200
MAX_ERROR_SNIPPET_LENGTH: int = 2000
MAX_ERROR_RESPONSE_NEWLINES: int = 3


def _is_rate_limited(error_message: str) -> bool:
    """Detect transient rate-limit errors that need extended backoff."""
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


RATE_LIMIT_BACKOFF_FLOOR: float = 60.0


def _is_permanent_error(error_message: str) -> bool:
    """Detect permanent provider errors that should NOT be retried."""
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
        r"quota\s+(exhausted|exceeded)",
        r"daily\s+quota",
        r"terminal\s*quota\s*error",
        r"credit\s+balance\s+is\s+too\s+low",
        r"plans\s*&\s*billing",
        r"insufficient\s+(credit|balance|funds)",
        r"not\s+logged\s+in",
        r"please\s+run\s+/login",
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
    """Clear progress context."""
    global _agentic_interrupt_context
    _agentic_interrupt_context = None


def get_and_clear_agentic_interrupt_context() -> Optional[Dict[str, Any]]:
    """Return current progress and clear it."""
    global _agentic_interrupt_context
    ctx = _agentic_interrupt_context
    _agentic_interrupt_context = None
    return ctx


JOB_TIMEOUT_MARGIN_SECONDS: float = 120.0
MIN_ATTEMPT_TIMEOUT_SECONDS: float = 60.0


def get_job_deadline() -> Optional[float]:
    """Return the absolute Unix timestamp deadline from PDD_JOB_DEADLINE env var."""
    val = os.environ.get("PDD_JOB_DEADLINE")
    if val:
        try:
            return float(val)
        except (ValueError, TypeError):
            return None
    return None


GITHUB_STATE_MARKER_START = "<!-- PDD_WORKFLOW_STATE:"
GITHUB_STATE_MARKER_END = "-->"


@dataclass
class Pricing:
    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 1.0


GEMINI_PRICING_BY_FAMILY = {
    "flash": Pricing(0.35, 1.05, 0.5),
    "pro": Pricing(3.50, 10.50, 0.5),
}

CODEX_PRICING = Pricing(1.50, 6.00, 0.25)

ANTHROPIC_PRICING_BY_FAMILY = {
    "opus": Pricing(15.0, 75.0, 0.1),
    "sonnet": Pricing(3.0, 15.0, 0.1),
    "haiku": Pricing(0.80, 4.0, 0.1),
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
    """Return the requested model for *provider* from its env var."""
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
    """Append one record per provider attempt to the session JSONL log."""
    global _AGENTIC_SESSION_ID

    try:
        log_dir = Path(cwd) / AGENTIC_LOG_DIR
        log_dir.mkdir(parents=True, exist_ok=True)

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
        pass


# ---------------------------------------------------------------------------
# CLI Discovery
# ---------------------------------------------------------------------------


def _load_agentic_config() -> Dict[str, Any]:
    """Load agentic CLI configuration from .pddrc."""
    try:
        import yaml
    except ImportError:
        return {}

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
    """Find a CLI binary using multiple strategies."""
    if config is None:
        config = _load_agentic_config()

    config_key = f"{name}_path"
    if config_key in config:
        custom_path = Path(config[config_key])
        if custom_path.exists() and os.access(custom_path, os.X_OK):
            return str(custom_path)

    path_result = shutil.which(name)
    if path_result:
        return path_result

    for path in _iter_common_cli_paths(name):
        if "nvm" in str(path) and path.name == "node":
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
    """Return common CLI paths, including runtime-expanded home paths."""
    paths = list(_COMMON_CLI_PATHS.get(name, []))
    if name in {"claude", "codex", "gemini", "opencode"}:
        home = Path.home()
        paths.extend([
            home / ".npm-global" / "bin" / name,
            home / ".local" / "bin" / name,
            home / "bin" / name,
            home / ".nvm" / "versions" / "node",
        ])

    seen: set = set()
    unique_paths: List[Path] = []
    for path in paths:
        key = str(path)
        if key in seen:
            continue
        seen.add(key)
        unique_paths.append(path)
    return unique_paths


def _get_cli_diagnostic_info(name: str) -> str:
    """Generate diagnostic information for CLI discovery failures."""
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
    """Returns list of available provider names based on CLI existence and API key configuration."""
    available = []

    if _find_cli_binary("claude"):
        available.append("anthropic")

    has_gemini_cli = _find_cli_binary("gemini") is not None
    has_google_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    has_vertex_auth = (
        os.environ.get("GOOGLE_GENAI_USE_VERTEXAI") == "true"
        and (
            os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
            or os.environ.get("GOOGLE_CLOUD_PROJECT")
        )
    )
    has_gemini_oauth = _has_gemini_oauth_credentials()

    if has_gemini_cli and (has_google_key or has_vertex_auth or has_gemini_oauth):
        available.append("google")

    has_codex_oauth = _has_codex_auth_file()
    if _find_cli_binary("codex") and (
        os.environ.get("OPENAI_API_KEY")
        or os.environ.get("PDD_CODEX_AUTH_AVAILABLE")
        or has_codex_oauth
    ):
        available.append("openai")

    if _find_cli_binary("opencode") and _has_opencode_credentials():
        available.append("opencode")

    return available


def _has_gemini_oauth_credentials() -> bool:
    """Return True when Gemini CLI stored OAuth credentials are present."""
    creds_path = Path.home() / ".gemini" / "oauth_creds.json"
    try:
        data = json.loads(creds_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    return bool(data.get("refresh_token") or data.get("access_token"))


def _has_codex_auth_file() -> bool:
    """Return True when Codex CLI stored ChatGPT login is present."""
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
# OpenCode helpers
# ---------------------------------------------------------------------------

_OPENCODE_PROVIDER_ENV_KEYS_FALLBACK: Tuple[str, ...] = (
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

_OPENCODE_ENV_VAR_TO_PROVIDER: Dict[str, str] = {
    "GITHUB_TOKEN": "github-copilot",
}


def _opencode_provider_env_keys() -> Tuple[str, ...]:
    """Return the union of provider credential env vars from llm_model.csv."""
    keys: set = set(_OPENCODE_PROVIDER_ENV_KEYS_FALLBACK)
    try:
        df = _load_model_data(None)
    except Exception:
        df = None
    if df is not None and not getattr(df, "empty", True):
        try:
            for raw in df["api_key"].dropna().tolist():
                field = str(raw).strip()
                if not field or field.lower() == "api_key":
                    continue
                for k in field.split("|"):
                    k = k.strip()
                    if k:
                        keys.add(k)
        except Exception:
            pass
    return tuple(sorted(keys))


def _opencode_auth_file_has_credentials(path: Path) -> bool:
    """Return True when ``path`` is an OpenCode auth.json with usable provider data."""
    try:
        if not path.exists() or path.stat().st_size == 0:
            return False
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict) or not data:
        return False
    for value in data.values():
        if isinstance(value, dict) and value:
            return True
        if isinstance(value, str) and value.strip():
            return True
    return False


def _opencode_config_paths(cwd: Optional[Path] = None) -> List[Path]:
    """Return candidate OpenCode config file locations (existing files only)."""
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
    seen: set = set()
    unique: List[Path] = []
    for p in paths:
        key = str(p)
        if key in seen:
            continue
        seen.add(key)
        unique.append(p)
    return unique


_OPENCODE_PROVIDER_CREDENTIAL_FIELDS = frozenset(
    {"apikey", "key", "token", "bearer", "bearertoken", "accesstoken", "secret"}
)

_JSONC_TOKEN_RE = re.compile(
    r'"(?:\\.|[^"\\])*"'
    r'|/\*[\s\S]*?\*/'
    r'|//[^\n]*'
)


def _strip_jsonc_comments(text: str) -> str:
    """Strip JSONC line/block comments while preserving string contents."""
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


def _opencode_data_declares_provider(
    data: Optional[Dict[str, Any]],
    base_dir: Optional[Path] = None,
) -> bool:
    """Return True when parsed OpenCode config declares usable provider auth."""
    if not isinstance(data, dict):
        return False
    provider = data.get("provider")
    if isinstance(provider, dict):
        for value in provider.values():
            if _opencode_provider_value_has_usable_credential(value, base_dir=base_dir):
                return True
    return False


def _iter_opencode_config_texts(
    cwd: Optional[Path] = None,
) -> List[Tuple[str, Optional[Path]]]:
    """Yield ``(text, base_dir)`` pairs from all OpenCode config sources."""
    texts: List[Tuple[str, Optional[Path]]] = []
    for cfg in _opencode_config_paths(cwd):
        try:
            texts.append((cfg.read_text(encoding="utf-8"), cfg.parent))
        except OSError:
            continue
    inline = os.environ.get("OPENCODE_CONFIG_CONTENT", "")
    if inline and inline.strip():
        texts.append((inline, None))
    return texts


_OPENCODE_PROVIDER_CREDENTIAL_CONTAINERS = frozenset({"options", "auth", "headers"})


def _resolve_opencode_template_value(
    value: Any,
    base_dir: Optional[Path] = None,
) -> Optional[str]:
    """Resolve an OpenCode config template ``{env:VAR}`` / ``{file:PATH}``."""
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
        raw = m.group(1).strip()
        candidate = Path(raw).expanduser()
        if not candidate.is_absolute() and base_dir is not None and not raw.startswith("~"):
            candidate = base_dir / candidate
        try:
            text = candidate.read_text(encoding="utf-8").strip()
        except OSError:
            return None
        return text or None
    return s


def _opencode_provider_value_has_usable_credential(
    value: Any,
    base_dir: Optional[Path] = None,
) -> bool:
    """Return True when an OpenCode ``provider.<id>`` value carries usable auth."""
    if isinstance(value, str):
        return _resolve_opencode_template_value(value, base_dir=base_dir) is not None
    if not isinstance(value, dict):
        return False
    for key, sub in value.items():
        if not isinstance(key, str):
            continue
        normalized = key.lower().replace("-", "").replace("_", "")
        if normalized in _OPENCODE_PROVIDER_CREDENTIAL_FIELDS:
            if isinstance(sub, str):
                if _resolve_opencode_template_value(sub, base_dir=base_dir) is not None:
                    return True
            elif isinstance(sub, dict):
                for v in sub.values():
                    if isinstance(v, str) and _resolve_opencode_template_value(v, base_dir=base_dir) is not None:
                        return True
            continue
        if normalized in _OPENCODE_PROVIDER_CREDENTIAL_CONTAINERS and isinstance(sub, dict):
            if _opencode_provider_value_has_usable_credential(sub, base_dir=base_dir):
                return True
    return False


def _opencode_config_declares_provider(path: Path) -> bool:
    """Return True when an OpenCode config file declares usable provider auth."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return False
    return _opencode_data_declares_provider(
        _parse_opencode_config_text(text), base_dir=path.parent
    )


def _has_opencode_credentials(cwd: Optional[Path] = None) -> bool:
    """Return True when any OpenCode credential signal is present."""
    auth_path = Path.home() / ".local" / "share" / "opencode" / "auth.json"
    if _opencode_auth_file_has_credentials(auth_path):
        return True
    for text, base_dir in _iter_opencode_config_texts(cwd):
        if _opencode_data_declares_provider(
            _parse_opencode_config_text(text), base_dir=base_dir
        ):
            return True
    for key in _opencode_provider_env_keys():
        val = os.environ.get(key)
        if val and val.strip():
            return True
    return False


def _translate_to_opencode_model(model_id: str) -> str:
    """Translate LiteLLM-oriented model IDs to OpenCode ``provider/model`` form."""
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
    """Return the OpenCode provider IDs that have a usable credential source."""
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

    for text, base_dir in _iter_opencode_config_texts(cwd):
        cfg_data = _parse_opencode_config_text(text)
        if not isinstance(cfg_data, dict):
            continue
        provider_dict = cfg_data.get("provider")
        if isinstance(provider_dict, dict):
            for k, v in provider_dict.items():
                if _opencode_provider_value_has_usable_credential(v, base_dir=base_dir):
                    providers.add(k)

    try:
        df = _load_model_data(None)
    except Exception:
        df = None
    if df is not None and not getattr(df, "empty", True):
        for _, row in df.iterrows():
            api_key_field = str(row.get("api_key") or "").strip()
            if not api_key_field:
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
            if "/" not in translated:
                continue
            prefix = translated.split("/", 1)[0]
            if prefix:
                providers.add(prefix)

    for env_var, provider_id in _OPENCODE_ENV_VAR_TO_PROVIDER.items():
        if (src.get(env_var) or "").strip():
            providers.add(provider_id)

    return providers


def _resolve_opencode_csv_fallback(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> Optional[str]:
    """Pick an OpenCode model from ``llm_model.csv`` using auth-aware filtering."""
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

    for _, row in sorted_df.iterrows():
        model_id = str(row.get("model") or "").strip()
        if not model_id:
            continue
        translated = _translate_to_opencode_model(model_id)
        if "/" not in translated:
            continue
        prefix = translated.split("/", 1)[0]
        if prefix in configured:
            return translated
    return None


def _opencode_csv_cost(model_id: Optional[str], tokens: Optional[Dict[str, Any]]) -> float:
    """Compute USD cost for an OpenCode run from the CSV pricing row."""
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
    candidates = [model_id]
    if "/" in model_id:
        head, tail = model_id.split("/", 1)
        if head == "github-copilot":
            candidates.append("github_copilot/" + tail)
        elif head == "google":
            candidates.append("gemini/" + tail)
        elif head == "anthropic" and tail.startswith("claude-"):
            candidates.append(tail)
        elif head == "openai" and tail.startswith("gpt-"):
            candidates.append(tail)
        else:
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
    """Resolve the OpenCode model from ``OPENCODE_MODEL`` only."""
    src = env if env is not None else os.environ
    raw = (src.get("OPENCODE_MODEL") or "").strip()
    if raw:
        return raw
    return None


def _resolve_opencode_model_for_run(
    env: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
) -> Optional[str]:
    """Resolve the OpenCode model with auth-aware CSV fallback."""
    src = env if env is not None else os.environ
    raw = (src.get("OPENCODE_MODEL") or "").strip()
    if raw:
        return raw
    return _resolve_opencode_csv_fallback(env=src, cwd=cwd)


def _parse_opencode_jsonl(stdout: str) -> Dict[str, Any]:
    """Parse OpenCode JSONL output into a normalized accounting dict."""
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

        family = "flash" if "flash" in model_name.lower() else "pro"
        pricing = GEMINI_PRICING_BY_FAMILY.get(family, GEMINI_PRICING_BY_FAMILY["flash"])

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

    new_input = max(0, input_tokens - cached_tokens)

    input_cost = (new_input / 1_000_000) * pricing.input_per_million
    cached_cost = (cached_tokens / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    output_cost = (output_tokens / 1_000_000) * pricing.output_per_million

    return input_cost + cached_cost + output_cost


def _calculate_anthropic_cost(data: Dict[str, Any]) -> float:
    """Calculate cost from Claude Code JSON when total_cost_usd is missing."""
    model_usage = data.get("modelUsage", {})
    if model_usage:
        total = sum(
            float(info.get("costUSD", 0.0))
            for info in model_usage.values()
            if isinstance(info, dict)
        )
        if total > 0:
            return total

    usage = data.get("usage", {})
    if not usage:
        return 0.0

    input_tokens = usage.get("input_tokens", 0)
    output_tokens = usage.get("output_tokens", 0)
    cache_read = usage.get("cache_read_input_tokens", 0)
    cache_creation = usage.get("cache_creation_input_tokens", 0)

    family = "sonnet"
    for model_name in model_usage.keys():
        name_lower = model_name.lower()
        if "opus" in name_lower:
            family = "opus"
            break
        elif "haiku" in name_lower:
            family = "haiku"
            break

    pricing = ANTHROPIC_PRICING_BY_FAMILY.get(family, ANTHROPIC_PRICING_BY_FAMILY["sonnet"])

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
    """Runs an agentic task using available providers in preference order."""
    agents = get_available_agents()

    candidates = [p for p in get_agent_provider_preference() if p in agents]

    if not candidates:
        msg = "No agent providers are available (check CLI installation and API keys)"
        if not quiet:
            console.print(f"[bold red]{msg}[/bold red]")
        return False, msg, 0.0, ""

    effective_timeout = timeout if timeout is not None else DEFAULT_TIMEOUT_SECONDS
    effective_deadline = deadline if deadline is not None else get_job_deadline()
    task_start_time = time.time()
    aggregate_deadline = task_start_time + (2 * effective_timeout)

    prompt_filename = f".agentic_prompt_{uuid.uuid4().hex[:8]}.txt"
    prompt_path = cwd / prompt_filename

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
        with open(prompt_path, "w", encoding="utf-8") as f:
            f.write(full_instruction)

        provider_errors: List[str] = []

        for provider in candidates:
            if verbose:
                console.print(f"[dim]Attempting provider: {provider} for task '{label}'[/dim]")

            if time.time() > aggregate_deadline:
                if verbose:
                    console.print(f"[yellow]Aggregate step timeout exceeded. Skipping {provider}.[/yellow]")
                break

            last_output = ""
            deadline_exhausted = False
            any_attempt_logged_inside = False
            actual_model: Optional[str] = None
            effective_model: Optional[str] = _get_provider_model(provider)
            for attempt in range(1, max_retries + 1):
                now = time.time()
                budgets = []
                if effective_deadline is not None:
                    budgets.append(effective_deadline - now - JOB_TIMEOUT_MARGIN_SECONDS)
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
                effective_model = actual_model or _get_provider_model(provider)

                if success:
                    stripped_output = output.strip()
                    output_length = len(stripped_output)
                    is_false_positive = (
                        output_length == 0 or
                        (cost == 0.0 and output_length < MIN_VALID_OUTPUT_LENGTH) or
                        (
                            cost > 0.0
                            and stripped_output.startswith("Error:")
                            and stripped_output.count("\n") < MAX_ERROR_RESPONSE_NEWLINES
                            and output_length < 4000
                        )
                    )

                    if is_false_positive:
                        if not quiet:
                            console.print(f"[yellow]Provider '{provider}' returned false positive (attempt {attempt}/{max_retries})[/yellow]")
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
                        if len(candidates) == 1 and attempt < max_retries:
                            base_backoff = retry_delay * (2 ** (attempt - 1))
                            jitter = random.uniform(0, retry_delay)
                            backoff = min(base_backoff + jitter, MAX_RETRY_DELAY)
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
                        suspicious = []
                        for name in ["C", "E", "T"]:
                            if (cwd / name).exists():
                                suspicious.append(name)

                        if suspicious:
                            console.print(f"[bold red]SUSPICIOUS FILES DETECTED: {', '.join(['- ' + s for s in suspicious])}[/bold red]")

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

                if attempt < max_retries:
                    base_backoff = retry_delay * (2 ** (attempt - 1))
                    jitter = random.uniform(0, retry_delay)
                    backoff = min(base_backoff + jitter, MAX_RETRY_DELAY)
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

            provider_errors.append(f"{provider}: {last_output[:MAX_ERROR_SNIPPET_LENGTH]}")
            if verbose:
                console.print(f"[yellow]Provider {provider} failed after {max_retries} attempts: {last_output}[/yellow]")
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
            if deadline_exhausted or time.time() > aggregate_deadline:
                break

        return False, f"All agent providers failed: {'; '.join(provider_errors)}", 0.0, ""

    finally:
        if prompt_path.exists():
            try:
                os.remove(prompt_path)
            except OSError:
                pass


import logging as _logging
_scope_guard_logger = _logging.getLogger(__name__ + ".scope_guard")


def _revert_out_of_scope_changes(
    cwd: Path,
    allowed_paths: set,
) -> List[Path]:
    """Revert any git-tracked file changes outside the allowed set."""
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
    """Cached `claude auth status` output for OAuth detection (Issue #813)."""
    cli_path = _find_cli_binary("claude")
    if not cli_path:
        return {}

    probe_env = os.environ.copy()
    probe_env.pop("ANTHROPIC_API_KEY", None)
    probe_env.pop("ANTHROPIC_AUTH_TOKEN", None)

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
    "claude.ai",
    "oauth_token",
})


def _claude_has_oauth_login() -> bool:
    """True when Claude Code has a usable first-party OAuth credential."""
    info = _probe_claude_auth_status()
    return (
        bool(info.get("loggedIn"))
        and info.get("authMethod") in _CLAUDE_OAUTH_AUTH_METHODS
        and info.get("apiProvider") == "firstParty"
    )


def _strip_anthropic_creds_for_claude_subprocess(
    env: Dict[str, str], *, verbose: bool = False, quiet: bool = False
) -> bool:
    """Pop stale ANTHROPIC_API_KEY / ANTHROPIC_AUTH_TOKEN when claude has OAuth."""
    if env.get("CLAUDE_CODE_USE_BEDROCK") or env.get("CLAUDE_CODE_USE_VERTEX"):
        return False

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
    """Wrapper around subprocess that uses Popen for proper process group cleanup."""
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
    """Internal helper to run a specific provider's CLI."""
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    env.pop("PDD_OUTPUT_COST_PATH", None)
    env["GIT_WORK_TREE"] = str(cwd)

    if provider == "anthropic":
        _strip_anthropic_creds_for_claude_subprocess(env, verbose=verbose, quiet=quiet)

    cli_name = CLI_COMMANDS.get(provider)
    if not cli_name:
        return False, f"Unknown provider {provider}", 0.0, None

    if cli_path is None:
        cli_path = _find_cli_binary(cli_name)
    if not cli_path:
        return False, f"CLI '{cli_name}' not found. {_get_cli_diagnostic_info(cli_name)}", 0.0, None

    cmd: List[str] = []

    prompt_content = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else ""

    if reasoning_time is not None:
        try:
            from .reasoning import time_to_effort_level
            reasoning_effort = time_to_effort_level(reasoning_time)
        except ImportError:
            reasoning_effort = ""
    else:
        reasoning_effort = (env.get("PDD_REASONING_EFFORT") or "").strip().lower()
        if reasoning_effort not in {"low", "medium", "high"}:
            reasoning_effort = ""

    if provider == "anthropic":
        if use_playwright:
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
        claude_model = env.get("CLAUDE_MODEL")
        if claude_model:
            cmd.extend(["--model", claude_model])
        if reasoning_effort and not quiet:
            console.print(
                f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but Claude Code CLI "
                "has no reasoning-effort flag; applies to llm_invoke steps only, "
                "not this subprocess.[/dim]"
            )
    elif provider == "google":
        cmd = [
            cli_path,
            f"Read the file {prompt_path.name} for your full instructions and execute them.",
            "--yolo",
            "--output-format", "json"
        ]
        gemini_model = env.get("GEMINI_MODEL")
        if gemini_model:
            cmd.extend(["--model", gemini_model])
        if reasoning_effort and not quiet:
            console.print(
                f"[dim]PDD_REASONING_EFFORT={reasoning_effort} requested, but Gemini CLI "
                "has no reasoning-effort flag; applies to llm_invoke steps only, "
                "not this subprocess.[/dim]"
            )
    elif provider == "openai":
        sandbox_mode = env.get("CODEX_SANDBOX_MODE", "danger-full-access")
        cmd = [cli_path]
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
        codex_model = env.get("CODEX_MODEL")
        if codex_model:
            cmd.extend(["--model", codex_model])
    elif provider == "opencode":
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
        cmd.append("--")
        cmd.append(
            f"Read the file {prompt_path.name} for your full instructions and execute them."
        )
    else:
        return False, f"Unknown provider {provider}", 0.0, None

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

    if provider == "opencode":
        parsed = _parse_opencode_jsonl(result.stdout)
        actual_model = parsed.get("model") or None
        err = parsed.get("error") or ""
        if parsed.get("cost_reported"):
            cost = float(parsed.get("cost") or 0.0)
        else:
            tokens = parsed.get("tokens") or {}
            csv_model_id = actual_model or _resolve_opencode_model_for_run(env, cwd=cwd)
            cost = _opencode_csv_cost(csv_model_id, tokens)
        if err:
            return False, str(err), cost, actual_model
        return (
            True,
            str(parsed.get("text") or ""),
            cost,
            actual_model,
        )

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

    try:
        output_str = result.stdout.strip()
        data = {}

        if provider == "openai" and "\n" in output_str:
            lines = output_str.splitlines()
            agent_message_data = None
            session_end = None
            for line in lines:
                try:
                    item = json.loads(line)
                    if item.get("type") == "result":
                        data = item
                        break
                    if (item.get("type") == "item.completed"
                            and isinstance(item.get("item"), dict)
                            and item["item"].get("type") == "agent_message"):
                        agent_message_data = item
                    if item.get("type") in ("session.end", "turn.completed"):
                        session_end = item
                except json.JSONDecodeError:
                    continue
            if not data:
                if agent_message_data is not None:
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
                    except Exception:
                        pass
        else:
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
        return False, f"Invalid JSON output: {result.stdout[:MAX_ERROR_SNIPPET_LENGTH]}...", 0.0, None


def _extract_json_from_output(output_str: str) -> dict:
    """Extract a JSON object from output that may contain non-JSON text."""
    for line in output_str.splitlines():
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            return json.loads(line)
        except json.JSONDecodeError:
            continue

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
    """Extract the actual model name from a provider's JSON response."""
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
    """Extracts (success, text_response, cost_usd, actual_model) from provider JSON."""
    cost = 0.0
    output_text = ""
    actual_model = _extract_provider_model_from_data(provider, data)

    try:
        if provider == "anthropic":
            cost = float(data.get("total_cost_usd", 0.0))
            if cost == 0.0:
                cost = _calculate_anthropic_cost(data)
            output_text = data.get("result") or data.get("response") or ""
            if data.get("is_error"):
                return False, str(output_text) or "CLI reported is_error with no message", cost, actual_model

        elif provider == "google":
            stats = data.get("stats", {})
            cost = _calculate_gemini_cost(stats)
            output_text = data.get("result") or data.get("response") or data.get("output") or ""

        elif provider == "openai":
            usage = data.get("usage", {})
            cost = _calculate_codex_cost(usage)
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
    """Returns (comment_id, state_dict) if found, else None."""
    if not _find_cli_binary("gh"):
        return None

    try:
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
    """Creates or updates a GitHub comment with the state."""
    if not _find_cli_binary("gh"):
        return None

    body = _serialize_state_comment(workflow_type, issue_number, state)

    try:
        if comment_id:
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
    """Wrapper to find state. Returns (state, comment_id)."""
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
    """Deletes the state comment if it exists."""
    result = _find_state_comment(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if not result:
        return True

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


def validate_cached_state(
    last_completed_step: Union[int, float],
    step_outputs: Dict[str, str],
    step_order: Optional[List[Union[int, float]]] = None,
    quiet: bool = False,
) -> Union[int, float]:
    """Validate cached state and return actual last successful step."""
    if not step_outputs:
        return last_completed_step

    if step_order is None:
        numeric_keys = []
        for k in step_outputs.keys():
            try:
                float(k)
                numeric_keys.append(k)
            except ValueError:
                continue
        step_order = sorted(numeric_keys, key=lambda k: float(k))
    else:
        step_order = [str(s) if not isinstance(s, str) else s for s in step_order]

    actual_last_success: Union[int, float] = 0
    for sn in step_order:
        key = str(sn)
        output_val = step_outputs.get(key, "")
        if not output_val:
            break
        if str(output_val).startswith("FAILED:"):
            break
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


def load_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True
) -> Tuple[Optional[Dict], Optional[int]]:
    """Loads state from GitHub (priority) or local file."""
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    if _should_use_github_state(use_github_state):
        gh_state, gh_id = github_load_state(repo_owner, repo_name, issue_number, workflow_type, cwd)
        if gh_state:
            try:
                state_dir.mkdir(parents=True, exist_ok=True)
                with open(local_file, "w") as f:
                    json.dump(gh_state, f, indent=2)
            except Exception:
                pass
            return gh_state, gh_id
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
    """Saves state to local file and GitHub. Returns updated github_comment_id."""
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    try:
        state_dir.mkdir(parents=True, exist_ok=True)
        tmp_file = local_file.with_suffix(".json.tmp")
        with open(tmp_file, "w") as f:
            json.dump(state, f, indent=2)
        tmp_file.replace(local_file)
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to save local state: {e}[/yellow]")

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
    """Clears local and GitHub state."""
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"

    if local_file.exists():
        try:
            os.remove(local_file)
        except Exception:
            pass

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
    """Post a fallback comment on a GitHub issue when a step fails."""
    if not _find_cli_binary("gh"):
        return False

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
    """Post a comment on a pull request."""
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
    """Post a final status comment when the workflow stops early."""
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