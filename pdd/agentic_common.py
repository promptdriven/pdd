from __future__ import annotations

import os
import sys
import json
import re
import time
import random
import shutil
import subprocess
import signal
import glob
import tempfile
import csv
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any, Tuple, Union

from rich.console import Console

console = Console()

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
DEFAULT_TIMEOUT_SECONDS: float = 600.0
MIN_VALID_OUTPUT_LENGTH: int = 50
DEFAULT_MAX_RETRIES: int = 3
DEFAULT_RETRY_DELAY: float = 5.0
MAX_RETRY_DELAY: float = 120.0
JOB_TIMEOUT_MARGIN_SECONDS: float = 120.0
MIN_ATTEMPT_TIMEOUT_SECONDS: float = 60.0
MAX_ERROR_SNIPPET_LENGTH: int = 2000
MAX_ERROR_RESPONSE_NEWLINES: int = 3

_DEFAULT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai", "opencode"]

_SEMANTIC_TAIL_LINES: int = 30

_LOG_DIR = Path(".pdd/agentic-logs")
_SESSION_LOG_PATH: Optional[Path] = None
_SESSION_LOG_BASE_CWD: Optional[Path] = None
_AGENTIC_SESSION_ID: Optional[str] = None

_GEMINI_OAUTH_PATH = Path.home() / ".gemini" / "oauth_creds.json"
_OPENCODE_AUTH_PATH = Path.home() / ".local" / "share" / "opencode" / "auth.json"

# Common CLI search paths
_COMMON_CLI_PATHS = [
    "/usr/local/bin",
    "/usr/bin",
    "/opt/homebrew/bin",
    "/home/linuxbrew/.linuxbrew/bin",
    str(Path.home() / ".local" / "bin"),
    str(Path.home() / ".npm-global" / "bin"),
    str(Path.home() / "node_modules" / ".bin"),
    str(Path.home() / ".cargo" / "bin"),
    str(Path.home() / ".bun" / "bin"),
]

_CLI_NAMES = {
    "anthropic": ["claude"],
    "google": ["gemini"],
    "openai": ["codex"],
    "opencode": ["opencode"],
}

# ---------------------------------------------------------------------------
# Token pricing
# ---------------------------------------------------------------------------
@dataclass
class Pricing:
    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 0.5

GEMINI_PRICING = {
    "flash": Pricing(0.35, 1.05, 0.5),
    "pro": Pricing(3.50, 10.50, 0.5),
}
CODEX_PRICING = Pricing(1.50, 6.00, 0.25)
ANTHROPIC_PRICING = {
    "opus": Pricing(15.0, 75.0, 0.1),
    "sonnet": Pricing(3.0, 15.0, 0.1),
    "haiku": Pricing(0.8, 4.0, 0.1),
}

# ---------------------------------------------------------------------------
# Control token detection
# ---------------------------------------------------------------------------
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
        r"\ball\s+(\d+\s+)?tests?\s+(are\s+)?(now\s+)?pass(es|ing|ed)?\b",
        r"\btests?\s+(all\s+)?pass(ed|ing)?\s+successfully\b",
        r"\b\d+\s+passed,?\s+0\s+failed\b",
        r"\bevery\s+test\s+(now\s+)?pass(es|ed)\b",
    ],
    "NOT_A_BUG": [
        r"\bnot\s+a\s+bug\b",
        r"\bworking\s+as\s+(intended|designed|expected)\b",
        r"\bno\s+bug\s+found\b",
        r"\bbehavior\s+is\s+correct\b",
    ],
    "MAX_CYCLES_REACHED": [
        r"\bmax(imum)?\s+(cycles?|iterations?|attempts?)\s+reached\b",
        r"\breached\s+(the\s+)?max(imum)?\s+(cycles?|iterations?)\b",
    ],
    "CONTINUE_CYCLE": [
        r"\btests?\s+(still\s+)?(are\s+)?failing\b",
        r"\bcontinue\s+(the\s+)?(cycle|iteration|loop)\b",
        r"\bmore\s+(work|iterations?)\s+(is\s+)?needed\b",
    ],
    "BUG_CONFIRMED": [
        r"\bbug\s+(is\s+)?confirmed\b",
        r"\bissue\s+(is\s+)?reproduced\b",
    ],
}

# ---------------------------------------------------------------------------
# Progress tracking
# ---------------------------------------------------------------------------
_AGENTIC_PROGRESS: Dict[str, Any] = {}


def set_agentic_progress(
    workflow: str,
    current_step: int,
    total_steps: int,
    step_name: str,
    completed_steps: Optional[List[str]] = None,
) -> None:
    global _AGENTIC_PROGRESS
    _AGENTIC_PROGRESS = {
        "workflow": workflow,
        "current_step": current_step,
        "total_steps": total_steps,
        "step_name": step_name,
        "completed_steps": list(completed_steps or []),
        "timestamp": datetime.utcnow().isoformat(),
    }


def clear_agentic_progress() -> None:
    global _AGENTIC_PROGRESS
    _AGENTIC_PROGRESS = {}


def get_and_clear_agentic_interrupt_context() -> Optional[Dict]:
    global _AGENTIC_PROGRESS
    if not _AGENTIC_PROGRESS:
        return None
    ctx = dict(_AGENTIC_PROGRESS)
    _AGENTIC_PROGRESS = {}
    return ctx


# ---------------------------------------------------------------------------
# Template substitution
# ---------------------------------------------------------------------------
def substitute_template_variables(template: str, variables: Dict[str, Any]) -> str:
    """Safe substitution that handles curly braces in template content."""
    if not isinstance(template, str):
        return str(template)
    result = template
    for key, value in (variables or {}).items():
        for placeholder in (f"{{{key}}}", f"{{{{{key}}}}}"):
            result = result.replace(placeholder, str(value))
    return result


# ---------------------------------------------------------------------------
# Provider preference & config
# ---------------------------------------------------------------------------
def get_agent_provider_preference() -> List[str]:
    raw = os.environ.get("PDD_AGENTIC_PROVIDER", "").strip()
    if not raw:
        return list(_DEFAULT_PROVIDER_PREFERENCE)
    items = [p.strip().lower() for p in raw.split(",") if p.strip()]
    valid = {"anthropic", "google", "openai", "opencode"}
    filtered = [p for p in items if p in valid]
    return filtered or list(_DEFAULT_PROVIDER_PREFERENCE)


def _load_agentic_config() -> Dict:
    """Load .pddrc agentic configuration if present."""
    config: Dict[str, Any] = {}
    candidates = [Path.cwd() / ".pddrc", Path.home() / ".pddrc"]
    for path in candidates:
        if not path.exists():
            continue
        try:
            try:
                import yaml  # type: ignore
                with open(path, "r", encoding="utf-8") as f:
                    data = yaml.safe_load(f) or {}
            except ImportError:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
            agentic = data.get("agentic") if isinstance(data, dict) else None
            if isinstance(agentic, dict):
                config.update(agentic)
                break
        except Exception:
            continue
    return config


# ---------------------------------------------------------------------------
# CLI discovery
# ---------------------------------------------------------------------------
def _expand_nvm_paths() -> List[str]:
    paths: List[str] = []
    nvm_glob = str(Path.home() / ".nvm" / "versions" / "node" / "*" / "bin")
    try:
        paths.extend(glob.glob(nvm_glob))
    except Exception:
        pass
    return paths


def _find_cli_binary(name: str, config: Optional[Dict] = None) -> Optional[str]:
    """Find a CLI binary by name."""
    cfg = config if config is not None else _load_agentic_config()
    override_key = f"{name}_path"
    override = cfg.get(override_key) if isinstance(cfg, dict) else None
    if override:
        override_path = Path(os.path.expanduser(str(override)))
        if override_path.exists() and os.access(override_path, os.X_OK):
            return str(override_path)

    found = shutil.which(name)
    if found:
        return found

    search_paths = list(_COMMON_CLI_PATHS) + _expand_nvm_paths()
    for base in search_paths:
        candidate = Path(base) / name
        if candidate.exists() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def _get_cli_diagnostic_info(name: str) -> str:
    """Return diagnostic info about a CLI for error messages."""
    found = _find_cli_binary(name)
    if found:
        return f"{name} found at {found}"
    return f"{name} not found in PATH or common locations"


# ---------------------------------------------------------------------------
# Availability checks
# ---------------------------------------------------------------------------
def _has_gemini_oauth() -> bool:
    return _GEMINI_OAUTH_PATH.exists()


def _has_gemini_oauth_credentials() -> bool:
    return _has_gemini_oauth()


def _has_opencode_auth_file() -> bool:
    return _OPENCODE_AUTH_PATH.exists()


def _is_anthropic_available() -> bool:
    return _find_cli_binary("claude") is not None


def _is_google_available() -> bool:
    if _find_cli_binary("gemini") is None:
        return False
    if os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY"):
        return True
    if os.environ.get("GOOGLE_GENAI_USE_VERTEXAI") or os.environ.get("GOOGLE_CLOUD_PROJECT"):
        return True
    if _has_gemini_oauth_credentials():
        return True
    return False


def _is_openai_available() -> bool:
    if _find_cli_binary("codex") is None:
        return False
    if os.environ.get("OPENAI_API_KEY"):
        return True
    if os.environ.get("PDD_CODEX_AUTH_AVAILABLE"):
        return True
    return False


def _is_opencode_available() -> bool:
    if _find_cli_binary("opencode") is None:
        return False
    keys = [
        "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GEMINI_API_KEY",
        "GOOGLE_API_KEY", "OPENROUTER_API_KEY", "GITHUB_TOKEN", "GROQ_API_KEY",
    ]
    if any(os.environ.get(k) for k in keys):
        return True
    return _has_opencode_auth_file()


def get_available_agents() -> List[str]:
    avail: List[str] = []
    if _is_anthropic_available():
        avail.append("anthropic")
    if _is_google_available():
        avail.append("google")
    if _is_openai_available():
        avail.append("openai")
    if _is_opencode_available():
        avail.append("opencode")
    return avail


# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
def _session_log_path(cwd: Optional[Union[str, Path]] = None) -> Path:
    global _SESSION_LOG_PATH, _SESSION_LOG_BASE_CWD, _AGENTIC_SESSION_ID

    base_cwd = Path(cwd).resolve() if cwd is not None else Path.cwd().resolve()
    if _SESSION_LOG_PATH is not None and _SESSION_LOG_BASE_CWD == base_cwd:
        return _SESSION_LOG_PATH

    _AGENTIC_SESSION_ID = datetime.now().strftime("%Y%m%d_%H%M%S")
    _SESSION_LOG_BASE_CWD = base_cwd
    _SESSION_LOG_PATH = base_cwd / ".pdd" / "agentic-logs" / f"session_{_AGENTIC_SESSION_ID}.jsonl"
    _SESSION_LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    return _SESSION_LOG_PATH


def _log_agentic_interaction(
    provider: Union[str, Dict[str, Any]],
    instruction: str = "",
    output: str = "",
    success: bool = False,
    cost: float = 0.0,
    duration: float = 0.0,
    *,
    verbose: bool = False,
    error: Optional[str] = None,
    extra: Optional[Dict] = None,
) -> None:
    """Log agentic interaction. Always log failures; gate successes on verbose."""
    cwd: Optional[Union[str, Path]] = None
    if isinstance(provider, dict):
        entry_data = dict(provider)
        success = bool(entry_data.get("success", success))
        if success and not verbose:
            return
        cwd = entry_data.get("cwd")
        entry_data.setdefault("timestamp", datetime.utcnow().isoformat())
        try:
            path = _session_log_path(cwd)
            with open(path, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry_data) + "\n")
        except Exception:
            pass
        return

    if success and not verbose:
        return
    try:
        cwd = extra.get("cwd") if extra else None
        path = _session_log_path(cwd)
        entry = {
            "timestamp": datetime.utcnow().isoformat(),
            "provider": provider,
            "success": success,
            "cost": cost,
            "duration_s": duration,
            "instruction_len": len(instruction),
            "output_len": len(output),
            "output_tail": output[-2000:] if output else "",
            "error": error,
        }
        if extra:
            entry.update(extra)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
    except Exception:
        pass


def _auth_env_keys_present() -> List[str]:
    keys = sorted(
        k for k, v in os.environ.items()
        if v and ("TOKEN" in k.upper() or "API_KEY" in k.upper())
    )
    return keys


def _log_blank_provider_diagnostic(
    provider: str,
    cwd: str,
    instruction: str,
    stderr_tail: str,
) -> None:
    keys = _auth_env_keys_present()
    console.print(
        f"[yellow]Warning: {provider} returned blank stdout (exit 0). "
        f"prompt_size={len(instruction)} cwd={cwd} "
        f"auth_env_keys={keys} stderr_tail={stderr_tail[-500:]!r}[/yellow]"
    )


# ---------------------------------------------------------------------------
# Subprocess execution
# ---------------------------------------------------------------------------
def _sanitized_env(cwd: Optional[Union[str, Path]] = None) -> Dict[str, str]:
    env = dict(os.environ)
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    if cwd is not None:
        env["GIT_WORK_TREE"] = str(Path(cwd))
    env.pop("PDD_OUTPUT_COST_PATH", None)
    return env


def _subprocess_run(
    argv: List[str],
    cwd: Optional[Union[str, Path]] = None,
    *,
    timeout: Optional[float] = None,
    input: Optional[str] = None,
    stdin_data: Optional[str] = None,
    env: Optional[Dict[str, str]] = None,
    capture_output: bool = True,
    text: bool = True,
    start_new_session: bool = True,
    **kwargs: Any,
) -> subprocess.CompletedProcess[str]:
    """Run a subprocess with process-group kill on timeout."""
    stdin_payload = input if input is not None else stdin_data
    effective_env = _sanitized_env(cwd)
    if env:
        effective_env.update(env)
        effective_env["TERM"] = "dumb"
        effective_env["NO_COLOR"] = "1"
        effective_env["CI"] = "1"
        effective_env.pop("PDD_OUTPUT_COST_PATH", None)

    proc = subprocess.Popen(
        argv,
        cwd=str(cwd) if cwd is not None else None,
        env=effective_env,
        stdin=subprocess.PIPE if stdin_payload is not None else kwargs.get("stdin", subprocess.DEVNULL),
        stdout=subprocess.PIPE if capture_output else kwargs.get("stdout"),
        stderr=subprocess.PIPE if capture_output else kwargs.get("stderr"),
        text=text,
        start_new_session=start_new_session,
    )
    try:
        stdout, stderr = proc.communicate(input=stdin_payload, timeout=timeout)
        return subprocess.CompletedProcess(
            args=argv,
            returncode=proc.returncode,
            stdout=stdout or "",
            stderr=stderr or "",
        )
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass
        try:
            stdout, stderr = proc.communicate(timeout=5)
        except Exception:
            stdout, stderr = "", ""
        exc.output = stdout
        exc.stderr = stderr
        raise
    except Exception as e:
        try:
            proc.kill()
        except Exception:
            pass
        raise RuntimeError(str(e)) from e


# ---------------------------------------------------------------------------
# Cost parsing helpers
# ---------------------------------------------------------------------------
def _estimate_cost_from_tokens(input_tokens: int, output_tokens: int, pricing: Pricing) -> float:
    return (input_tokens / 1_000_000) * pricing.input_per_million + \
           (output_tokens / 1_000_000) * pricing.output_per_million


def _usage_int(data: Dict[str, Any], *keys: str) -> int:
    for key in keys:
        value: Any = data
        for part in key.split("."):
            if not isinstance(value, dict):
                value = None
                break
            value = value.get(part)
        if value is not None:
            try:
                return int(value)
            except (TypeError, ValueError):
                continue
    return 0


def _select_anthropic_pricing(model: str) -> Pricing:
    m = (model or "").lower()
    if "opus" in m:
        return ANTHROPIC_PRICING["opus"]
    if "haiku" in m:
        return ANTHROPIC_PRICING["haiku"]
    return ANTHROPIC_PRICING["sonnet"]


def _select_gemini_pricing(model: str) -> Pricing:
    m = (model or "").lower()
    if "pro" in m:
        return GEMINI_PRICING["pro"]
    return GEMINI_PRICING["flash"]


def _calculate_anthropic_usage_cost(model_name: str, usage: Dict[str, Any], root_usage: Optional[Dict[str, Any]] = None) -> float:
    pricing = _select_anthropic_pricing(model_name)
    root_usage = root_usage or {}
    input_t = _usage_int(usage, "inputTokens", "input_tokens") or _usage_int(root_usage, "input_tokens")
    output_t = _usage_int(usage, "outputTokens", "output_tokens") or _usage_int(root_usage, "output_tokens")
    cache_read = _usage_int(
        usage,
        "cacheReadInputTokens",
        "cache_read_input_tokens",
        "cache_read_tokens",
    ) or _usage_int(root_usage, "cache_read_input_tokens", "cache_read_tokens")
    cache_write = _usage_int(
        usage,
        "cacheCreationInputTokens",
        "cache_creation_input_tokens",
        "cache_write_tokens",
    ) or _usage_int(root_usage, "cache_creation_input_tokens", "cache_write_tokens")
    new_input = max(0, input_t - cache_read - cache_write)
    return (
        _estimate_cost_from_tokens(new_input, output_t, pricing)
        + (cache_read / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
        + (cache_write / 1_000_000) * pricing.input_per_million * 1.25
    )


def _calculate_anthropic_cost(data: Dict[str, Any]) -> float:
    total_cost = data.get("total_cost_usd")
    try:
        if total_cost is not None and float(total_cost) > 0:
            return float(total_cost)
    except (TypeError, ValueError):
        pass

    model_usage = data.get("modelUsage")
    if isinstance(model_usage, dict) and model_usage:
        reported = 0.0
        saw_reported = False
        for usage in model_usage.values():
            if not isinstance(usage, dict):
                continue
            for key in ("costUSD", "cost_usd", "cost"):
                if key in usage:
                    try:
                        reported += float(usage[key])
                        saw_reported = True
                    except (TypeError, ValueError):
                        pass
        if saw_reported and reported > 0:
            return reported

        root_usage = data.get("usage") if isinstance(data.get("usage"), dict) else {}
        return sum(
            _calculate_anthropic_usage_cost(str(model_name), usage, root_usage)
            for model_name, usage in model_usage.items()
            if isinstance(usage, dict)
        )

    usage = data.get("usage")
    if isinstance(usage, dict):
        model_name = str(data.get("model") or os.environ.get("CLAUDE_MODEL") or "sonnet")
        return _calculate_anthropic_usage_cost(model_name, usage)
    return 0.0


def _calculate_gemini_cost(stats: Dict[str, Any]) -> float:
    models = stats.get("models", {}) if isinstance(stats, dict) else {}
    if not isinstance(models, dict):
        return 0.0
    cost = 0.0
    for model_name, usage in models.items():
        if not isinstance(usage, dict):
            continue
        for explicit_key in ("cost", "costUSD", "cost_usd"):
            if explicit_key in usage:
                try:
                    cost += float(usage[explicit_key])
                    break
                except (TypeError, ValueError):
                    pass
        else:
            explicit_key = ""
        if explicit_key:
            continue
        pricing = _select_gemini_pricing(str(model_name))
        input_t = _usage_int(
            usage,
            "inputTokens",
            "input_tokens",
            "promptTokens",
            "prompt_tokens",
            "prompt_token_count",
            "tokens.prompt",
            "tokens.input",
        )
        output_t = _usage_int(
            usage,
            "outputTokens",
            "output_tokens",
            "completionTokens",
            "completion_tokens",
            "candidates_token_count",
            "tokens.candidates",
            "tokens.output",
        )
        cached = _usage_int(usage, "cachedTokens", "cached_token_count", "tokens.cached")
        new_input = max(0, input_t - cached)
        cost += _estimate_cost_from_tokens(new_input, output_t, pricing)
        cost += (cached / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    return cost


def _calculate_codex_cost(usage: Dict[str, Any]) -> float:
    input_t = _usage_int(usage, "input_tokens", "prompt_tokens", "input")
    output_t = _usage_int(usage, "output_tokens", "completion_tokens", "output")
    cached = _usage_int(
        usage,
        "cached_input_tokens",
        "cached_tokens",
        "cached",
        "input_tokens_details.cached_tokens",
    )
    new_input = max(0, input_t - cached)
    return (
        _estimate_cost_from_tokens(new_input, output_t, CODEX_PRICING)
        + (cached / 1_000_000) * CODEX_PRICING.input_per_million * CODEX_PRICING.cached_input_multiplier
    )


# ---------------------------------------------------------------------------
# OpenCode model resolution
# ---------------------------------------------------------------------------
_OPENCODE_MODEL_PREFIX_MAP = {
    "github_copilot/": "github-copilot/",
}

_OPENCODE_PROVIDER_PREFIX_MAP = {
    "anthropic": "anthropic",
    "openai": "openai",
    "google": "google",
    "google vertex ai": "google",
    "gemini": "google",
    "openrouter": "openrouter",
    "github copilot": "github-copilot",
    "github_copilot": "github-copilot",
    "groq": "groq",
}


def _opencode_provider_for_row(row: Dict[str, str]) -> str:
    """Map a CSV row's provider column to an OpenCode provider prefix."""
    provider = (row.get("provider") or "").strip().lower()
    return _OPENCODE_PROVIDER_PREFIX_MAP.get(provider, provider)


def _configured_opencode_providers() -> Optional[set]:
    """Return the OpenCode provider prefixes that have credentials configured.

    Maps environment variables to OpenCode provider IDs. Returns ``None`` when
    no provider can be inferred (e.g. only an opaque ``auth.json`` is present),
    signalling callers to skip provider filtering and fall back to the entire
    catalog.
    """
    providers: set = set()
    if os.environ.get("OPENAI_API_KEY"):
        providers.add("openai")
    if os.environ.get("ANTHROPIC_API_KEY"):
        providers.add("anthropic")
    if os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY"):
        providers.add("google")
    if os.environ.get("OPENROUTER_API_KEY"):
        providers.add("openrouter")
    if os.environ.get("GITHUB_TOKEN"):
        providers.add("github-copilot")
    if os.environ.get("GROQ_API_KEY"):
        providers.add("groq")
    if providers:
        return providers
    if _has_opencode_auth_file():
        try:
            data = json.loads(_OPENCODE_AUTH_PATH.read_text(encoding="utf-8"))
        except Exception:
            return None
        if isinstance(data, dict):
            for key in data:
                if isinstance(key, str) and key.strip():
                    providers.add(key.strip().replace("_", "-").lower())
        return providers or None
    return None


def _translate_to_opencode_model(model_id: str) -> str:
    for src, dst in _OPENCODE_MODEL_PREFIX_MAP.items():
        if model_id.startswith(src):
            return dst + model_id[len(src):]
    return model_id


def _resolve_model_csv_path() -> Optional[Path]:
    csv_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv",
    ]
    for csv_path in csv_paths:
        if csv_path.is_file():
            return csv_path
    return None


def _load_model_data(path: Optional[Union[str, Path]] = None) -> Optional[List[Dict[str, str]]]:
    csv_path = Path(path) if path is not None else _resolve_model_csv_path()
    if csv_path is None or not csv_path.exists():
        return None
    try:
        with open(csv_path, "r", encoding="utf-8") as f:
            return list(csv.DictReader(f))
    except Exception:
        return None


def _safe_float(value: Any, default: float = 0.0) -> float:
    try:
        if value in (None, ""):
            return default
        return float(value)
    except (TypeError, ValueError):
        return default


def _row_average_cost(row: Dict[str, str]) -> float:
    return (_safe_float(row.get("input")) + _safe_float(row.get("output"))) / 2.0


def _row_to_opencode_model(row: Dict[str, str]) -> Optional[str]:
    model = (row.get("model") or row.get("name") or "").strip()
    if not model:
        return None
    translated = _translate_to_opencode_model(model)
    provider_prefix = _opencode_provider_for_row(row)
    if provider_prefix:
        # Avoid double-prefixing when the model id is already qualified for
        # this provider (e.g. ``github_copilot/openai/gpt-5`` was translated
        # to ``github-copilot/openai/gpt-5``).
        if translated == provider_prefix or translated.startswith(provider_prefix + "/"):
            return translated
        return f"{provider_prefix}/{translated}"
    # No provider context available — fall back to the translated id as-is.
    return translated


def _select_opencode_model_from_rows(
    rows: List[Dict[str, str]],
    strength: float,
    allowed_providers: Optional[set] = None,
) -> Optional[str]:
    candidates = [row for row in rows if (row.get("model") or row.get("name"))]
    if not candidates:
        return None
    if allowed_providers is not None:
        candidates = [row for row in candidates if _opencode_provider_for_row(row) in allowed_providers]
        if not candidates:
            return None

    base_name = os.environ.get("PDD_MODEL_DEFAULT", "").strip()
    base_row = next((row for row in candidates if row.get("model") == base_name), None) if base_name else None
    if base_row is None:
        base_row = candidates[0]

    if strength == 0.5:
        return _row_to_opencode_model(base_row)

    if strength < 0.5:
        base_cost = _row_average_cost(base_row)
        cheapest_cost = min(_row_average_cost(row) for row in candidates)
        target_cost = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost)
        selected = min(candidates, key=lambda row: abs(_row_average_cost(row) - target_cost))
        return _row_to_opencode_model(selected)

    elo_rows = [row for row in candidates if _safe_float(row.get("coding_arena_elo"), -1.0) >= 0]
    if not elo_rows:
        return _row_to_opencode_model(base_row)
    base_elo = _safe_float(base_row.get("coding_arena_elo"), _safe_float(elo_rows[0].get("coding_arena_elo")))
    highest_elo = max(_safe_float(row.get("coding_arena_elo")) for row in elo_rows)
    target_elo = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo)
    selected = min(elo_rows, key=lambda row: abs(_safe_float(row.get("coding_arena_elo")) - target_elo))
    return _row_to_opencode_model(selected)


def _resolve_opencode_model() -> Optional[str]:
    explicit = os.environ.get("OPENCODE_MODEL", "").strip()
    if explicit:
        return _translate_to_opencode_model(explicit)

    try:
        from . import DEFAULT_STRENGTH  # type: ignore
    except Exception:
        DEFAULT_STRENGTH = 0.5  # type: ignore

    rows = _load_model_data() or []
    if not rows:
        return None
    allowed = _configured_opencode_providers()
    return _select_opencode_model_from_rows(rows, float(DEFAULT_STRENGTH), allowed_providers=allowed)


def _opencode_csv_pricing(model_id: Optional[str]) -> Optional[Pricing]:
    """Return CSV-derived ``Pricing`` for an OpenCode model id, if available.

    OpenCode model ids are ``<provider>/<model>`` (e.g. ``openai/gpt-5``); for some
    providers like ``github-copilot`` or ``openrouter`` the model portion itself
    contains a slash (``github-copilot/openai/gpt-5``). To avoid billing the wrong
    provider when multiple CSV rows share the same model tail (e.g. both
    ``OpenRouter`` and ``github_copilot`` carry an ``openai/gpt-5`` row), prefer
    matching the row whose translated provider matches the model id's leading
    segment. Fall back to a tail-only match when no provider-qualified row exists.
    """
    if not model_id:
        return None
    rows = _load_model_data() or []
    if not rows:
        return None

    def _row_pricing(row: Dict[str, str]) -> Pricing:
        return Pricing(
            input_per_million=_safe_float(row.get("input")),
            output_per_million=_safe_float(row.get("output")),
            cached_input_multiplier=0.5,
        )

    # Provider-qualified match: split the leading provider segment and require
    # both the translated provider and remaining model id to match.
    if "/" in model_id:
        provider_segment, model_remainder = model_id.split("/", 1)
        for row in rows:
            row_model = (row.get("model") or row.get("name") or "").strip()
            if not row_model:
                continue
            if (
                _opencode_provider_for_row(row) == provider_segment
                and row_model == model_remainder
            ):
                return _row_pricing(row)

    # Fallback: match by full id or trailing model when no provider-qualified row
    # exists (e.g. legacy ids without an OpenCode provider prefix).
    candidates = [model_id]
    if "/" in model_id:
        candidates.append(model_id.split("/", 1)[1])
    for candidate in candidates:
        for row in rows:
            row_model = (row.get("model") or row.get("name") or "").strip()
            if not row_model:
                continue
            if row_model == candidate:
                return _row_pricing(row)
    return None


# ---------------------------------------------------------------------------
# Reasoning effort
# ---------------------------------------------------------------------------
_VALID_REASONING_EFFORTS = {"low", "medium", "high"}
_VALID_CODEX_EFFORTS = {"low", "medium", "high", "xhigh"}


def _resolve_reasoning_effort(reasoning_time: Optional[float] = None) -> Optional[str]:
    """Resolve generic reasoning effort from explicit time or env var."""
    if reasoning_time is not None:
        if reasoning_time > 0.7:
            return "high"
        if reasoning_time > 0.3:
            return "medium"
        return "low"
    env_val = os.environ.get("PDD_REASONING_EFFORT", "").strip().lower()
    if env_val in _VALID_REASONING_EFFORTS:
        return env_val
    return None


def _resolve_codex_reasoning_effort(reasoning_time: Optional[float] = None) -> Optional[str]:
    if reasoning_time is not None:
        return _resolve_reasoning_effort(reasoning_time)
    env_val = os.environ.get("CODEX_REASONING_EFFORT", "").strip().lower()
    if env_val in _VALID_CODEX_EFFORTS:
        return env_val
    return _resolve_reasoning_effort(reasoning_time)


# ---------------------------------------------------------------------------
# Codex auth failure detection
# ---------------------------------------------------------------------------
_CODEX_AUTH_PATTERNS = [
    "access token could not be refreshed",
    "please sign in again",
    "chatgpt.com/backend-api/codex",
    "codex/responses",
]


def _codex_auth_failure_message(error_detail: str) -> Optional[str]:
    """Detect Codex stale ChatGPT login failure and return actionable message."""
    if not error_detail:
        return None
    lower = error_detail.lower()
    has_auth_pattern = any(p in lower for p in _CODEX_AUTH_PATTERNS)
    has_unauth = ("401" in lower) or ("unauthorized" in lower) or ("sign in" in lower) or ("login" in lower)
    if has_auth_pattern and has_unauth:
        return (
            "Codex CLI authentication has expired. Please run:\n"
            "  codex login           (ChatGPT sign-in)\n"
            "  codex login --device-auth  (alternative device flow)\n"
            "  codex login --with-api-key (API-key auth)"
        )
    return None


# ---------------------------------------------------------------------------
# Permanent error classification
# ---------------------------------------------------------------------------
_PERMANENT_ERROR_PATTERNS = [
    "authentication", "unauthorized", "401", "403",
    "not logged in", "please run /login", "please sign in again",
    "invalid parameter", "invalid_request",
    "model not found", "model_not_found",
    "unsupported", "quota exhausted", "daily quota",
    "terminalquotaerror",
    "permission denied",
    "no provider for model",
    "provider not configured",
    "invalid model id",
    "auth.json",
]


def _is_permanent_error(error_msg: str) -> bool:
    if not error_msg:
        return False
    lower = error_msg.lower()
    return any(p in lower for p in _PERMANENT_ERROR_PATTERNS)


# ---------------------------------------------------------------------------
# False positive detection
# ---------------------------------------------------------------------------
def _is_false_positive(output: str, cost: float) -> bool:
    """Detect false-positive 'success' responses."""
    if not output or not output.strip():
        return True
    stripped = output.strip()
    if cost == 0 and len(stripped) < MIN_VALID_OUTPUT_LENGTH:
        return True
    if cost > 0 and stripped.startswith("Error:"):
        newline_count = stripped.count("\n")
        if newline_count < MAX_ERROR_RESPONSE_NEWLINES and len(stripped) < 4000:
            return True
    return False


# ---------------------------------------------------------------------------
# Control token detection
# ---------------------------------------------------------------------------
def detect_control_token(
    output: str,
    token: str,
    tail_lines: int = _SEMANTIC_TAIL_LINES,
) -> Optional[TokenMatch]:
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
    tail = "\n".join(lines[-tail_lines:])
    for pat in patterns:
        try:
            if re.search(pat, tail, re.IGNORECASE):
                return TokenMatch(tier="semantic", token=token, pattern=pat)
        except re.error:
            continue
    return None


def classify_step_output(
    output: str,
    tokens: List[str],
    quiet: bool = False,
) -> Optional[str]:
    """Tier-4 LLM classification fallback."""
    if not output or not tokens:
        return None
    for token in tokens:
        if detect_control_token(output, token):
            return token
    try:
        from .llm_invoke import llm_invoke  # type: ignore
        from pydantic import BaseModel

        class TokenClassification(BaseModel):
            token: Optional[str]
            confidence: float

        token_list = ", ".join(tokens)
        prompt = (
            "Classify the following step output by selecting which control "
            f"token best matches. Tokens: {token_list}\n"
            "If none match, return null for token. Output:\n{{output}}"
        )
        response = llm_invoke(
            prompt=prompt,
            input_json={"output": output[-4000:]},
            strength=0.3,
            temperature=0.0,
            output_pydantic=TokenClassification,
        )
        result = response.get("result")
        if result and getattr(result, "token", None) and result.token in tokens:
            return result.token
    except Exception as e:
        if not quiet:
            console.print(f"[yellow]LLM classification failed: {e}[/yellow]")
    return None


# ---------------------------------------------------------------------------
# Provider JSON parsing
# ---------------------------------------------------------------------------
def _coerce_json_payload(payload: Union[str, Dict[str, Any], Any]) -> Union[str, Dict[str, Any], Any]:
    if isinstance(payload, str):
        stripped = payload.strip()
        if not stripped:
            return ""
        try:
            return json.loads(stripped)
        except Exception:
            return payload
    return payload


def _parse_anthropic_json(payload: Union[str, Dict[str, Any]]) -> Tuple[bool, str, float]:
    data = _coerce_json_payload(payload)
    if not isinstance(data, dict):
        return True, str(payload), 0.0
    if isinstance(data, dict) and data.get("is_error"):
        text = data.get("result") or data.get("response") or "Anthropic error"
        try:
            cost = float(data.get("total_cost_usd") or 0.0)
        except (TypeError, ValueError):
            cost = 0.0
        return False, str(text), cost
    text = data.get("result") or data.get("response") or ""
    return True, str(text), _calculate_anthropic_cost(data)


def _parse_google_json(payload: Union[str, Dict[str, Any]]) -> Tuple[bool, str, float]:
    data = _coerce_json_payload(payload)
    if not isinstance(data, dict):
        return True, str(payload), 0.0
    text = data.get("result") or data.get("response") or data.get("output") or ""
    stats = data.get("stats", {})
    return True, str(text), _calculate_gemini_cost(stats if isinstance(stats, dict) else {})


def _extract_openai_text_from_item(item: Dict[str, Any]) -> str:
    if item.get("type") != "agent_message":
        return ""
    text = item.get("text")
    if text:
        return str(text)
    content = item.get("content")
    if isinstance(content, list):
        parts: List[str] = []
        for part in content:
            if isinstance(part, dict) and part.get("type") in {"output_text", "text"}:
                part_text = part.get("text")
                if part_text:
                    parts.append(str(part_text))
        return "\n".join(parts)
    if isinstance(content, str):
        return content
    return ""


def _parse_openai_json(payload: Union[str, Dict[str, Any]]) -> Tuple[bool, str, float]:
    """Parse Codex/OpenAI output. Handles both JSON and NDJSON."""
    text_parts: List[str] = []
    cost = 0.0
    parsed_any = False

    # Try single JSON first
    if isinstance(payload, dict):
        data = payload
        parsed_any = True
        item = data.get("item")
        if isinstance(item, dict):
            item_text = _extract_openai_text_from_item(item)
            if item_text:
                text_parts.append(item_text)
        if not text_parts:
            text_parts.append(str(data.get("result") or data.get("response") or data.get("output") or ""))
        usage = data.get("usage", {})
        if isinstance(usage, dict):
            cost += _calculate_codex_cost(usage)
    else:
        stdout = str(payload)
        stripped = stdout.strip()
        if stripped.startswith("{") and stripped.endswith("}"):
            try:
                data = json.loads(stripped)
                parsed_any = True
                if isinstance(data, dict):
                    item = data.get("item")
                    if isinstance(item, dict):
                        item_text = _extract_openai_text_from_item(item)
                        if item_text:
                            text_parts.append(item_text)
                    if not text_parts:
                        text_parts.append(str(data.get("result") or data.get("response") or data.get("output") or ""))
                    usage = data.get("usage", {})
                    if isinstance(usage, dict):
                        cost += _calculate_codex_cost(usage)
            except Exception:
                parsed_any = False

    if not parsed_any and isinstance(payload, str):
        # NDJSON
        for line in payload.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            parsed_any = True
            if not isinstance(obj, dict):
                continue
            obj_type = obj.get("type", "")
            if obj_type in ("item.completed", "item"):
                item = obj.get("item", obj)
                if isinstance(item, dict):
                    item_text = _extract_openai_text_from_item(item)
                    if item_text:
                        text_parts.append(item_text)
            elif obj_type in ("session.end", "turn.completed"):
                usage = obj.get("usage", {})
                if isinstance(usage, dict):
                    cost += _calculate_codex_cost(usage)

    if not parsed_any:
        return True, str(payload), 0.0
    return True, "\n".join(p for p in text_parts if p), cost


def _opencode_usage_cost(model_name: str, usage: Dict[str, Any]) -> float:
    input_t = _usage_int(
        usage,
        "input_tokens",
        "prompt_tokens",
        "input",
        "inputTokens",
        "promptTokens",
        "tokens.input",
        "tokens.prompt",
    )
    output_t = _usage_int(
        usage,
        "output_tokens",
        "completion_tokens",
        "output",
        "outputTokens",
        "completionTokens",
        "tokens.output",
        "tokens.candidates",
    )
    cached = _usage_int(
        usage,
        "cached_input_tokens",
        "cached_tokens",
        "cached",
        "cacheReadInputTokens",
        "tokens.cached",
    )
    cache_write = _usage_int(usage, "cacheCreationInputTokens", "cache_write_tokens")
    model_lower = model_name.lower()
    if "claude" in model_lower or "anthropic" in model_lower:
        pricing = _select_anthropic_pricing(model_name)
        new_input = max(0, input_t - cached - cache_write)
        return (
            _estimate_cost_from_tokens(new_input, output_t, pricing)
            + (cached / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
            + (cache_write / 1_000_000) * pricing.input_per_million * 1.25
        )
    if "gemini" in model_lower or "google" in model_lower:
        pricing = _select_gemini_pricing(model_name)
        return (
            _estimate_cost_from_tokens(max(0, input_t - cached), output_t, pricing)
            + (cached / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
        )
    return _calculate_codex_cost(
        {
            "input_tokens": input_t,
            "output_tokens": output_t,
            "cached_input_tokens": cached,
        }
    )


def _event_usage_payloads(obj: Dict[str, Any]) -> List[Tuple[str, Dict[str, Any]]]:
    payloads: List[Tuple[str, Dict[str, Any]]] = []
    containers: List[Dict[str, Any]] = [obj]
    part = obj.get("part")
    if isinstance(part, dict):
        containers.append(part)
    for container in containers:
        model = str(container.get("model") or obj.get("model") or os.environ.get("OPENCODE_MODEL") or "")
        usage = container.get("usage")
        if isinstance(usage, dict):
            payloads.append((model, usage))
            continue
        tokens = container.get("tokens")
        if isinstance(tokens, dict):
            payloads.append((model, {"tokens": tokens}))
            continue
        if any(
            key in container
            for key in (
                "input_tokens",
                "output_tokens",
                "prompt_tokens",
                "completion_tokens",
                "inputTokens",
                "outputTokens",
            )
        ):
            payloads.append((model, container))
    return payloads


def _parse_opencode_jsonl(stdout: str) -> Tuple[bool, str, float, Optional[str], Dict[str, Any]]:
    """Parse OpenCode JSONL stream."""
    text_parts: List[str] = []
    cost = 0.0
    fallback_cost = 0.0
    error_msg: Optional[str] = None
    saw_text = False
    saw_step = False
    cost_reported = False

    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        for model_name, usage in _event_usage_payloads(obj):
            fallback_cost += _opencode_usage_cost(model_name, usage)
        evt = obj.get("type") or obj.get("event") or ""
        if evt == "text":
            saw_text = True
            part = obj.get("part")
            if isinstance(part, dict):
                text_parts.append(str(part.get("text") or part.get("content") or ""))
            else:
                text_parts.append(str(obj.get("text") or obj.get("content") or ""))
        elif evt == "step_finish":
            saw_step = True
            part = obj.get("part") or {}
            if isinstance(part, dict):
                if "cost" in part:
                    cost_reported = True
                try:
                    cost += float(part.get("cost") or 0.0)
                except Exception:
                    pass
            if "cost" in obj:
                cost_reported = True
                try:
                    cost += float(obj.get("cost") or 0.0)
                except Exception:
                    pass
        elif evt == "error":
            part = obj.get("part")
            if isinstance(part, dict):
                error_msg = str(part.get("message") or part.get("error") or "OpenCode error")
            else:
                error_msg = str(obj.get("message") or obj.get("error") or "OpenCode error")

    info = {"cost_reported": cost_reported}
    if error_msg:
        return False, "", cost, error_msg, info
    if not saw_text and not saw_step:
        return False, "", 0.0, None, info
    if not cost_reported:
        if fallback_cost > 0:
            cost = fallback_cost
        elif text_parts:
            output_tokens = max(1, len("".join(text_parts)) // 4)
            model_id = os.environ.get("OPENCODE_MODEL", "").strip() or _resolve_opencode_model()
            pricing = _opencode_csv_pricing(model_id) or CODEX_PRICING
            cost = _estimate_cost_from_tokens(0, output_tokens, pricing)
    return True, "".join(text_parts), cost, None, info


def _parse_provider_json(provider: str, payload: Union[str, Dict[str, Any]]) -> Tuple[bool, str, float]:
    if provider == "anthropic":
        return _parse_anthropic_json(payload)
    if provider == "google":
        return _parse_google_json(payload)
    if provider == "openai":
        return _parse_openai_json(payload)
    if provider == "opencode":
        ok, text, cost, error, _info = _parse_opencode_jsonl(str(payload))
        return ok, error or text, cost
    return True, str(payload), 0.0


# ---------------------------------------------------------------------------
# Build CLI command
# ---------------------------------------------------------------------------
def _build_anthropic_cmd(cli_path: str, instruction: str, use_playwright: bool) -> Tuple[List[str], Optional[str]]:
    if use_playwright:
        cmd = [
            cli_path, "-p", "-",
            "--allowedTools", "Bash", "Read", "Write",
            "--max-turns", "30",
            "--output-format", "json",
        ]
    else:
        cmd = [
            cli_path, "-p", "-",
            "--dangerously-skip-permissions",
            "--output-format", "json",
        ]
    model = os.environ.get("CLAUDE_MODEL")
    if model:
        cmd.extend(["--model", model])
    return cmd, instruction


def _build_google_cmd(cli_path: str, instruction: str, use_playwright: bool) -> Tuple[List[str], Optional[str]]:
    cmd = [cli_path, instruction, "--yolo", "--output-format", "json"]
    model = os.environ.get("GEMINI_MODEL")
    if model:
        cmd.extend(["--model", model])
    return cmd, None


def _build_openai_cmd(
    cli_path: str,
    instruction: str,
    cwd: str,
    use_playwright: bool,
    reasoning_time: Optional[float] = None,
) -> Tuple[List[str], Optional[str]]:
    sandbox_mode = os.environ.get("PDD_CODEX_SANDBOX", "danger-full-access")
    # Write instruction to a temp file
    fd, path = tempfile.mkstemp(suffix=".txt", prefix="codex_instr_", dir=cwd)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(instruction)
    except Exception:
        os.close(fd)
        path = ""

    cmd = [cli_path]
    effort = _resolve_codex_reasoning_effort(reasoning_time)
    if effort:
        cmd.extend(["-c", f"model_reasoning_effort={effort}"])
    cmd.extend(["exec", "--sandbox", sandbox_mode, "--json"])
    model = os.environ.get("CODEX_MODEL")
    if model:
        cmd.extend(["--model", model])
    if path:
        cmd.append(path)
    return cmd, None


def _build_opencode_cmd(cli_path: str, instruction: str, cwd: str, use_playwright: bool) -> Tuple[List[str], Optional[str]]:
    cmd = [cli_path, "run", "--dir", cwd, "--format", "json", "--dangerously-skip-permissions"]
    model = _resolve_opencode_model()
    if model:
        cmd.extend(["--model", model])
    agent = os.environ.get("OPENCODE_AGENT", "").strip()
    if agent:
        cmd.extend(["--agent", agent])
    variant = os.environ.get("OPENCODE_VARIANT", "").strip()
    if variant:
        cmd.extend(["--variant", variant])
    cmd.append(instruction)
    return cmd, None


# ---------------------------------------------------------------------------
# Run with provider
# ---------------------------------------------------------------------------
def _run_with_provider(
    provider: str,
    instruction: Optional[Union[str, Path]] = None,
    cwd: Union[str, Path] = ".",
    *,
    prompt_path: Optional[Union[str, Path]] = None,
    cli_path: Optional[str] = None,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
    use_playwright: bool = False,
    verbose: bool = False,
    reasoning_time: Optional[float] = None,
    quiet: bool = False,
) -> Tuple[bool, str, float]:
    """Run a single provider attempt. Returns (success, output_or_error, cost)."""
    cwd_str = str(cwd)
    if prompt_path is None and isinstance(instruction, Path):
        prompt_path = instruction
    if prompt_path is not None:
        instruction_text = (
            f"Read the file {Path(prompt_path)} for instructions. "
            "You have full file access to explore and modify files as needed."
        )
    else:
        instruction_text = str(instruction or "")

    if cli_path is None:
        cli_names = _CLI_NAMES.get(provider, [])
        for name in cli_names:
            cli_path = _find_cli_binary(name)
            if cli_path:
                break
    if not cli_path:
        return False, f"{provider} CLI not found", 0.0

    stdin_data: Optional[str] = None
    if provider == "anthropic":
        cmd, stdin_data = _build_anthropic_cmd(cli_path, instruction_text, use_playwright)
        if not quiet and _resolve_reasoning_effort(reasoning_time):
            console.print("[dim]Anthropic CLI does not support reasoning_effort; ignoring.[/dim]")
    elif provider == "google":
        cmd, stdin_data = _build_google_cmd(cli_path, instruction_text, use_playwright)
        if not quiet and _resolve_reasoning_effort(reasoning_time):
            console.print("[dim]Gemini CLI does not support reasoning_effort; ignoring.[/dim]")
    elif provider == "openai":
        cmd, stdin_data = _build_openai_cmd(cli_path, instruction_text, cwd_str, use_playwright, reasoning_time)
    elif provider == "opencode":
        cmd, stdin_data = _build_opencode_cmd(cli_path, instruction_text, cwd_str, use_playwright)
    else:
        return False, f"Unknown provider {provider}", 0.0

    start = time.time()
    try:
        completed = _subprocess_run(
            cmd,
            cwd=cwd_str,
            timeout=timeout,
            input=stdin_data,
            start_new_session=True,
        )
    except subprocess.TimeoutExpired as exc:
        duration = time.time() - start
        stdout = str(exc.output or "")
        stderr = str(exc.stderr or "")
        error_text = f"Timeout expired after {timeout}s"
        _log_agentic_interaction(
            provider, instruction_text, stdout, False, 0.0, duration,
            verbose=verbose, error=error_text, extra={"cwd": cwd_str},
        )
        return False, error_text if not stderr else f"{error_text}: {stderr[:MAX_ERROR_SNIPPET_LENGTH]}", 0.0
    if isinstance(completed, tuple):
        rc, stdout, stderr = completed
    else:
        rc = int(getattr(completed, "returncode", 0))
        stdout = str(getattr(completed, "stdout", "") or "")
        stderr = str(getattr(completed, "stderr", "") or "")
    duration = time.time() - start

    if rc != 0:
        combined = (stderr or "") + "\n" + (stdout or "")
        if provider == "openai":
            auth_msg = _codex_auth_failure_message(combined)
            if auth_msg:
                _log_agentic_interaction(
                    provider, instruction_text, stdout, False, 0.0, duration,
                    verbose=verbose, error=auth_msg, extra={"cwd": cwd_str},
                )
                return False, auth_msg, 0.0
        err_snippet = (stderr or stdout or f"Exit code {rc}")[:MAX_ERROR_SNIPPET_LENGTH]
        _log_agentic_interaction(
            provider, instruction_text, stdout, False, 0.0, duration,
            verbose=verbose, error=err_snippet, extra={"cwd": cwd_str},
        )
        return False, f"Exit code {rc}: {err_snippet}", 0.0

    # rc == 0 but possibly empty
    if not stdout.strip():
        _log_blank_provider_diagnostic(provider, cwd_str, instruction_text, stderr or "")
        _log_agentic_interaction(
            provider, instruction_text, stdout, False, 0.0, duration,
            verbose=verbose, error="empty stdout", extra={"cwd": cwd_str},
        )
        return False, "Empty provider response", 0.0

    ok, text, cost = _parse_provider_json(provider, stdout)
    if provider == "opencode" and not ok and _is_permanent_error(text):
        text = (
            f"OpenCode configuration error: {text}. "
            "Check OPENCODE_MODEL and run `opencode auth login` or `opencode models`."
        )

    if not ok:
        _log_agentic_interaction(
            provider, instruction_text, text, False, cost, duration,
            verbose=verbose, error=text[:500], extra={"cwd": cwd_str},
        )
        return False, text, cost

    _log_agentic_interaction(
        provider, instruction_text, text, True, cost, duration,
        verbose=verbose, extra={"cwd": cwd_str},
    )
    return True, text, cost


# ---------------------------------------------------------------------------
# Job deadline
# ---------------------------------------------------------------------------
def get_job_deadline() -> Optional[float]:
    raw = os.environ.get("PDD_JOB_DEADLINE", "").strip()
    if not raw:
        return None
    try:
        return float(raw)
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------
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
    """Try providers in preference order. Returns (success, output, cost, provider)."""
    if not instruction or not str(instruction).strip():
        return False, "Empty instruction", 0.0, ""

    cwd_path = Path(cwd)
    user_feedback = os.environ.get("PDD_USER_FEEDBACK", "").strip()
    prompt_text = str(instruction)
    if user_feedback:
        prompt_text = f"{prompt_text}\n\nUser Feedback:\n{user_feedback}"

    prompt_file: Optional[Path] = None
    agent_instruction = ""
    try:
        fd, prompt_name = tempfile.mkstemp(
            suffix=".txt",
            prefix=".agentic_prompt_",
            dir=str(cwd_path),
        )
        prompt_file = Path(prompt_name)
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(prompt_text)
        agent_instruction = (
            f"Read the file {prompt_file} for instructions. "
            "You have full file access to explore and modify files as needed."
        )
    except Exception as e:
        return False, f"Failed to create agentic prompt file: {e}", 0.0, ""

    available = set(get_available_agents())
    preference = get_agent_provider_preference()
    candidates = [p for p in preference if p in available]
    if not candidates:
        msg = f"No agentic providers available. Preference: {preference}, Available: {sorted(available)}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        try:
            if prompt_file and prompt_file.exists():
                prompt_file.unlink()
        except Exception:
            pass
        return False, msg, 0.0, ""

    effective_timeout = float(timeout or DEFAULT_TIMEOUT_SECONDS)
    job_deadline = deadline if deadline is not None else get_job_deadline()
    has_external_deadline = job_deadline is not None
    if job_deadline is None:
        # Aggregate per-step deadline: 2x the step timeout
        step_deadline = time.time() + 2 * effective_timeout
    else:
        step_deadline = job_deadline

    single_provider = len(candidates) == 1
    last_error = ""
    last_output = ""
    last_cost = 0.0
    deadline_reached = False

    try:
        for provider in candidates:
            for attempt in range(1, max_retries + 1):
                now = time.time()
                remaining = step_deadline - now
                reserve = JOB_TIMEOUT_MARGIN_SECONDS if has_external_deadline else 0.0
                usable_remaining = remaining - reserve
                if usable_remaining < MIN_ATTEMPT_TIMEOUT_SECONDS:
                    if not quiet:
                        console.print(
                            f"[yellow]Skipping {provider} attempt {attempt}: "
                            f"only {usable_remaining:.1f}s remaining"
                            f"{' after reserve' if reserve else ''}[/yellow]"
                        )
                    last_error = "Deadline exceeded before provider attempt"
                    break

                attempt_timeout = min(effective_timeout, usable_remaining)

                if not quiet:
                    lbl = f" [{label}]" if label else ""
                    console.print(
                        f"[cyan]-> {provider}{lbl} attempt {attempt}/{max_retries} "
                        f"(timeout={attempt_timeout:.0f}s)[/cyan]"
                    )

                result = _run_with_provider(
                    provider, agent_instruction, cwd_path,
                    timeout=attempt_timeout,
                    use_playwright=use_playwright,
                    verbose=verbose,
                    reasoning_time=reasoning_time,
                    quiet=quiet,
                )
                if len(result) == 4:
                    success, output, cost, err = result  # type: ignore[misc]
                    err_text = str(err or "")
                else:
                    success, output, cost = result
                    err_text = "" if success else output
                last_error = err_text
                last_output = output
                last_cost = cost

                if success and not _is_false_positive(output, cost):
                    # Detect single-letter file artifacts
                    for letter in ("C", "E", "T"):
                        candidate = cwd_path / letter
                        if candidate.exists() and candidate.is_file():
                            console.print(
                                f"[red]Warning: suspicious single-letter file '{letter}' "
                                f"created by {provider} in {cwd_path}[/red]"
                            )
                    if not quiet:
                        console.print(f"[green]{provider} succeeded (cost=${cost:.4f})[/green]")
                    return True, output, cost, provider

                if time.time() >= step_deadline:
                    deadline_reached = True
                    last_error = "Deadline exceeded after provider attempt"
                    break

                if not success and err_text and _is_permanent_error(err_text):
                    if not quiet:
                        console.print(f"[red]{provider} permanent error: {err_text[:200]}[/red]")
                    break  # move to next provider

                if not success and not single_provider and (
                    not err_text or "empty provider response" in err_text.lower()
                ):
                    break

                if success and _is_false_positive(output, cost):
                    if not quiet:
                        console.print(f"[yellow]{provider} returned false-positive response[/yellow]")
                    if not single_provider:
                        break  # move to next provider
                    err_text = output or "False-positive provider response"
                    last_error = err_text

                # Retry decision
                if attempt < max_retries and (single_provider or not success):
                    backoff = retry_delay * (2 ** (attempt - 1)) + random.uniform(0, retry_delay)
                    backoff = min(backoff, MAX_RETRY_DELAY)
                    if not quiet:
                        console.print(f"[dim]Retrying after {backoff:.1f}s...[/dim]")
                    time.sleep(backoff)
                elif not single_provider:
                    break
            if deadline_reached:
                break
    finally:
        try:
            if prompt_file and prompt_file.exists():
                prompt_file.unlink()
        except Exception:
            pass

    final_msg = last_output if last_output else last_error or "All providers failed"
    return False, final_msg, last_cost, ""


def _revert_out_of_scope_changes(cwd: Union[str, Path], allowed_files: set[Path]) -> List[Path]:
    """Revert tracked and remove untracked files outside an explicit allow-list."""
    cwd_path = Path(cwd)
    allowed = {Path(p).resolve() for p in allowed_files}
    reverted: List[Path] = []
    try:
        status = subprocess.run(
            ["git", "status", "--porcelain", "-u"],
            cwd=str(cwd_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
    except Exception:
        return reverted
    if status.returncode != 0:
        return reverted

    for raw_line in (status.stdout or "").splitlines():
        if not raw_line:
            continue
        status_code = raw_line[:2]
        rel = raw_line[3:].strip()
        if " -> " in rel:
            rel = rel.split(" -> ", 1)[1].strip()
        path = (cwd_path / rel).resolve()
        if path in allowed:
            continue
        try:
            if status_code == "??":
                if path.is_file() or path.is_symlink():
                    path.unlink()
                elif path.is_dir():
                    shutil.rmtree(path)
            else:
                subprocess.run(
                    ["git", "checkout", "HEAD", "--", rel],
                    cwd=str(cwd_path),
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
            reverted.append(path)
        except Exception:
            continue
    return reverted


# ---------------------------------------------------------------------------
# GitHub state persistence
# ---------------------------------------------------------------------------
_STATE_MARKER_PREFIX = "<!-- PDD_WORKFLOW_STATE:"
_STATE_MARKER_SUFFIX = "-->"
GITHUB_STATE_MARKER_START = _STATE_MARKER_PREFIX
GITHUB_STATE_MARKER_END = _STATE_MARKER_SUFFIX


def _gh_available() -> bool:
    return shutil.which("gh") is not None


def _should_use_github_state(use_github_state: bool = True) -> bool:
    if os.environ.get("PDD_NO_GITHUB_STATE"):
        return False
    return bool(use_github_state)


def _run_gh(args: List[str], cwd: Union[str, Path], timeout: float = 60.0) -> Tuple[int, str, str]:
    try:
        completed = subprocess.run(
            ["gh"] + args,
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return int(completed.returncode), str(completed.stdout or ""), str(completed.stderr or "")
    except Exception as e:
        return 1, "", str(e)


def _state_marker(workflow: str, issue_number: Optional[int] = None) -> str:
    if issue_number is None:
        return f"{_STATE_MARKER_PREFIX}{workflow}"
    return f"{_STATE_MARKER_PREFIX}{workflow}:issue-{issue_number}"


def _serialize_state_comment(workflow: str, issue_number: Optional[int], state: Dict[str, Any]) -> str:
    payload = json.dumps(state, indent=2)
    return (
        f"{_state_marker(workflow, issue_number)}\n"
        f"{payload}\n"
        f"{_STATE_MARKER_SUFFIX}"
    )


def _format_state_comment(workflow: str, state: Dict[str, Any], issue_number: Optional[int] = None) -> str:
    return _serialize_state_comment(workflow, issue_number, state)


def _find_state_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow: str,
    cwd: Union[str, Path],
) -> Tuple[Optional[int], Optional[Dict]]:
    if not _gh_available():
        return None, None
    rc, stdout, _ = _run_gh(
        [
            "api", "--paginate",
            f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
        ],
        cwd,
    )
    if rc != 0 or not stdout.strip():
        return None, None
    marker = _state_marker(workflow)
    try:
        # --paginate may return concatenated JSON arrays; parse each
        comments: List[Dict] = []
        decoder = json.JSONDecoder()
        idx = 0
        s = stdout.strip()
        while idx < len(s):
            while idx < len(s) and s[idx] in " \t\r\n":
                idx += 1
            if idx >= len(s):
                break
            obj, end = decoder.raw_decode(s, idx)
            if isinstance(obj, list):
                comments.extend(obj)
            elif isinstance(obj, dict):
                comments.append(obj)
            idx = end
    except Exception:
        try:
            comments = json.loads(stdout)
        except Exception:
            return None, None

    markers = (_state_marker(workflow, issue_number), _state_marker(workflow))
    for c in reversed(comments):
        body = c.get("body", "")
        if any(marker in body for marker in markers):
            cid = c.get("id")
            try:
                json_match = re.search(r"```json\s*(\{.*?\})\s*```", body, re.DOTALL)
                if json_match:
                    state = json.loads(json_match.group(1))
                    return cid, state
                comment_match = re.search(
                    r"<!--\s*PDD_WORKFLOW_STATE:[^\n>]*\n(.*?)\n\s*-->",
                    body,
                    re.DOTALL,
                )
                if comment_match:
                    state = json.loads(comment_match.group(1).strip())
                    return cid, state
            except Exception:
                continue
    return None, None


def github_save_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow: str = "default",
    state: Optional[Dict[str, Any]] = None,
    cwd: Union[str, Path] = ".",
    **kwargs: Any,
) -> Optional[int]:
    workflow = str(kwargs.get("workflow_id") or kwargs.get("workflow_type") or workflow)
    state = dict(state or kwargs.get("state") or {})
    if not _gh_available():
        return None
    body = _format_state_comment(workflow, state, issue_number)
    existing_id, _ = _find_state_comment(repo_owner, repo_name, issue_number, workflow, cwd)

    if existing_id:
        rc, stdout, _ = _run_gh(
            [
                "api", "--method", "PATCH",
                f"repos/{repo_owner}/{repo_name}/issues/comments/{existing_id}",
                "-f", f"body={body}",
            ],
            cwd,
        )
        if rc == 0:
            return existing_id
        return None

    rc, stdout, _ = _run_gh(
        [
            "api", "--method", "POST",
            f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
            "-f", f"body={body}",
        ],
        cwd,
    )
    if rc != 0:
        return None
    try:
        data = json.loads(stdout)
        return data.get("id")
    except Exception:
        return None


def github_load_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow: str = "default",
    cwd: Union[str, Path] = ".",
    **kwargs: Any,
) -> Tuple[Optional[Dict], Optional[int]]:
    workflow = str(kwargs.get("workflow_id") or kwargs.get("workflow_type") or workflow)
    cid, state = _find_state_comment(repo_owner, repo_name, issue_number, workflow, cwd)
    return state, cid


def github_clear_state(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    workflow: str = "default",
    cwd: Union[str, Path] = ".",
    **kwargs: Any,
) -> bool:
    """Delete the GitHub state comment for the given workflow if present.

    Returns True when the comment is cleared (or already absent), False on error.
    """
    workflow = str(kwargs.get("workflow_id") or kwargs.get("workflow_type") or workflow)
    if not _gh_available():
        return False
    cid, _ = _find_state_comment(repo_owner, repo_name, issue_number, workflow, cwd)
    if not cid:
        return True  # already clear
    rc, _, _ = _run_gh(
        [
            "api", "--method", "DELETE",
            f"repos/{repo_owner}/{repo_name}/issues/comments/{cid}",
        ],
        cwd,
    )
    return rc == 0


def _local_state_path(
    workflow: str,
    cwd: Union[str, Path] = ".",
    issue_number: Optional[int] = None,
    state_dir: Optional[Union[str, Path]] = None,
) -> Path:
    if state_dir is not None:
        filename = f"{workflow}_state_{issue_number}.json" if issue_number is not None else f"{workflow}.json"
        return Path(state_dir) / filename
    return Path(cwd) / ".pdd" / "workflow-state" / f"{workflow}.json"


def _normalize_state_call(args: Tuple[Any, ...], kwargs: Dict[str, Any], *, op: str) -> Dict[str, Any]:
    data = dict(kwargs)
    if args:
        if op == "save" and args and isinstance(args[0], (str, Path)) and len(args) >= 5:
            # Legacy: (cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            data.setdefault("cwd", args[0])
            data.setdefault("issue_number", args[1] if len(args) > 1 else None)
            data.setdefault("workflow_type", args[2] if len(args) > 2 else "default")
            data.setdefault("state", args[3] if len(args) > 3 else {})
            data.setdefault("state_dir", args[4] if len(args) > 4 else None)
            data.setdefault("repo_owner", args[5] if len(args) > 5 else None)
            data.setdefault("repo_name", args[6] if len(args) > 6 else None)
            data.setdefault("use_github_state", args[7] if len(args) > 7 else False)
            data.setdefault("github_comment_id", args[8] if len(args) > 8 else None)
        elif op == "save" and args and isinstance(args[0], dict):
            data.setdefault("state", args[0])
            if len(args) > 1:
                data.setdefault("repo_owner", args[1])
            if len(args) > 2:
                data.setdefault("repo_name", args[2])
            if len(args) > 3:
                data.setdefault("issue_number", args[3])
            if len(args) > 4:
                data.setdefault("workflow", args[4])
            if len(args) > 5:
                data.setdefault("cwd", args[5])
        elif op in {"load", "clear"} and isinstance(args[0], (str, Path)) and len(args) >= 4:
            # Legacy: (cwd, issue_number, workflow_type, state_dir, repo_owner, repo_name, use_github_state)
            data.setdefault("cwd", args[0])
            data.setdefault("issue_number", args[1] if len(args) > 1 else None)
            data.setdefault("workflow_type", args[2] if len(args) > 2 else "default")
            data.setdefault("state_dir", args[3] if len(args) > 3 else None)
            data.setdefault("repo_owner", args[4] if len(args) > 4 else None)
            data.setdefault("repo_name", args[5] if len(args) > 5 else None)
            data.setdefault("use_github_state", args[6] if len(args) > 6 else False)
        else:
            names = ["repo_owner", "repo_name", "issue_number", "workflow", "cwd"]
            for name, value in zip(names, args):
                data.setdefault(name, value)
    workflow = data.get("workflow_type") or data.get("workflow_id") or data.get("workflow") or "default"
    data["workflow"] = str(workflow)
    data.setdefault("cwd", ".")
    data.setdefault("state_dir", None)
    data.setdefault("use_github_state", bool(data.get("repo_owner") and data.get("repo_name") and data.get("issue_number")))
    return data


def load_workflow_state(*args: Any, **kwargs: Any) -> Tuple[Optional[Dict], Optional[int]]:
    data = _normalize_state_call(args, kwargs, op="load")
    repo_owner = data.get("repo_owner")
    repo_name = data.get("repo_name")
    issue_number = data.get("issue_number")
    workflow = data["workflow"]
    cwd = data["cwd"]
    state_dir = data.get("state_dir")
    use_github_state = bool(data.get("use_github_state"))

    if use_github_state and repo_owner and repo_name and issue_number:
        state, cid = github_load_state(str(repo_owner), str(repo_name), int(issue_number), workflow, cwd)
        if state is not None:
            return state, cid

    local = _local_state_path(workflow, cwd, int(issue_number) if issue_number is not None else None, state_dir)
    if local.exists():
        try:
            with open(local, "r", encoding="utf-8") as f:
                return json.load(f), None
        except Exception:
            pass

    if not use_github_state and repo_owner and repo_name and issue_number:
        cid, state = _find_state_comment(str(repo_owner), str(repo_name), int(issue_number), workflow, cwd)
        if state is not None:
            return state, cid
    return None, None


def save_workflow_state(*args: Any, **kwargs: Any) -> Optional[int]:
    data = _normalize_state_call(args, kwargs, op="save")
    state = dict(data.get("state") or {})
    repo_owner = data.get("repo_owner")
    repo_name = data.get("repo_name")
    issue_number = data.get("issue_number")
    workflow = data["workflow"]
    cwd = data["cwd"]
    state_dir = data.get("state_dir")
    use_github_state = bool(data.get("use_github_state"))

    local = _local_state_path(workflow, cwd, int(issue_number) if issue_number is not None else None, state_dir)
    try:
        local.parent.mkdir(parents=True, exist_ok=True)
        with open(local, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2)
    except Exception as e:
        console.print(f"[yellow]Failed to save local workflow state: {e}[/yellow]")

    if use_github_state and repo_owner and repo_name and issue_number:
        cid = github_save_state(str(repo_owner), str(repo_name), int(issue_number), workflow, state, cwd)
        if cid is None:
            console.print("[yellow]Failed to save GitHub workflow state[/yellow]")
            return None
        return cid
    return None


def clear_workflow_state(*args: Any, **kwargs: Any) -> None:
    data = _normalize_state_call(args, kwargs, op="clear")
    repo_owner = data.get("repo_owner")
    repo_name = data.get("repo_name")
    issue_number = data.get("issue_number")
    workflow = data["workflow"]
    cwd = data["cwd"]
    state_dir = data.get("state_dir")
    use_github_state = bool(data.get("use_github_state"))

    local = _local_state_path(workflow, cwd, int(issue_number) if issue_number is not None else None, state_dir)
    try:
        if local.exists():
            local.unlink()
    except Exception:
        pass
    if use_github_state and repo_owner and repo_name and issue_number and _gh_available():
        cid, _ = _find_state_comment(str(repo_owner), str(repo_name), int(issue_number), workflow, cwd)
        if cid:
            _run_gh(
                [
                    "api", "--method", "DELETE",
                    f"repos/{repo_owner}/{repo_name}/issues/comments/{cid}",
                ],
                cwd,
            )


# ---------------------------------------------------------------------------
# State validation
# ---------------------------------------------------------------------------
def validate_cached_state(
    last_completed_step: Union[int, float],
    step_outputs: Dict[str, str],
    step_order: Optional[List[str]] = None,
    quiet: bool = False,
) -> Union[int, float]:
    """Scan step_outputs for FAILED markers and correct last_completed_step."""
    if not step_outputs:
        return last_completed_step

    if step_order:
        for idx, step_name in enumerate(step_order):
            output = step_outputs.get(str(step_name), step_outputs.get(step_name, ""))  # type: ignore[arg-type]
            if output == "" and idx < int(last_completed_step):
                corrected = idx
                if not isinstance(last_completed_step, int):
                    corrected = float(corrected)
                if not quiet:
                    console.print(
                        f"[yellow]State validation: missing output for step '{step_name}', "
                        f"correcting last_completed_step from {last_completed_step} to {corrected}[/yellow]"
                    )
                return corrected
            if isinstance(output, str) and "FAILED:" in output:
                if idx > 0:
                    prev_step = step_order[idx - 1]
                    try:
                        corrected = int(prev_step)  # type: ignore[arg-type]
                    except (TypeError, ValueError):
                        corrected = idx
                else:
                    corrected = 0
                if not isinstance(last_completed_step, int):
                    corrected = float(corrected)
                if not quiet:
                    console.print(
                        f"[yellow]State validation: step '{step_name}' marked FAILED. "
                        f"correcting last_completed_step from {last_completed_step} to {corrected}[/yellow]"
                    )
                return corrected
    else:
        def _step_sort_key(item: Tuple[str, str]) -> Tuple[int, Union[int, str]]:
            key = str(item[0])
            return (0, int(key)) if key.isdigit() else (1, key)

        for index, (step_name, output) in enumerate(sorted(step_outputs.items(), key=_step_sort_key)):
            if isinstance(output, str) and "FAILED:" in output:
                try:
                    step_number = int(str(step_name))
                    corrected_value: Union[int, float] = step_number - 1
                except ValueError:
                    corrected_value = index
                if not isinstance(last_completed_step, int):
                    corrected_value = float(corrected_value)
                if not quiet:
                    console.print(
                        f"[yellow]State validation: step '{step_name}' contains FAILED marker; "
                        f"correcting last_completed_step to {corrected_value}[/yellow]"
                    )
                return corrected_value

    return last_completed_step


# ---------------------------------------------------------------------------
# GitHub comment posters
# ---------------------------------------------------------------------------
def post_step_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    step_num: int,
    total_steps: int,
    description: str,
    output: str,
    cwd: str = ".",
) -> bool:
    if not _gh_available():
        console.print("[yellow]gh CLI not found; cannot post step comment[/yellow]")
        return False
    body = (
        f"## Step {step_num}/{total_steps}: {description}\n\n"
        f"<details><summary>Output</summary>\n\n```\n{output[-8000:]}\n```\n\n</details>\n"
    )
    rc, _, stderr = _run_gh(
        [
            "issue", "comment", str(issue_number),
            "--repo", f"{repo_owner}/{repo_name}",
            "--body", body,
        ],
        cwd,
    )
    if rc != 0:
        console.print(f"[yellow]Failed to post step comment: {stderr[:200]}[/yellow]")
        return False
    return True


def post_pr_comment(
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    body: str,
    cwd: str = ".",
) -> bool:
    if not _gh_available():
        console.print("[yellow]gh CLI not found; cannot post PR comment[/yellow]")
        return False
    rc, _, stderr = _run_gh(
        [
            "pr", "comment", str(pr_number),
            "--repo", f"{repo_owner}/{repo_name}",
            "--body", body,
        ],
        cwd,
    )
    if rc != 0:
        console.print(f"[yellow]Failed to post PR comment: {stderr[:200]}[/yellow]")
        return False
    return True


def post_final_comment(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    body: str,
    cwd: str = ".",
) -> bool:
    if not _gh_available():
        console.print("[yellow]gh CLI not found; cannot post final comment[/yellow]")
        return False
    rc, _, stderr = _run_gh(
        [
            "issue", "comment", str(issue_number),
            "--repo", f"{repo_owner}/{repo_name}",
            "--body", body,
        ],
        cwd,
    )
    if rc != 0:
        console.print(f"[yellow]Failed to post final comment: {stderr[:200]}[/yellow]")
        return False
    return True


__all__ = [
    "DEFAULT_TIMEOUT_SECONDS",
    "MIN_VALID_OUTPUT_LENGTH",
    "DEFAULT_MAX_RETRIES",
    "DEFAULT_RETRY_DELAY",
    "MAX_RETRY_DELAY",
    "JOB_TIMEOUT_MARGIN_SECONDS",
    "MIN_ATTEMPT_TIMEOUT_SECONDS",
    "MAX_ERROR_SNIPPET_LENGTH",
    "MAX_ERROR_RESPONSE_NEWLINES",
    "GITHUB_STATE_MARKER_START",
    "GITHUB_STATE_MARKER_END",
    "TokenMatch",
    "SEMANTIC_PATTERNS",
    "Pricing",
    "_calculate_anthropic_cost",
    "_calculate_gemini_cost",
    "_calculate_codex_cost",
    "_parse_provider_json",
    "_parse_opencode_jsonl",
    "get_agent_provider_preference",
    "get_available_agents",
    "run_agentic_task",
    "_revert_out_of_scope_changes",
    "detect_control_token",
    "classify_step_output",
    "_codex_auth_failure_message",
    "substitute_template_variables",
    "set_agentic_progress",
    "clear_agentic_progress",
    "get_and_clear_agentic_interrupt_context",
    "get_job_deadline",
    "post_step_comment",
    "post_pr_comment",
    "post_final_comment",
    "validate_cached_state",
    "_serialize_state_comment",
    "github_load_state",
    "github_save_state",
    "github_clear_state",
    "load_workflow_state",
    "save_workflow_state",
    "clear_workflow_state",
]
