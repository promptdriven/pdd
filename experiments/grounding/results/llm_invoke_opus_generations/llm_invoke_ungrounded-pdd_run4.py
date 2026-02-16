from __future__ import annotations

import ast
import copy
import json
import logging
import os
import re
import sys
import time as time_module
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Type, Union

import litellm
import pandas as pd
from dotenv import load_dotenv, set_key
from pydantic import BaseModel
from rich.console import Console

# ─── Internal Imports ───────────────────────────────────────────────────────────

try:
    from . import DEFAULT_STRENGTH, DEFAULT_TIME, EXTRACTION_STRENGTH
except ImportError:
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = 0.25
    EXTRACTION_STRENGTH = 0.5

try:
    from .path_resolution import get_default_resolver
except ImportError:
    get_default_resolver = None  # type: ignore[assignment]

try:
    from .cloud_config import CloudConfig  # type: ignore[import-untyped]
except ImportError:
    CloudConfig = None  # type: ignore[assignment,misc]

try:
    from .cloud_auth import get_jwt_token, clear_jwt_cache  # type: ignore[import-untyped]
except ImportError:
    get_jwt_token = None  # type: ignore[assignment]
    clear_jwt_cache = None  # type: ignore[assignment]

# ─── Constants ──────────────────────────────────────────────────────────────────

LLM_CALL_TIMEOUT: int = 120
_CLOUD_TIMEOUT: int = 300
_PROSE_FIELD_NAMES: set[str] = {
    "reasoning", "explanation", "analysis", "thought", "thinking",
    "rationale", "description", "summary", "note", "notes",
    "justification", "context", "interpretation",
}

# ─── Console ────────────────────────────────────────────────────────────────────

console = Console(stderr=True)

# ─── Exceptions ─────────────────────────────────────────────────────────────────


class SchemaValidationError(Exception):
    """Raised when structured output fails schema validation; triggers model fallback."""


class CloudFallbackError(Exception):
    """Recoverable cloud error (network, timeout, auth, 5xx). Triggers local fallback."""


class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""


class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required. Does NOT fall back to local."""


# ─── Logging ────────────────────────────────────────────────────────────────────

logger = logging.getLogger("pdd.llm_invoke")
_litellm_logger = logging.getLogger("litellm")


def _configure_logging() -> None:
    """Configure loggers based on environment variables."""
    environment = os.getenv("PDD_ENVIRONMENT", "").lower()
    verbose_flag = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"

    if verbose_flag:
        pdd_level = logging.DEBUG
    else:
        default_pdd = "WARNING" if environment == "production" else "INFO"
        pdd_level = getattr(logging, os.getenv("PDD_LOG_LEVEL", default_pdd).upper(), logging.INFO)

    default_litellm = "WARNING" if environment == "production" else "WARNING"
    litellm_level = getattr(
        logging,
        os.getenv("LITELLM_LOG_LEVEL", default_litellm).upper(),
        logging.WARNING,
    )

    logger.setLevel(pdd_level)
    _litellm_logger.setLevel(litellm_level)

    if not logger.handlers:
        handler = logging.StreamHandler()
        handler.setFormatter(logging.Formatter("%(name)s - %(levelname)s - %(message)s"))
        logger.addHandler(handler)


def setup_file_logging(log_dir: Optional[Path] = None) -> None:
    """Add rotating file handler (10 MB, 5 backups)."""
    if log_dir is None:
        log_dir = Path.cwd() / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "pdd_llm_invoke.log",
        maxBytes=10 * 1024 * 1024,
        backupCount=5,
    )
    handler.setFormatter(
        logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    )
    logger.addHandler(handler)


def set_verbose_logging(enable: bool = True) -> None:
    """Toggle DEBUG level on pdd logger."""
    logger.setLevel(logging.DEBUG if enable else logging.INFO)


# ─── WSL Diagnostics ───────────────────────────────────────────────────────────

_IS_WSL: Optional[bool] = None


def _detect_wsl() -> bool:
    """Detect whether we are running inside WSL."""
    global _IS_WSL
    if _IS_WSL is not None:
        return _IS_WSL
    if os.getenv("WSL_DISTRO_NAME"):
        _IS_WSL = True
        return True
    try:
        with open("/proc/version", "r") as f:
            _IS_WSL = "microsoft" in f.read().lower()
    except (OSError, FileNotFoundError):
        _IS_WSL = False
    return _IS_WSL  # type: ignore[return-value]


def _sanitize_api_key(key: str) -> str:
    """Trim whitespace and control characters (especially \\r on WSL)."""
    return key.strip().strip("\r\n\t\x00")


# ─── Path / CSV Resolution ─────────────────────────────────────────────────────

_project_root: Optional[Path] = None


def _resolve_project_root() -> Path:
    """Resolve project root using PathResolver or marker search."""
    global _project_root
    if _project_root is not None:
        return _project_root

    if get_default_resolver is not None:
        try:
            resolver = get_default_resolver()
            _project_root = Path(resolver.resolve_project_root())
            return _project_root
        except Exception:
            pass

    # Fallback: search upward for markers
    cwd = Path.cwd()
    markers = {".git", "pyproject.toml", "data", ".env"}
    current = cwd
    while current != current.parent:
        if any((current / m).exists() for m in markers):
            _project_root = current
            return _project_root
        current = current.parent
    _project_root = cwd
    return _project_root


def _resolve_csv_path() -> Path:
    """Resolve llm_model.csv in priority order."""
    # (a) ~/.pdd/llm_model.csv
    home_csv = Path.home() / ".pdd" / "llm_model.csv"
    if home_csv.is_file():
        return home_csv

    # (b) <PROJECT_ROOT>/.pdd/llm_model.csv if PDD_PATH points to a real project
    pdd_path_env = os.getenv("PDD_PATH")
    pkg_dir = str(Path(__file__).resolve().parent)
    if pdd_path_env:
        pdd_p = Path(pdd_path_env).resolve()
        if not str(pdd_p).startswith(pkg_dir):
            proj_csv = pdd_p / ".pdd" / "llm_model.csv"
            if proj_csv.is_file():
                return proj_csv

    # Also try project root
    try:
        root = _resolve_project_root()
        root_csv = root / ".pdd" / "llm_model.csv"
        if root_csv.is_file():
            return root_csv
    except Exception:
        pass

    # (c) <cwd>/.pdd/llm_model.csv
    cwd_csv = Path.cwd() / ".pdd" / "llm_model.csv"
    if cwd_csv.is_file():
        return cwd_csv

    # (d) packaged pdd/data/llm_model.csv
    pkg_csv = Path(__file__).resolve().parent / "data" / "llm_model.csv"
    if pkg_csv.is_file():
        return pkg_csv

    raise FileNotFoundError(
        "Could not find llm_model.csv in any of the expected locations: "
        f"{home_csv}, <project>/.pdd/, {cwd_csv}, {pkg_csv}"
    )


# ─── CSV Loading & Model Rate Map ──────────────────────────────────────────────

_model_df: Optional[pd.DataFrame] = None
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}


def _load_model_csv() -> pd.DataFrame:
    """Load and cache the model CSV. Build the rate map."""
    global _model_df, _MODEL_RATE_MAP
    if _model_df is not None:
        return _model_df

    csv_path = _resolve_csv_path()
    logger.debug("Loading model CSV from %s", csv_path)
    df = pd.read_csv(csv_path)

    # Normalise column names
    df.columns = df.columns.str.strip().str.lower()

    required_cols = {"model", "provider", "input", "output", "coding_arena_elo", "api_key"}
    missing = required_cols - set(df.columns)
    if missing:
        raise ValueError(f"Model CSV missing required columns: {missing}")

    # Fill optional columns
    for col, default in [
        ("structured_output", False),
        ("reasoning_type", "none"),
        ("max_reasoning_tokens", 0),
        ("location", ""),
        ("base_url", ""),
    ]:
        if col not in df.columns:
            df[col] = default

    df["structured_output"] = df["structured_output"].astype(str).str.strip().str.lower().isin(
        {"true", "1", "yes"}
    )
    df["max_reasoning_tokens"] = pd.to_numeric(df["max_reasoning_tokens"], errors="coerce").fillna(0).astype(int)
    df["input"] = pd.to_numeric(df["input"], errors="coerce").fillna(0.0)
    df["output"] = pd.to_numeric(df["output"], errors="coerce").fillna(0.0)
    df["coding_arena_elo"] = pd.to_numeric(df["coding_arena_elo"], errors="coerce").fillna(0)
    df["api_key"] = df["api_key"].fillna("").astype(str).str.strip()
    df["location"] = df["location"].fillna("").astype(str).str.strip()
    df["base_url"] = df["base_url"].fillna("").astype(str).str.strip()
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.strip().str.lower()

    _model_df = df
    _MODEL_RATE_MAP = {
        row["model"]: (row["input"], row["output"])
        for _, row in df.iterrows()
    }
    return df


# ─── API Key Management ────────────────────────────────────────────────────────

_newly_acquired_keys: set[str] = set()


def _check_and_acquire_api_key(key_name: str, model_name: str) -> bool:
    """Check for API key, prompt interactively if missing.

    Returns True if key is available, False if model should be skipped.
    """
    if not key_name or key_name.upper() == "EXISTING_KEY":
        return True

    existing = os.getenv(key_name)
    if existing and existing.strip():
        return True

    # Non-interactive mode
    if os.getenv("PDD_FORCE"):
        logger.info("PDD_FORCE set; skipping model %s (missing %s)", model_name, key_name)
        return False

    console.print(
        f"[yellow]API key [bold]{key_name}[/bold] required for model "
        f"[bold]{model_name}[/bold] is not set.[/yellow]"
    )
    try:
        raw = input(f"Enter {key_name}: ")
    except (EOFError, KeyboardInterrupt):
        logger.info("User cancelled key input for %s", key_name)
        return False

    key_value = _sanitize_api_key(raw)
    if not key_value:
        console.print("[red]Empty key provided, skipping model.[/red]")
        return False

    os.environ[key_name] = key_value
    _newly_acquired_keys.add(key_name)

    # Save to .env
    _save_key_to_dotenv(key_name, key_value)
    return True


def _save_key_to_dotenv(key_name: str, key_value: str) -> None:
    """Save API key to .env file, replacing existing entry in-place."""
    try:
        root = _resolve_project_root()
    except Exception:
        root = Path.cwd()

    env_path = root / ".env"
    env_path.touch(exist_ok=True)

    # Read existing lines, remove old entries (including commented ones)
    lines = env_path.read_text().splitlines()
    pattern = re.compile(rf"^\s*#?\s*{re.escape(key_name)}\s*=")
    cleaned = [line for line in lines if not pattern.match(line)]

    # Add new key
    cleaned.append(f"{key_name}={key_value}")
    env_path.write_text("\n".join(cleaned) + "\n")

    logger.warning("API key %s saved to %s – treat this file as sensitive.", key_name, env_path)
    console.print(
        f"[yellow]⚠ Key [bold]{key_name}[/bold] saved to [bold]{env_path}[/bold]. "
        f"Keep this file secure.[/yellow]"
    )


# ─── Vertex AI Support ─────────────────────────────────────────────────────────

def _is_vertex_model(provider: str, model: str) -> bool:
    """Detect Vertex AI model by provider or prefix."""
    provider_lower = provider.lower().strip()
    return (
        provider_lower in ("google", "vertex_ai", "vertex")
        or model.startswith("vertex_ai/")
    )


def _get_vertex_credentials() -> Dict[str, Any]:
    """Load Vertex AI credentials from environment."""
    result: Dict[str, Any] = {}

    cred_path = os.getenv("VERTEX_CREDENTIALS", "")
    if cred_path and Path(cred_path).is_file():
        result["vertex_credentials"] = Path(cred_path).read_text()

    project = os.getenv("VERTEX_PROJECT", "")
    if project:
        result["vertex_project"] = project

    location = os.getenv("VERTEX_LOCATION", "us-central1")
    if location:
        result["vertex_location"] = location

    return result


# ─── Cache Setup ────────────────────────────────────────────────────────────────

_cache_initialized: bool = False


def _setup_cache() -> None:
    """Configure LiteLLM caching: S3-compatible (GCS HMAC) → disk SQLite → none."""
    global _cache_initialized
    if _cache_initialized:
        return
    _cache_initialized = True

    if os.getenv("LITELLM_CACHE_DISABLE", "0") == "1":
        logger.debug("LiteLLM caching disabled by LITELLM_CACHE_DISABLE")
        return

    # Try S3-compatible (GCS HMAC keys)
    hmac_key = os.getenv("GCS_HMAC_ACCESS_KEY_ID")
    hmac_secret = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
    bucket = os.getenv("GCS_BUCKET_NAME")

    if hmac_key and hmac_secret and bucket:
        try:
            litellm.cache = litellm.Cache(
                type="s3",
                s3_bucket_name=bucket,
                s3_region_name="auto",
                s3_endpoint_url="https://storage.googleapis.com",
                s3_access_key_id=hmac_key,
                s3_secret_access_key=hmac_secret,
            )
            logger.debug("LiteLLM S3-compatible cache configured (GCS bucket: %s)", bucket)
            return
        except Exception as exc:
            logger.warning("S3 cache setup failed, falling back to disk: %s", exc)

    # Disk-based SQLite cache
    try:
        root = _resolve_project_root()
        db_path = str(root / "litellm_cache.sqlite")
        litellm.cache = litellm.Cache(type="disk", disk_cache_dir=db_path)
        logger.debug("LiteLLM disk cache at %s", db_path)
    except Exception as exc:
        logger.warning("Disk cache setup failed: %s", exc)


# ─── LiteLLM Callback ──────────────────────────────────────────────────────────

_LAST_CALLBACK_DATA: Dict[str, Any] = {}


def _litellm_success_callback(kwargs: Any, completion_response: Any, start_time: Any, end_time: Any) -> None:
    """Success callback registered with LiteLLM to capture cost data."""
    global _LAST_CALLBACK_DATA
    data: Dict[str, Any] = {}
    try:
        if hasattr(completion_response, "usage") and completion_response.usage:
            usage = completion_response.usage
            data["prompt_tokens"] = getattr(usage, "prompt_tokens", 0)
            data["completion_tokens"] = getattr(usage, "completion_tokens", 0)
            data["total_tokens"] = getattr(usage, "total_tokens", 0)

        if hasattr(completion_response, "choices") and completion_response.choices:
            data["finish_reason"] = getattr(completion_response.choices[0], "finish_reason", None)

        try:
            data["cost"] = litellm.completion_cost(completion_response=completion_response)
        except Exception:
            data["cost"] = 0.0
    except Exception as exc:
        logger.debug("Callback data extraction error: %s", exc)
        data["cost"] = 0.0

    _LAST_CALLBACK_DATA = data


def _compute_cost_fallback(
    model: str, prompt_tokens: int, completion_tokens: int
) -> float:
    """Compute cost from CSV rates when LiteLLM cost calculation fails."""
    rates = _MODEL_RATE_MAP.get(model)
    if not rates:
        return 0.0
    input_rate, output_rate = rates  # $/M tokens
    return (prompt_tokens * input_rate + completion_tokens * output_rate) / 1_000_000


def _get_cost_from_response(response: Any, model: str) -> float:
    """Extract cost from response, callback data, or CSV fallback."""
    # Try litellm.completion_cost first
    try:
        cost = litellm.completion_cost(completion_response=response)
        if cost and cost > 0:
            return float(cost)
    except Exception:
        pass

    # Try callback data
    if _LAST_CALLBACK_DATA.get("cost", 0) > 0:
        return float(_LAST_CALLBACK_DATA["cost"])

    # CSV fallback
    if hasattr(response, "usage") and response.usage:
        pt = getattr(response.usage, "prompt_tokens", 0) or 0
        ct = getattr(response.usage, "completion_tokens", 0) or 0
        return _compute_cost_fallback(model, pt, ct)

    return 0.0


# ─── Initialization ────────────────────────────────────────────────────────────

_initialized: bool = False


def _ensure_initialized() -> None:
    """Lazy one-time initialization: load .env, configure logging, cache, callbacks."""
    global _initialized
    if _initialized:
        return
    _initialized = True

    # Load .env from project root
    try:
        root = _resolve_project_root()
        env_file = root / ".env"
        if env_file.is_file():
            load_dotenv(str(env_file), override=False)
            logger.debug("Loaded .env from %s", env_file)
    except Exception:
        load_dotenv(override=False)

    _configure_logging()

    # litellm.drop_params
    drop_str = os.getenv("LITELLM_DROP_PARAMS", "true").lower()
    litellm.drop_params = drop_str in ("true", "1", "yes")

    # Register callback
    if _litellm_success_callback not in litellm.success_callback:
        litellm.success_callback.append(_litellm_success_callback)  # type: ignore[arg-type]

    _setup_cache()
    _load_model_csv()


# ─── Model Selection ───────────────────────────────────────────────────────────


def _get_available_models(df: pd.DataFrame) -> pd.DataFrame:
    """Filter models to those with a non-empty api_key column."""
    return df[df["api_key"].str.len() > 0].copy()


def _select_model_candidates(
    strength: float,
    use_cloud: Optional[bool],
) -> List[Dict[str, Any]]:
    """Return ordered list of candidate model rows based on strength.

    Each element is a dict from the CSV row.
    """
    df = _load_model_csv()
    available = _get_available_models(df)

    if available.empty:
        raise RuntimeError("No models available in CSV (all missing api_key).")

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")

    if base_model_name and base_model_name in available["model"].values:
        base_idx = available[available["model"] == base_model_name].index[0]
    else:
        # Use first available as surrogate (silently)
        base_idx = available.index[0]

    base_row = available.loc[base_idx]

    if abs(strength - 0.5) < 1e-9:
        # strength = 0.5: base model, fallback to next highest ELO
        sorted_elo = available.sort_values("coding_arena_elo", ascending=False)
        ordered = [base_row.to_dict()]
        for _, row in sorted_elo.iterrows():
            d = row.to_dict()
            if d["model"] != base_row["model"]:
                ordered.append(d)
        return ordered

    if strength < 0.5:
        # Interpolate by cost from cheapest to base
        available = available.copy()
        available["_total_cost"] = available["input"] + available["output"]
        base_cost = float(base_row["input"]) + float(base_row["output"])
        cheapest_cost = float(available["_total_cost"].min())
        t = strength / 0.5
        target_cost = cheapest_cost + t * (base_cost - cheapest_cost)
        available["_diff"] = (available["_total_cost"] - target_cost).abs()
        sorted_df = available.sort_values("_diff")
        return [row.to_dict() for _, row in sorted_df.iterrows()]

    # strength > 0.5: interpolate by ELO from base to highest
    base_elo = float(base_row["coding_arena_elo"])
    highest_elo = float(available["coding_arena_elo"].max())
    t = (strength - 0.5) / 0.5
    target_elo = base_elo + t * (highest_elo - base_elo)
    available = available.copy()
    available["_diff"] = (available["coding_arena_elo"] - target_elo).abs()
    sorted_df = available.sort_values("_diff")
    return [row.to_dict() for _, row in sorted_df.iterrows()]


# ─── Reasoning Parameters ──────────────────────────────────────────────────────


def _build_reasoning_params(
    model_row: Dict[str, Any],
    time_param: float,
) -> Dict[str, Any]:
    """Build reasoning/thinking parameters based on CSV reasoning_type."""
    reasoning_type = str(model_row.get("reasoning_type", "none")).lower()
    max_tokens = int(model_row.get("max_reasoning_tokens", 0))
    model_name = str(model_row.get("model", ""))
    params: Dict[str, Any] = {}

    if reasoning_type == "budget":
        budget_tokens = max(1, int(time_param * max_tokens))
        # Anthropic-style thinking
        if "claude" in model_name.lower() or "anthropic" in str(model_row.get("provider", "")).lower():
            params["thinking"] = {"type": "enabled", "budget_tokens": budget_tokens}
        else:
            params["thinking"] = {"type": "enabled", "budget_tokens": budget_tokens}

    elif reasoning_type == "effort":
        if time_param <= 0.33:
            effort_str = "low"
        elif time_param <= 0.66:
            effort_str = "medium"
        else:
            effort_str = "high"

        # OpenAI gpt-5* uses responses API with reasoning dict
        if model_name.startswith("gpt-5"):
            params["_reasoning_for_responses"] = {"effort": effort_str, "summary": "auto"}
        else:
            params["reasoning_effort"] = effort_str

    # reasoning_type == "none" → no params

    return params


# ─── Structured Output Helpers ──────────────────────────────────────────────────


def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively ensure ALL properties appear in required arrays."""
    schema = copy.deepcopy(schema)
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop_schema in schema["properties"].values():
            if isinstance(prop_schema, dict):
                _ensure_all_properties_required_inplace(prop_schema)
    if "items" in schema and isinstance(schema["items"], dict):
        _ensure_all_properties_required_inplace(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for item in schema[key]:
                if isinstance(item, dict):
                    _ensure_all_properties_required_inplace(item)
    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            if isinstance(def_schema, dict):
                _ensure_all_properties_required_inplace(def_schema)
    return schema


def _ensure_all_properties_required_inplace(schema: Dict[str, Any]) -> None:
    """In-place variant for recursive calls."""
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop_schema in schema["properties"].values():
            if isinstance(prop_schema, dict):
                _ensure_all_properties_required_inplace(prop_schema)
    if "items" in schema and isinstance(schema["items"], dict):
        _ensure_all_properties_required_inplace(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for item in schema[key]:
                if isinstance(item, dict):
                    _ensure_all_properties_required_inplace(item)
    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            if isinstance(def_schema, dict):
                _ensure_all_properties_required_inplace(def_schema)


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively add additionalProperties: false on ALL object schemas."""
    schema = copy.deepcopy(schema)
    _add_ap_false_inplace(schema)
    return schema


def _add_ap_false_inplace(schema: Dict[str, Any]) -> None:
    """In-place recursive additionalProperties: false."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop_schema in schema["properties"].values():
                if isinstance(prop_schema, dict):
                    _add_ap_false_inplace(prop_schema)
    if "items" in schema and isinstance(schema["items"], dict):
        _add_ap_false_inplace(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for item in schema[key]:
                if isinstance(item, dict):
                    _add_ap_false_inplace(item)
    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            if isinstance(def_schema, dict):
                _add_ap_false_inplace(def_schema)


def _build_response_format(
    model_row: Dict[str, Any],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    messages: List[Dict[str, Any]],
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]], List[Dict[str, Any]]]:
    """Build response_format and extra_body for structured output.

    Returns (response_format, extra_body, possibly-modified messages).
    """
    if not output_pydantic and not output_schema:
        return None, None, messages

    # Build raw schema
    if output_pydantic:
        raw_schema = output_pydantic.model_json_schema()
        schema_name = output_pydantic.__name__
    else:
        raw_schema = output_schema  # type: ignore[assignment]
        schema_name = raw_schema.get("title", "response_schema")  # type: ignore[union-attr]

    # Enforce strictness
    processed = _ensure_all_properties_required(raw_schema)  # type: ignore[arg-type]
    processed = _add_additional_properties_false(processed)

    # Remove unsupported keys for strict schemas
    processed.pop("title", None)
    if "$defs" not in processed:
        processed.pop("$defs", None)

    model_name = str(model_row.get("model", ""))
    supports_structured = bool(model_row.get("structured_output", False))
    provider = str(model_row.get("provider", "")).lower()

    # Groq: simple json_object + schema in system prompt
    if "groq" in provider or "groq" in model_name.lower():
        schema_instruction = (
            f"You MUST respond with valid JSON matching this schema:\n"
            f"```json\n{json.dumps(processed, indent=2)}\n```"
        )
        messages = list(messages)
        if messages and messages[0].get("role") == "system":
            messages[0] = dict(messages[0])
            messages[0]["content"] = messages[0]["content"] + "\n\n" + schema_instruction
        else:
            messages.insert(0, {"role": "system", "content": schema_instruction})
        return {"type": "json_object"}, None, messages

    if supports_structured:
        response_format: Dict[str, Any] = {
            "type": "json_schema",
            "json_schema": {
                "name": schema_name,
                "schema": processed,
                "strict": True,
            },
        }

        extra_body: Optional[Dict[str, Any]] = None
        # LM Studio: bypass drop_params
        if "lm-studio" in model_name.lower() or "lm_studio" in provider:
            extra_body = {"response_format": response_format}
            return None, extra_body, messages

        return response_format, None, messages

    # Model doesn't support structured output – add schema as instruction
    schema_instruction = (
        f"Respond with valid JSON matching this schema:\n"
        f"```json\n{json.dumps(processed, indent=2)}\n```"
    )
    messages = list(messages)
    if messages and messages[0].get("role") == "system":
        messages[0] = dict(messages[0])
        messages[0]["content"] = messages[0]["content"] + "\n\n" + schema_instruction
    else:
        messages.insert(0, {"role": "system", "content": schema_instruction})
    return None, None, messages


# ─── JSON Parsing & Repair ──────────────────────────────────────────────────────


def _extract_json_from_fenced(text: str) -> Optional[str]:
    """Extract JSON from ```json ... ``` fences."""
    pattern = r"```(?:json)?\s*\n?(.*?)```"
    match = re.search(pattern, text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None


def _extract_balanced_json(text: str) -> Optional[str]:
    """Extract a balanced JSON object from text."""
    start = text.find("{")
    if start == -1:
        return None
    depth = 0
    in_string = False
    escape = False
    for i in range(start, len(text)):
        ch = text[i]
        if escape:
            escape = False
            continue
        if ch == "\\":
            escape = True
            continue
        if ch == '"' and not escape:
            in_string = not in_string
            continue
        if in_string:
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                candidate = text[start : i + 1]
                try:
                    json.loads(candidate)
                    return candidate
                except json.JSONDecodeError:
                    pass
    # Return partial if depth didn't balance
    return text[start:]


def _clean_fences(text: str) -> str:
    """Remove markdown code fences."""
    text = re.sub(r"^```\w*\n?", "", text.strip())
    text = re.sub(r"\n?```\s*$", "", text)
    return text.strip()


def _repair_truncated_json(text: str) -> Optional[Any]:
    """Try to repair truncated JSON by appending closures."""
    closures = [
        '}',
        '"}',
        '"]}',
        '"]}]}',
        '"]}]}}',
        ']',
        '"]',
        '}}',
        '"}}',
        ']}',
    ]
    for closure in closures:
        candidate = text.rstrip() + closure
        try:
            return json.loads(candidate)
        except json.JSONDecodeError:
            continue
    # Try closing multiple braces
    open_braces = text.count("{") - text.count("}")
    open_brackets = text.count("[") - text.count("]")
    if open_braces > 0 or open_brackets > 0:
        suffix = "]" * max(0, open_brackets) + "}" * max(0, open_braces)
        try:
            return json.loads(text.rstrip() + suffix)
        except json.JSONDecodeError:
            # Try with closing quote first
            try:
                return json.loads(text.rstrip() + '"' + suffix)
            except json.JSONDecodeError:
                pass
    return None


def _parse_json_response(text: str) -> Any:
    """Robust JSON parsing with multiple strategies."""
    # Try direct parse
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass

    # Try fenced extraction
    fenced = _extract_json_from_fenced(text)
    if fenced:
        try:
            return json.loads(fenced)
        except json.JSONDecodeError:
            repaired = _repair_truncated_json(fenced)
            if repaired is not None:
                return repaired

    # Try balanced extraction
    balanced = _extract_balanced_json(text)
    if balanced:
        try:
            return json.loads(balanced)
        except json.JSONDecodeError:
            repaired = _repair_truncated_json(balanced)
            if repaired is not None:
                return repaired

    # Try fence cleaning
    cleaned = _clean_fences(text)
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError:
        repaired = _repair_truncated_json(cleaned)
        if repaired is not None:
            return repaired

    raise json.JSONDecodeError("Could not parse JSON from response", text, 0)


# ─── Python Validation & Repair ────────────────────────────────────────────────


def _smart_unescape_code(code: str) -> str:
    """Unescape double-escaped newlines while preserving \\n inside string literals."""
    # Replace \\n that are not inside string literals
    lines = code.split("\n")
    result_lines: List[str] = []
    for line in lines:
        # Simple heuristic: replace \\n outside of quoted strings
        parts: List[str] = []
        in_str = False
        str_char = ""
        i = 0
        while i < len(line):
            ch = line[i]
            if not in_str:
                if ch in ('"', "'"):
                    # Check for triple quotes
                    if line[i : i + 3] in ('"""', "'''"):
                        in_str = True
                        str_char = line[i : i + 3]
                        parts.append(str_char)
                        i += 3
                        continue
                    in_str = True
                    str_char = ch
                    parts.append(ch)
                elif line[i : i + 2] == "\\n":
                    parts.append("\n")
                    i += 2
                    continue
                else:
                    parts.append(ch)
            else:
                if len(str_char) == 3:
                    if line[i : i + 3] == str_char:
                        parts.append(str_char)
                        in_str = False
                        i += 3
                        continue
                elif ch == str_char and (i == 0 or line[i - 1] != "\\"):
                    in_str = False
                parts.append(ch)
            i += 1
        result_lines.append("".join(parts))
    return "\n".join(result_lines)


def _repair_python_syntax(code: str) -> str:
    """Attempt to repair common Python syntax errors."""
    # Fix trailing unclosed quotes
    lines = code.split("\n")
    repaired_lines: List[str] = []
    for line in lines:
        stripped = line.rstrip()
        # Count unmatched quotes
        single = stripped.count("'") - stripped.count("\\'")
        double = stripped.count('"') - stripped.count('\\"')
        if single % 2 != 0:
            stripped += "'"
        if double % 2 != 0:
            stripped += '"'
        repaired_lines.append(stripped)
    return "\n".join(repaired_lines)


def _is_valid_python(code: str) -> bool:
    """Check if code is valid Python syntax."""
    try:
        ast.parse(code)
        return True
    except SyntaxError:
        return False


def _validate_code_fields(
    data: Dict[str, Any],
    language: Optional[str],
) -> Tuple[bool, Dict[str, Any]]:
    """Validate and repair code fields in structured output.

    Returns (all_valid, repaired_data).
    """
    if language is not None and language.lower() != "python":
        return True, data

    data = copy.deepcopy(data)
    all_valid = True

    for key, value in data.items():
        if key.lower() in _PROSE_FIELD_NAMES:
            continue
        if not isinstance(value, str):
            continue
        # Check if it looks like code
        if any(kw in value for kw in ("def ", "class ", "import ", "return ", "if ", "for ")):
            value = _smart_unescape_code(value)
            if not _is_valid_python(value):
                value = _repair_python_syntax(value)
                if not _is_valid_python(value):
                    all_valid = False
            data[key] = value

    return all_valid, data


# ─── Response Processing ───────────────────────────────────────────────────────


def _extract_thinking(response: Any) -> Optional[str]:
    """Extract thinking/reasoning output from response."""
    # Check _hidden_params
    if hasattr(response, "_hidden_params"):
        hp = response._hidden_params
        if isinstance(hp, dict) and "thinking" in hp:
            return str(hp["thinking"])

    # Check reasoning_content
    if hasattr(response, "choices") and response.choices:
        msg = response.choices[0].message
        if hasattr(msg, "reasoning_content") and msg.reasoning_content:
            return str(msg.reasoning_content)

    return None


def _process_response(
    response: Any,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
    model_name: str,
    is_responses_api: bool = False,
) -> Dict[str, Any]:
    """Process an LLM response into the standard return dict."""
    thinking_output = _extract_thinking(response)
    cost = _get_cost_from_response(response, model_name)

    # Extract content
    if is_responses_api:
        content = _extract_responses_api_content(response)
    else:
        if (
            hasattr(response, "choices")
            and response.choices
            and hasattr(response.choices[0], "message")
        ):
            content = response.choices[0].message.content
        else:
            content = None

    if content is None:
        raise ValueError("Response content is None – may need retry with cache bypass.")

    # Check for excessive trailing newlines (possible truncation)
    if content.rstrip() != content and content.count("\n") > len(content) // 2:
        raise ValueError("Response appears truncated (excessive trailing newlines).")

    result: Any = content

    # If structured output expected, parse as JSON
    if output_pydantic or output_schema:
        try:
            parsed = _parse_json_response(content)
        except json.JSONDecodeError:
            raise SchemaValidationError(f"Could not parse JSON from response: {content[:200]}")

        if isinstance(parsed, dict):
            valid, repaired = _validate_code_fields(parsed, language)
            parsed = repaired
            if not valid and (language is None or language.lower() == "python"):
                raise ValueError("Invalid Python code in response fields – retry needed.")

        if output_pydantic:
            try:
                result = output_pydantic.model_validate(parsed)
            except Exception as exc:
                raise SchemaValidationError(f"Pydantic validation failed: {exc}")
        else:
            result = parsed
    else:
        # Plain text – check code validity for Python
        stripped = content.strip()
        if stripped and (language is None or language.lower() == "python"):
            if any(kw in stripped for kw in ("def ", "class ", "import ")):
                unescaped = _smart_unescape_code(stripped)
                if not _is_valid_python(unescaped):
                    repaired = _repair_python_syntax(unescaped)
                    if _is_valid_python(repaired):
                        result = repaired
                    else:
                        raise ValueError("Invalid Python in response – retry needed.")
                else:
                    result = unescaped

    return {
        "result": result,
        "cost": cost,
        "model_name": model_name,
        "thinking_output": thinking_output,
    }


def _extract_responses_api_content(response: Any) -> Optional[str]:
    """Extract text content from OpenAI Responses API response."""
    if hasattr(response, "output"):
        for item in response.output:
            if hasattr(item, "content"):
                for block in item.content:
                    if hasattr(block, "text"):
                        return block.text
            if hasattr(item, "text"):
                return item.text
    return None


# ─── Cloud Execution ───────────────────────────────────────────────────────────


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    """Convert Pydantic model to JSON Schema for cloud transport."""
    schema = pydantic_class.model_json_schema()
    schema = _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    """Validate cloud response using the Pydantic model."""
    if isinstance(result, str):
        try:
            result = json.loads(result)
        except json.JSONDecodeError:
            pass
    return pydantic_class.model_validate(result)


def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    strength: float,
    temperature: float,
    verbose: bool,
    output_schema: Optional[Dict[str, Any]],
    time_param: float,
    use_batch_mode: bool,
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]],
    language: Optional[str],
) -> Dict[str, Any]:
    """Execute llm_invoke via cloud endpoint ``llmInvoke``."""
    try:
        import requests  # noqa: I001
    except ImportError:
        raise CloudInvocationError("requests package required for cloud execution")

    if get_jwt_token is None:
        raise CloudFallbackError("Cloud auth module not available")

    try:
        token = get_jwt_token()
    except Exception as exc:
        raise CloudFallbackError(f"Failed to get JWT token: {exc}")

    if CloudConfig is None:
        raise CloudFallbackError("CloudConfig not available")

    try:
        base_url = CloudConfig.get_cloud_functions_url()
    except Exception:
        base_url = "https://us-central1-prompt-driven-development.cloudfunctions.net"

    url = f"{base_url}/llmInvoke"

    payload: Dict[str, Any] = {
        "strength": strength,
        "temperature": temperature,
        "time": time_param,
        "verbose": verbose,
        "useBatchMode": use_batch_mode,
    }
    if prompt is not None:
        payload["prompt"] = prompt
    if input_json is not None:
        payload["inputJson"] = input_json
    if messages is not None:
        payload["messages"] = messages
    if output_schema is not None:
        payload["outputSchema"] = output_schema
    if language is not None:
        payload["language"] = language

    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json",
    }

    try:
        resp = requests.post(url, json=payload, headers=headers, timeout=_CLOUD_TIMEOUT)
    except requests.exceptions.Timeout:
        raise CloudFallbackError("Cloud request timed out")
    except requests.exceptions.ConnectionError as exc:
        raise CloudFallbackError(f"Cloud connection error: {exc}")

    if resp.status_code == 402:
        try:
            err_msg = resp.json().get("error", {}).get("message", "Insufficient credits")
        except Exception:
            err_msg = "Insufficient credits"
        raise InsufficientCreditsError(err_msg)

    if resp.status_code in (401, 403):
        if clear_jwt_cache is not None:
            clear_jwt_cache()
        raise CloudFallbackError(f"Cloud auth error ({resp.status_code})")

    if resp.status_code >= 500:
        raise CloudFallbackError(f"Cloud server error ({resp.status_code})")

    if resp.status_code != 200:
        try:
            err_data = resp.json()
        except Exception:
            err_data = resp.text
        raise CloudInvocationError(f"Cloud error {resp.status_code}: {err_data}")

    data = resp.json()
    return {
        "result": data.get("result"),
        "cost": float(data.get("totalCost", 0)),
        "model_name": data.get("modelName", "cloud"),
        "thinking_output": data.get("thinkingOutput"),
    }


# ─── Core Invocation Logic ─────────────────────────────────────────────────────


def _build_messages(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    idx: Optional[int] = None,
) -> List[Dict[str, str]]:
    """Build chat messages from prompt template and input_json."""
    if not prompt:
        return [{"role": "user", "content": ""}]

    content = prompt
    if input_json:
        vars_dict = input_json if isinstance(input_json, dict) else (input_json[idx] if idx is not None else input_json[0])  # type: ignore[index]
        try:
            content = prompt.format(**vars_dict)
        except (KeyError, IndexError) as exc:
            logger.warning("Template formatting error: %s. Using raw prompt.", exc)

    return [{"role": "user", "content": content}]


def _invoke_single(
    model_row: Dict[str, Any],
    messages: List[Dict[str, Any]],
    temperature: float,
    reasoning_params: Dict[str, Any],
    response_format: Optional[Dict[str, Any]],
    extra_body: Optional[Dict[str, Any]],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
) -> Dict[str, Any]:
    """Invoke LLM for a single request against one model candidate."""
    model_name = str(model_row["model"])
    provider = str(model_row.get("provider", "")).lower()

    call_kwargs: Dict[str, Any] = {
        "model": model_name,
        "messages": messages,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    # Temperature handling
    is_anthropic_thinking = (
        "thinking" in reasoning_params
        and ("claude" in model_name.lower() or "anthropic" in provider)
    )
    is_gpt5 = model_name.startswith("gpt-5")

    if is_anthropic_thinking:
        call_kwargs["temperature"] = 1  # Anthropic requires temp=1 with thinking
    elif not is_gpt5:
        call_kwargs["temperature"] = temperature

    # Vertex AI credentials
    if _is_vertex_model(provider, model_name):
        vertex_creds = _get_vertex_credentials()
        call_kwargs.update(vertex_creds)
        # Per-model location override
        model_location = str(model_row.get("location", "")).strip()
        if model_location:
            call_kwargs["vertex_location"] = model_location

    # LM Studio
    if "lm-studio" in model_name.lower() or "lm_studio" in provider:
        base_url = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
        call_kwargs["api_key"] = "lm-studio"
        call_kwargs["base_url"] = base_url

    # Custom base_url from CSV
    csv_base_url = str(model_row.get("base_url", "")).strip()
    if csv_base_url and "base_url" not in call_kwargs:
        call_kwargs["base_url"] = csv_base_url

    # API key from env (for non-Vertex, non-LM-Studio)
    key_name = str(model_row.get("api_key", "")).strip()
    if key_name and key_name.upper() != "EXISTING_KEY" and "api_key" not in call_kwargs:
        key_val = os.getenv(key_name, "")
        if key_val and not key_name.upper().startswith("VERTEX"):
            call_kwargs["api_key"] = key_val

    # Reasoning params
    filtered_reasoning = {
        k: v for k, v in reasoning_params.items() if not k.startswith("_")
    }
    call_kwargs.update(filtered_reasoning)

    # Response format
    if response_format:
        call_kwargs["response_format"] = response_format
    if extra_body:
        call_kwargs["extra_body"] = extra_body

    # OpenAI gpt-5* → Responses API
    if is_gpt5 and "_reasoning_for_responses" in reasoning_params:
        return _invoke_responses_api(
            model_name=model_name,
            messages=messages,
            reasoning_params=reasoning_params,
            output_pydantic=output_pydantic,
            output_schema=output_schema,
            language=language,
            call_kwargs=call_kwargs,
        )

    # Standard completion
    logger.debug("Calling litellm.completion with model=%s", model_name)
    response = litellm.completion(**call_kwargs)
    return _process_response(
        response,
        output_pydantic=output_pydantic,
        output_schema=output_schema,
        language=language,
        model_name=model_name,
    )


def _invoke_responses_api(
    model_name: str,
    messages: List[Dict[str, Any]],
    reasoning_params: Dict[str, Any],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
    call_kwargs: Dict[str, Any],
) -> Dict[str, Any]:
    """Invoke using the OpenAI Responses API for gpt-5* models."""
    reasoning_cfg = reasoning_params.get("_reasoning_for_responses", {})

    responses_kwargs: Dict[str, Any] = {
        "model": model_name,
        "input": messages,
        "reasoning": reasoning_cfg,
    }

    # Build text format block
    if output_pydantic or output_schema:
        if output_pydantic:
            raw_schema = output_pydantic.model_json_schema()
            schema_name = output_pydantic.__name__
        else:
            raw_schema = output_schema  # type: ignore[assignment]
            schema_name = raw_schema.get("title", "response_schema")  # type: ignore[union-attr]

        processed = _ensure_all_properties_required(raw_schema)  # type: ignore[arg-type]
        processed = _add_additional_properties_false(processed)
        processed.pop("title", None)

        responses_kwargs["text"] = {
            "format": {
                "type": "json_schema",
                "name": schema_name,
                "schema": processed,
                "strict": True,
            }
        }
    else:
        responses_kwargs["text"] = {"format": {"type": "text"}}

    # Pass api_key if available
    if "api_key" in call_kwargs:
        responses_kwargs["api_key"] = call_kwargs["api_key"]

    try:
        response = litellm.responses(**responses_kwargs)  # type: ignore[attr-defined]
    except AttributeError:
        # litellm doesn't have responses() – fallback to completion
        logger.warning("litellm.responses() not available, falling back to completion")
        call_kwargs.pop("temperature", None)  # Skip temp for responses-style models
        if reasoning_cfg:
            call_kwargs["reasoning_effort"] = reasoning_cfg.get("effort", "medium")
        response = litellm.completion(**call_kwargs)
        return _process_response(
            response, output_pydantic, output_schema, language, model_name
        )

    return _process_response(
        response, output_pydantic, output_schema, language, model_name,
        is_responses_api=True,
    )


def _invoke_batch(
    model_row: Dict[str, Any],
    all_messages: List[List[Dict[str, Any]]],
    temperature: float,
    reasoning_params: Dict[str, Any],
    response_format: Optional[Dict[str, Any]],
    extra_body: Optional[Dict[str, Any]],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
) -> Dict[str, Any]:
    """Invoke batch completion for multiple message sets."""
    model_name = str(model_row["model"])
    provider = str(model_row.get("provider", "")).lower()

    call_kwargs: Dict[str, Any] = {
        "model": model_name,
        "messages": all_messages,
        "temperature": temperature,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    # Vertex AI credentials
    if _is_vertex_model(provider, model_name):
        vertex_creds = _get_vertex_credentials()
        call_kwargs.update(vertex_creds)
        model_location = str(model_row.get("location", "")).strip()
        if model_location:
            call_kwargs["vertex_location"] = model_location

    # API key
    key_name = str(model_row.get("api_key", "")).strip()
    if key_name and key_name.upper() != "EXISTING_KEY":
        key_val = os.getenv(key_name, "")
        if key_val and not key_name.upper().startswith("VERTEX"):
            call_kwargs["api_key"] = key_val

    csv_base_url = str(model_row.get("base_url", "")).strip()
    if csv_base_url:
        call_kwargs["base_url"] = csv_base_url

    filtered_reasoning = {k: v for k, v in reasoning_params.items() if not k.startswith("_")}
    call_kwargs.update(filtered_reasoning)

    if response_format:
        call_kwargs["response_format"] = response_format
    if extra_body:
        call_kwargs["extra_body"] = extra_body

    logger.debug("Calling litellm.batch_completion with model=%s, batch_size=%d", model_name, len(all_messages))
    responses = litellm.batch_completion(**call_kwargs)

    results: List[Any] = []
    total_cost = 0.0
    thinking_outputs: List[Optional[str]] = []

    for resp in responses:
        processed = _process_response(
            resp, output_pydantic, output_schema, language, model_name
        )
        results.append(processed["result"])
        total_cost += processed.get("cost", 0.0)
        thinking_outputs.append(processed.get("thinking_output"))

    return {
        "result": results,
        "cost": total_cost,
        "model_name": model_name,
        "thinking_output": thinking_outputs,
    }


def _is_auth_error(exc: Exception) -> bool:
    """Check if exception is an authentication error."""
    msg = str(exc).lower()
    return any(kw in msg for kw in ("401", "403", "unauthorized", "authentication", "invalid api key", "invalid_api_key", "authenticationerror"))


def _is_temperature_thinking_error(exc: Exception) -> bool:
    """Check if error is about temperature incompatibility with thinking."""
    msg = str(exc).lower()
    return "temperature" in msg and ("thinking" in msg or "budget" in msg)


# ─── Main Entry Point ──────────────────────────────────────────────────────────


def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    time: float = DEFAULT_TIME,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    """Invoke an LLM with prompt/input or pre-formatted messages.

    Returns a dict with keys: result, cost, model_name, thinking_output.
    """
    _ensure_initialized()

    if verbose:
        set_verbose_logging(True)
        logger.debug(
            "llm_invoke called: strength=%.2f, temperature=%.2f, time=%.2f, "
            "use_batch_mode=%s, use_cloud=%s",
            strength, temperature, time, use_batch_mode, use_cloud,
        )

    # ── Cloud Execution Path ────────────────────────────────────────────────
    should_try_cloud = False
    if use_cloud is True:
        should_try_cloud = True
    elif use_cloud is None:
        if os.getenv("PDD_FORCE_LOCAL", "0") != "1":
            if CloudConfig is not None:
                try:
                    should_try_cloud = CloudConfig.is_cloud_enabled()
                except Exception:
                    should_try_cloud = False

    if should_try_cloud:
        cloud_schema: Optional[Dict[str, Any]] = None
        if output_pydantic:
            cloud_schema = _pydantic_to_json_schema(output_pydantic)
        elif output_schema:
            cloud_schema = output_schema

        try:
            cloud_result = _llm_invoke_cloud(
                prompt=prompt,
                input_json=input_json,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                output_schema=cloud_schema,
                time_param=time,
                use_batch_mode=use_batch_mode,
                messages=messages,
                language=language,
            )
            # Validate with pydantic if specified
            if output_pydantic and cloud_result.get("result") is not None:
                try:
                    cloud_result["result"] = _validate_with_pydantic(
                        cloud_result["result"], output_pydantic
                    )
                except Exception as exc:
                    logger.warning("Cloud result pydantic validation failed: %s", exc)

            return cloud_result

        except InsufficientCreditsError:
            raise

        except CloudFallbackError as exc:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {exc}[/yellow]")
            logger.warning("Cloud fallback: %s", exc)

        except CloudInvocationError as exc:
            console.print(f"[yellow]Cloud error, falling back to local: {exc}[/yellow]")
            logger.warning("Cloud invocation error: %s", exc)

    # ── Local Execution Path ────────────────────────────────────────────────

    # Determine batch mode
    is_batch = use_batch_mode or (
        isinstance(input_json, list) and len(input_json) > 1 and messages is None
    )

    # Build messages
    if messages is not None:
        if is_batch:
            if isinstance(messages, list) and messages and isinstance(messages[0], list):
                all_message_sets: List[List[Dict[str, Any]]] = messages  # type: ignore[assignment]
            else:
                all_message_sets = [messages]  # type: ignore[list-item]
            working_messages = all_message_sets[0]  # type: ignore[index]
        else:
            working_messages = messages  # type: ignore[assignment]
    else:
        if is_batch and isinstance(input_json, list):
            all_message_sets = [_build_messages(prompt, input_json, i) for i in range(len(input_json))]
            working_messages = all_message_sets[0]
        else:
            working_messages = _build_messages(prompt, input_json)

    # Select model candidates
    candidates = _select_model_candidates(strength, use_cloud)

    if not candidates:
        raise RuntimeError("No model candidates available.")

    last_error: Optional[Exception] = None

    for candidate in candidates:
        model_name = str(candidate["model"])
        key_name = str(candidate.get("api_key", "")).strip()

        # Check API key
        if not _check_and_acquire_api_key(key_name, model_name):
            continue

        # Build reasoning params
        reasoning_params = _build_reasoning_params(candidate, time)

        # Build structured output format
        response_format, extra_body, working_messages_final = _build_response_format(
            candidate, output_pydantic, output_schema, working_messages
        )

        max_attempts = 3
        for attempt in range(max_attempts):
            try:
                if is_batch and messages is not None or (is_batch and isinstance(input_json, list)):
                    # Re-build response format for batch messages if needed
                    batch_messages = []
                    for msg_set in all_message_sets:
                        _, _, modified_msgs = _build_response_format(
                            candidate, output_pydantic, output_schema, msg_set
                        )
                        batch_messages.append(modified_msgs)
                    result = _invoke_batch(
                        model_row=candidate,
                        all_messages=batch_messages,
                        temperature=temperature,
                        reasoning_params=reasoning_params,
                        response_format=response_format,
                        extra_body=extra_body,
                        output_pydantic=output_pydantic,
                        output_schema=output_schema,
                        language=language,
                    )
                else:
                    result = _invoke_single(
                        model_row=candidate,
                        messages=working_messages_final,
                        temperature=temperature,
                        reasoning_params=reasoning_params,
                        response_format=response_format,
                        extra_body=extra_body,
                        output_pydantic=output_pydantic,
                        output_schema=output_schema,
                        language=language,
                    )

                if verbose:
                    logger.debug(
                        "Success with model=%s, cost=%.6f",
                        result["model_name"], result.get("cost", 0),
                    )
                return result

            except SchemaValidationError as exc:
                logger.warning("Schema validation error with %s: %s", model_name, exc)
                last_error = exc
                break  # Try next model candidate

            except ValueError as exc:
                err_msg = str(exc)
                if "None" in err_msg or "retry" in err_msg.lower() or "truncated" in err_msg.lower():
                    if attempt < max_attempts - 1:
                        logger.info(
                            "Retrying %s (attempt %d/%d): %s",
                            model_name, attempt + 2, max_attempts, exc,
                        )
                        # Cache bypass: slightly modify the prompt
                        if working_messages_final and working_messages_final[-1].get("role") == "user":
                            working_messages_final = list(working_messages_final)
                            working_messages_final[-1] = dict(working_messages_final[-1])
                            working_messages_final[-1]["content"] += " "
                        continue
                    last_error = exc
                    break
                last_error = exc
                break

            except Exception as exc:
                if _is_auth_error(exc):
                    if key_name in _newly_acquired_keys:
                        # Re-prompt for key
                        _newly_acquired_keys.discard(key_name)
                        if _detect_wsl():
                            console.print(
                                "[yellow]WSL detected – ensure API key has no carriage returns.[/yellow]"
                            )
                        console.print(
                            f"[red]Authentication failed for {model_name}. "
                            f"Key {key_name} may be invalid.[/red]"
                        )
                        try:
                            raw = input(f"Re-enter {key_name}: ")
                            new_key = _sanitize_api_key(raw)
                            if new_key:
                                os.environ[key_name] = new_key
                                _newly_acquired_keys.add(key_name)
                                _save_key_to_dotenv(key_name, new_key)
                                continue
                        except (EOFError, KeyboardInterrupt):
                            pass
                    last_error = exc
                    break  # Try next model

                if _is_temperature_thinking_error(exc):
                    # Anthropic: force temperature=1 and retry
                    logger.info("Adjusting temperature for thinking model %s", model_name)
                    temperature = 1.0
                    if attempt < max_attempts - 1:
                        continue

                logger.warning("Error with model %s: %s", model_name, exc)
                last_error = exc
                if attempt < max_attempts - 1:
                    continue
                break

    raise RuntimeError(
        f"All model candidates exhausted. Last error: {last_error}"
    )