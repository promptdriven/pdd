from __future__ import annotations

import ast
import json
import logging
import os
import re
import sys
import time as time_module
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Type, Union

import litellm
import pandas as pd
from dotenv import load_dotenv, set_key
from pydantic import BaseModel, ValidationError
from rich.console import Console

from .path_resolution import get_default_resolver

try:
    from . import DEFAULT_STRENGTH, DEFAULT_TIME
except ImportError:
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = 0.25

# ---------------------------------------------------------------------------
# Module-level state
# ---------------------------------------------------------------------------

console = Console(stderr=True)
logger = logging.getLogger("pdd.llm_invoke")
_litellm_logger = logging.getLogger("litellm")

LLM_CALL_TIMEOUT: int = 120
_CLOUD_TIMEOUT: int = 300

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_NEWLY_ACQUIRED_KEYS: Set[str] = set()
_IS_WSL: Optional[bool] = None
_CACHE_INITIALIZED: bool = False
_ENV_LOADED: bool = False
_CSV_DF: Optional[pd.DataFrame] = None

_PROSE_FIELD_NAMES: Set[str] = {
    "reasoning",
    "explanation",
    "analysis",
    "thought_process",
    "thinking",
    "rationale",
    "justification",
    "summary",
    "description",
    "notes",
    "comments",
}


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------


class SchemaValidationError(Exception):
    """Raised when structured output fails schema validation, triggers model fallback."""


class CloudFallbackError(Exception):
    """Recoverable cloud error (network, timeout, auth, 5xx). Falls back to local."""


class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""


class InsufficientCreditsError(Exception):
    """402 Payment Required. Does NOT fall back to local."""


# ---------------------------------------------------------------------------
# Logging setup
# ---------------------------------------------------------------------------


def _setup_logging() -> None:
    """Configure logging based on environment variables."""
    pdd_env = os.getenv("PDD_ENVIRONMENT", "").lower()
    verbose = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"

    if verbose:
        default_level = "DEBUG"
    elif pdd_env == "production":
        default_level = "WARNING"
    else:
        default_level = "INFO"

    pdd_level_name = os.getenv("PDD_LOG_LEVEL", default_level).upper()
    pdd_level = getattr(logging, pdd_level_name, logging.INFO)
    logger.setLevel(pdd_level)

    if not logger.handlers:
        handler = logging.StreamHandler(sys.stderr)
        handler.setFormatter(
            logging.Formatter("%(asctime)s [%(name)s] %(levelname)s: %(message)s")
        )
        logger.addHandler(handler)

    litellm_level_name = os.getenv(
        "LITELLM_LOG_LEVEL",
        "WARNING" if pdd_env == "production" else "WARNING",
    ).upper()
    litellm_level = getattr(logging, litellm_level_name, logging.WARNING)
    _litellm_logger.setLevel(litellm_level)


def setup_file_logging(log_dir: Optional[Path] = None) -> None:
    """Add rotating file handler (10 MB, 5 backups)."""
    if log_dir is None:
        log_dir = _get_project_root() / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    fh = RotatingFileHandler(
        log_dir / "pdd_llm_invoke.log",
        maxBytes=10 * 1024 * 1024,
        backupCount=5,
    )
    fh.setFormatter(
        logging.Formatter("%(asctime)s [%(name)s] %(levelname)s: %(message)s")
    )
    logger.addHandler(fh)


def set_verbose_logging(enabled: bool = True) -> None:
    """Toggle DEBUG level on the pdd.llm_invoke logger."""
    logger.setLevel(logging.DEBUG if enabled else logging.INFO)


# ---------------------------------------------------------------------------
# WSL detection
# ---------------------------------------------------------------------------


def _detect_wsl() -> bool:
    """Detect if running under WSL."""
    global _IS_WSL
    if _IS_WSL is not None:
        return _IS_WSL
    if os.getenv("WSL_DISTRO_NAME"):
        _IS_WSL = True
        return True
    try:
        with open("/proc/version", "r") as f:
            content = f.read().lower()
        _IS_WSL = "microsoft" in content or "wsl" in content
    except OSError:
        _IS_WSL = False
    return _IS_WSL


def _sanitize_api_key(key: str) -> str:
    """Strip whitespace and control characters from API key."""
    return key.strip().replace("\r", "").replace("\n", "")


# ---------------------------------------------------------------------------
# Environment & path resolution
# ---------------------------------------------------------------------------


def _get_project_root() -> Path:
    resolver = get_default_resolver()
    return resolver.resolve_project_root()


def _ensure_env_loaded() -> None:
    global _ENV_LOADED
    if _ENV_LOADED:
        return
    try:
        root = _get_project_root()
        env_path = root / ".env"
        if env_path.exists():
            load_dotenv(env_path, override=False)
    except Exception:
        load_dotenv(override=False)
    _ENV_LOADED = True


def _resolve_model_csv_path() -> Path:
    """Resolve llm_model.csv in priority order."""
    # (a) ~/.pdd/llm_model.csv
    home_csv = Path.home() / ".pdd" / "llm_model.csv"
    if home_csv.exists():
        return home_csv

    # (b) <PROJECT_ROOT>/.pdd/llm_model.csv if PDD_PATH points to real project
    pdd_path_env = os.environ.get("PDD_PATH")
    if pdd_path_env:
        pdd_path = Path(pdd_path_env).resolve()
        pkg_path = Path(__file__).resolve().parent
        if not str(pdd_path).startswith(str(pkg_path)):
            candidate = pdd_path / ".pdd" / "llm_model.csv"
            if candidate.exists():
                return candidate

    # Try project root
    try:
        root = _get_project_root()
        root_csv = root / ".pdd" / "llm_model.csv"
        if root_csv.exists():
            return root_csv
    except Exception:
        pass

    # (c) <cwd>/.pdd/llm_model.csv
    cwd_csv = Path.cwd() / ".pdd" / "llm_model.csv"
    if cwd_csv.exists():
        return cwd_csv

    # (d) packaged pdd/data/llm_model.csv
    pkg_csv = Path(__file__).resolve().parent / "data" / "llm_model.csv"
    if pkg_csv.exists():
        return pkg_csv

    raise FileNotFoundError(
        "Cannot locate llm_model.csv. Searched: ~/.pdd/, project .pdd/, cwd .pdd/, package data/"
    )


# ---------------------------------------------------------------------------
# CSV loading
# ---------------------------------------------------------------------------


def _load_model_csv(force_reload: bool = False) -> pd.DataFrame:
    """Load and cache the model CSV, build rate map."""
    global _CSV_DF, _MODEL_RATE_MAP
    if _CSV_DF is not None and not force_reload:
        return _CSV_DF

    csv_path = _resolve_model_csv_path()
    logger.debug("Loading model CSV from %s", csv_path)
    df = pd.read_csv(csv_path)

    # Normalize column names
    df.columns = [c.strip().lower() for c in df.columns]

    # Ensure required columns
    required = {"model", "provider", "input", "output", "api_key"}
    missing = required - set(df.columns)
    if missing:
        raise ValueError(f"Model CSV missing columns: {missing}")

    # Fill optional columns
    for col, default in [
        ("coding_arena_elo", 0),
        ("structured_output", False),
        ("reasoning_type", "none"),
        ("max_reasoning_tokens", 0),
        ("base_url", ""),
        ("location", ""),
    ]:
        if col not in df.columns:
            df[col] = default

    df["coding_arena_elo"] = pd.to_numeric(df["coding_arena_elo"], errors="coerce").fillna(0).astype(int)
    df["input"] = pd.to_numeric(df["input"], errors="coerce").fillna(0.0)
    df["output"] = pd.to_numeric(df["output"], errors="coerce").fillna(0.0)
    df["max_reasoning_tokens"] = pd.to_numeric(df["max_reasoning_tokens"], errors="coerce").fillna(0).astype(int)
    df["structured_output"] = df["structured_output"].astype(str).str.strip().str.lower().isin(["true", "1", "yes"])
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.strip().str.lower()
    df["base_url"] = df["base_url"].fillna("").astype(str).str.strip()
    df["location"] = df["location"].fillna("").astype(str).str.strip()
    df["api_key"] = df["api_key"].fillna("").astype(str).str.strip()
    df["provider"] = df["provider"].fillna("").astype(str).str.strip()

    # Build rate map
    _MODEL_RATE_MAP = {}
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row["model"]] = {
            "input": float(row["input"]),
            "output": float(row["output"]),
        }

    _CSV_DF = df
    return df


# ---------------------------------------------------------------------------
# API key management
# ---------------------------------------------------------------------------


def _check_api_key(key_name: str) -> Optional[str]:
    """Return the API key value if set, else None."""
    if not key_name or key_name.upper() == "EXISTING_KEY":
        return "EXISTING_KEY"
    val = os.getenv(key_name)
    if val:
        return _sanitize_api_key(val)
    return None


def _prompt_for_api_key(key_name: str) -> Optional[str]:
    """Interactively prompt the user for an API key, save to .env."""
    if os.getenv("PDD_FORCE"):
        logger.debug("PDD_FORCE set, skipping interactive key prompt for %s", key_name)
        return None

    console.print(
        f"\n[bold yellow]API key [cyan]{key_name}[/cyan] is not set.[/bold yellow]"
    )
    try:
        raw = input(f"Enter value for {key_name} (or press Enter to skip): ")
    except (EOFError, KeyboardInterrupt):
        console.print("[dim]Skipped.[/dim]")
        return None

    raw = raw.strip()
    if not raw:
        return None

    key_value = _sanitize_api_key(raw)
    os.environ[key_name] = key_value

    # Save to .env
    try:
        root = _get_project_root()
        env_path = root / ".env"
        _save_key_to_env(env_path, key_name, key_value)
        console.print(
            f"[bold green]✓[/bold green] Saved [cyan]{key_name}[/cyan] to {env_path}"
        )
        logger.warning(
            "Security: API key %s saved to %s. Ensure this file is in .gitignore.",
            key_name,
            env_path,
        )
    except Exception as exc:
        logger.warning("Could not save key to .env: %s", exc)

    _NEWLY_ACQUIRED_KEYS.add(key_name)
    return key_value


def _save_key_to_env(env_path: Path, key_name: str, key_value: str) -> None:
    """Save key to .env file, replacing existing entries in-place."""
    env_path.parent.mkdir(parents=True, exist_ok=True)

    if env_path.exists():
        lines = env_path.read_text().splitlines()
    else:
        lines = []

    # Remove old entries (including commented versions)
    pattern = re.compile(rf"^\s*#?\s*{re.escape(key_name)}\s*=")
    new_lines = [line for line in lines if not pattern.match(line)]

    # Use set_key from dotenv for proper formatting
    new_lines.append(f'{key_name}="{key_value}"')
    env_path.write_text("\n".join(new_lines) + "\n")


def _ensure_api_key_for_model(row: pd.Series) -> bool:
    """Ensure API key is available for a model. Returns True if ready."""
    key_name = str(row.get("api_key", "")).strip()
    if not key_name or key_name.upper() == "EXISTING_KEY":
        return True

    val = _check_api_key(key_name)
    if val:
        return True

    prompted = _prompt_for_api_key(key_name)
    return prompted is not None


# ---------------------------------------------------------------------------
# Model selection
# ---------------------------------------------------------------------------


def _get_available_models(df: pd.DataFrame) -> pd.DataFrame:
    """Filter to models whose API keys are available."""
    available_indices: List[int] = []
    for idx, row in df.iterrows():
        key_name = str(row.get("api_key", "")).strip()
        if not key_name or key_name.upper() == "EXISTING_KEY":
            available_indices.append(idx)  # type: ignore[arg-type]
        elif os.getenv(key_name):
            available_indices.append(idx)  # type: ignore[arg-type]
    return df.loc[available_indices].copy()


def _select_model_candidates(
    df: pd.DataFrame, strength: float
) -> List[pd.Series]:
    """Select ordered list of model candidates based on strength.

    strength < 0.5  → interpolate by cost from base down to cheapest.
    strength > 0.5  → interpolate by ELO from base up to highest.
    strength == 0.5 → base model, fallback to next highest ELO.
    """
    if df.empty:
        return []

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")

    # Find base model row
    base_row: Optional[pd.Series] = None
    if base_model_name:
        matches = df[df["model"] == base_model_name]
        if not matches.empty:
            base_row = matches.iloc[0]

    # Soft fallback: use first available as surrogate
    if base_row is None:
        base_row = df.iloc[0]

    # Compute composite cost for sorting
    df = df.copy()
    df["_cost"] = df["input"] + df["output"]

    # Sort by ELO descending for high-strength, by cost ascending for low-strength
    if abs(strength - 0.5) < 1e-9:
        # strength == 0.5 → base model first, then by ELO descending
        candidates = [base_row]
        others = df[df["model"] != base_row["model"]].sort_values(
            "coding_arena_elo", ascending=False
        )
        for _, row in others.iterrows():
            candidates.append(row)
        return candidates

    if strength < 0.5:
        # Interpolate by cost: lower strength → cheaper models
        sorted_df = df.sort_values("_cost", ascending=True)
        models_list = [row for _, row in sorted_df.iterrows()]

        base_idx = None
        for i, m in enumerate(models_list):
            if m["model"] == base_row["model"]:
                base_idx = i
                break

        if base_idx is None:
            base_idx = len(models_list) - 1

        # Fraction from cheapest (0.0) to base (0.5)
        frac = strength / 0.5
        target_idx = int(round((1 - frac) * 0 + frac * base_idx))
        target_idx = max(0, min(target_idx, len(models_list) - 1))

        # Build candidates centered on target
        candidates = [models_list[target_idx]]
        for offset in range(1, len(models_list)):
            for idx in [target_idx - offset, target_idx + offset]:
                if 0 <= idx < len(models_list):
                    row = models_list[idx]
                    if row["model"] != candidates[0]["model"]:
                        candidates.append(row)
        return candidates

    else:
        # strength > 0.5: interpolate by ELO from base up to highest
        sorted_df = df.sort_values("coding_arena_elo", ascending=True)
        models_list = [row for _, row in sorted_df.iterrows()]

        base_idx = None
        for i, m in enumerate(models_list):
            if m["model"] == base_row["model"]:
                base_idx = i
                break

        if base_idx is None:
            base_idx = 0

        # Fraction from base (0.5) to highest ELO (1.0)
        frac = (strength - 0.5) / 0.5
        highest_idx = len(models_list) - 1
        target_idx = int(round((1 - frac) * base_idx + frac * highest_idx))
        target_idx = max(0, min(target_idx, highest_idx))

        # Build candidates: target first, then descending ELO
        candidates = [models_list[target_idx]]
        for offset in range(1, len(models_list)):
            for idx in [target_idx + offset, target_idx - offset]:
                if 0 <= idx < len(models_list):
                    row = models_list[idx]
                    if not any(c["model"] == row["model"] for c in candidates):
                        candidates.append(row)
        return candidates


# ---------------------------------------------------------------------------
# Schema helpers
# ---------------------------------------------------------------------------


def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively ensure ALL properties are listed in required arrays."""
    if not isinstance(schema, dict):
        return schema

    if "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop_schema in schema["properties"].values():
            _ensure_all_properties_required(prop_schema)

    if "items" in schema:
        _ensure_all_properties_required(schema["items"])

    for keyword in ("anyOf", "oneOf", "allOf"):
        if keyword in schema:
            for sub in schema[keyword]:
                _ensure_all_properties_required(sub)

    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            _ensure_all_properties_required(def_schema)

    if "definitions" in schema:
        for def_schema in schema["definitions"].values():
            _ensure_all_properties_required(def_schema)

    return schema


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively add additionalProperties: false on ALL object schemas."""
    if not isinstance(schema, dict):
        return schema

    if schema.get("type") == "object" or "properties" in schema:
        schema["additionalProperties"] = False

    if "properties" in schema:
        for prop_schema in schema["properties"].values():
            _add_additional_properties_false(prop_schema)

    if "items" in schema:
        _add_additional_properties_false(schema["items"])

    for keyword in ("anyOf", "oneOf", "allOf"):
        if keyword in schema:
            for sub in schema[keyword]:
                _add_additional_properties_false(sub)

    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            _add_additional_properties_false(def_schema)

    if "definitions" in schema:
        for def_schema in schema["definitions"].values():
            _add_additional_properties_false(def_schema)

    return schema


def _prepare_json_schema(
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
) -> Optional[Dict[str, Any]]:
    """Build a strict JSON schema from pydantic model or raw schema."""
    if output_pydantic is not None:
        schema = output_pydantic.model_json_schema()
        name = output_pydantic.__name__
    elif output_schema is not None:
        schema = dict(output_schema)
        name = schema.pop("title", "output_schema")
    else:
        return None

    schema = _ensure_all_properties_required(schema)
    schema = _add_additional_properties_false(schema)

    return {
        "type": "json_schema",
        "json_schema": {
            "name": name,
            "schema": schema,
            "strict": True,
        },
    }


# ---------------------------------------------------------------------------
# Reasoning parameter builders
# ---------------------------------------------------------------------------


def _build_reasoning_params(
    model_row: pd.Series, time_val: float
) -> Dict[str, Any]:
    """Build reasoning parameters based on model's reasoning_type."""
    reasoning_type = str(model_row.get("reasoning_type", "none")).lower()
    max_tokens = int(model_row.get("max_reasoning_tokens", 0))
    extra_params: Dict[str, Any] = {}

    if reasoning_type == "budget" and max_tokens > 0:
        budget_tokens = int(time_val * max_tokens)
        budget_tokens = max(1024, budget_tokens)  # minimum reasonable budget
        model_name = str(model_row["model"])
        # Anthropic-style thinking parameter
        if "claude" in model_name.lower() or "anthropic" in str(model_row.get("provider", "")).lower():
            extra_params["thinking"] = {
                "type": "enabled",
                "budget_tokens": budget_tokens,
            }
        else:
            extra_params["thinking"] = {
                "type": "enabled",
                "budget_tokens": budget_tokens,
            }

    elif reasoning_type == "effort":
        if time_val <= 0.33:
            effort = "low"
        elif time_val <= 0.66:
            effort = "medium"
        else:
            effort = "high"

        model_name = str(model_row["model"])
        if model_name.startswith("gpt-5") or model_name.startswith("openai/gpt-5"):
            # Responses API: reasoning param handled separately
            extra_params["_responses_reasoning"] = {
                "effort": effort,
                "summary": "auto",
            }
        else:
            extra_params["reasoning_effort"] = effort

    return extra_params


# ---------------------------------------------------------------------------
# Message building
# ---------------------------------------------------------------------------


def _build_messages(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    """Format prompt with input_json into messages."""
    if prompt is None:
        return [{"role": "user", "content": ""}]

    if input_json is None:
        return [{"role": "user", "content": prompt}]

    if isinstance(input_json, list):
        # Batch mode: return list of message lists
        result: List[List[Dict[str, str]]] = []
        for item in input_json:
            try:
                content = prompt.format(**item)
            except KeyError as e:
                logger.warning("Missing template variable %s, using raw prompt", e)
                content = prompt
            result.append([{"role": "user", "content": content}])
        return result

    try:
        content = prompt.format(**input_json)
    except KeyError as e:
        logger.warning("Missing template variable %s, using raw prompt", e)
        content = prompt

    return [{"role": "user", "content": content}]


# ---------------------------------------------------------------------------
# LiteLLM cache setup
# ---------------------------------------------------------------------------


def _setup_cache() -> None:
    """Configure LiteLLM caching: S3/GCS → SQLite → disabled."""
    global _CACHE_INITIALIZED
    if _CACHE_INITIALIZED:
        return

    if os.getenv("LITELLM_CACHE_DISABLE", "0") == "1":
        logger.debug("LiteLLM caching disabled via LITELLM_CACHE_DISABLE")
        _CACHE_INITIALIZED = True
        return

    # Try S3-compatible (GCS HMAC)
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
            logger.debug("LiteLLM S3/GCS cache configured (bucket=%s)", bucket)
            _CACHE_INITIALIZED = True
            return
        except Exception as e:
            logger.warning("S3/GCS cache setup failed: %s. Falling back to disk.", e)

    # Fall back to disk SQLite cache
    try:
        root = _get_project_root()
        db_path = str(root / "litellm_cache.sqlite")
    except Exception:
        db_path = str(Path.cwd() / "litellm_cache.sqlite")

    try:
        litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(Path(db_path).parent))
        logger.debug("LiteLLM disk cache at %s", db_path)
    except Exception as e:
        logger.warning("Disk cache setup failed: %s", e)

    _CACHE_INITIALIZED = True


# ---------------------------------------------------------------------------
# LiteLLM callback
# ---------------------------------------------------------------------------


def _litellm_success_callback(
    kwargs: Dict[str, Any],
    completion_response: Any,
    start_time: Any,
    end_time: Any,
) -> None:
    """Success callback to capture cost and usage data."""
    global _LAST_CALLBACK_DATA

    usage: Dict[str, int] = {}
    finish_reason: str = ""
    model_name: str = kwargs.get("model", "")

    try:
        if hasattr(completion_response, "usage") and completion_response.usage:
            u = completion_response.usage
            usage = {
                "prompt_tokens": getattr(u, "prompt_tokens", 0) or 0,
                "completion_tokens": getattr(u, "completion_tokens", 0) or 0,
                "total_tokens": getattr(u, "total_tokens", 0) or 0,
            }

        if hasattr(completion_response, "choices") and completion_response.choices:
            finish_reason = getattr(
                completion_response.choices[0], "finish_reason", ""
            ) or ""
    except Exception:
        pass

    # Calculate cost
    cost = 0.0
    try:
        cost = litellm.completion_cost(completion_response=completion_response)
    except Exception:
        # Fall back to CSV rates
        if model_name in _MODEL_RATE_MAP and usage:
            rates = _MODEL_RATE_MAP[model_name]
            prompt_cost = (usage.get("prompt_tokens", 0) / 1_000_000) * rates["input"]
            completion_cost = (usage.get("completion_tokens", 0) / 1_000_000) * rates["output"]
            cost = prompt_cost + completion_cost
            logger.debug("Cost from CSV rates for %s: %.6f", model_name, cost)

    _LAST_CALLBACK_DATA = {
        "usage": usage,
        "finish_reason": finish_reason,
        "cost": cost,
        "model": model_name,
    }


def _register_callback() -> None:
    """Register the success callback if not already registered."""
    if _litellm_success_callback not in litellm.success_callback:
        litellm.success_callback.append(_litellm_success_callback)  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# Vertex AI helpers
# ---------------------------------------------------------------------------


def _is_vertex_model(model_row: pd.Series) -> bool:
    """Detect if model uses Vertex AI."""
    model_name = str(model_row.get("model", ""))
    provider = str(model_row.get("provider", "")).lower()
    return (
        model_name.startswith("vertex_ai/")
        or model_name.startswith("vertex_ai_beta/")
        or provider in ("google", "vertex_ai")
        and "vertex" in model_name.lower()
    )


def _get_vertex_credentials(model_row: pd.Series) -> Dict[str, Any]:
    """Load Vertex AI credentials and project info."""
    params: Dict[str, Any] = {}
    creds_path = os.getenv("VERTEX_CREDENTIALS", "")

    key_name = str(model_row.get("api_key", ""))
    if key_name == "VERTEX_CREDENTIALS":
        creds_path = os.getenv("VERTEX_CREDENTIALS", creds_path)

    if creds_path and Path(creds_path).exists():
        try:
            creds_json = Path(creds_path).read_text()
            params["vertex_credentials"] = creds_json
        except Exception as e:
            logger.warning("Failed to read Vertex credentials: %s", e)

    project = os.getenv("VERTEX_PROJECT", "")
    if project:
        params["vertex_project"] = project

    # Location: per-model override from CSV, then env var
    location = str(model_row.get("location", "")).strip()
    if not location:
        location = os.getenv("VERTEX_LOCATION", "us-central1")
    params["vertex_location"] = location

    return params


# ---------------------------------------------------------------------------
# LM Studio helpers
# ---------------------------------------------------------------------------


def _is_lm_studio_model(model_row: pd.Series) -> bool:
    """Detect if model targets LM Studio."""
    provider = str(model_row.get("provider", "")).lower()
    base_url = str(model_row.get("base_url", "")).lower()
    return "lm_studio" in provider or "lm-studio" in provider or "localhost:1234" in base_url


def _is_groq_model(model_row: pd.Series) -> bool:
    """Detect if model targets Groq."""
    provider = str(model_row.get("provider", "")).lower()
    model_name = str(model_row.get("model", "")).lower()
    return "groq" in provider or model_name.startswith("groq/")


def _is_gpt5_model(model_name: str) -> bool:
    """Detect gpt-5* models for Responses API."""
    clean = model_name.lower().replace("openai/", "")
    return clean.startswith("gpt-5")


# ---------------------------------------------------------------------------
# Cloud execution
# ---------------------------------------------------------------------------


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    """Convert Pydantic model to JSON Schema for cloud transport."""
    schema = pydantic_class.model_json_schema()
    schema = _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(
    result: Any, pydantic_class: Type[BaseModel]
) -> BaseModel:
    """Validate cloud response using the Pydantic model."""
    if isinstance(result, str):
        try:
            result = json.loads(result)
        except json.JSONDecodeError:
            raise SchemaValidationError(
                f"Cannot parse cloud result as JSON for {pydantic_class.__name__}"
            )
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    raise SchemaValidationError(
        f"Unexpected result type {type(result)} for {pydantic_class.__name__}"
    )


def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]],
    strength: float,
    temperature: float,
    time_val: float,
    verbose: bool,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    """Execute llm_invoke via cloud endpoint 'llmInvoke'."""
    try:
        from .cloud_config import CloudConfig  # type: ignore[import-untyped]
    except ImportError:
        raise CloudFallbackError("Cloud config module not available")

    config = CloudConfig()
    endpoint_url = config.get_endpoint_url("llmInvoke")
    token = config.get_auth_token()

    if not endpoint_url or not token:
        raise CloudFallbackError("Cloud endpoint or auth token not configured")

    # Build payload
    payload: Dict[str, Any] = {
        "strength": strength,
        "temperature": temperature,
        "time": time_val,
        "verbose": verbose,
        "useBatchMode": use_batch_mode,
    }

    if prompt is not None:
        payload["prompt"] = prompt
    if input_json is not None:
        payload["inputJson"] = input_json
    if messages is not None:
        payload["messages"] = messages
    if language is not None:
        payload["language"] = language

    # Schema for structured output
    if output_pydantic is not None:
        payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema is not None:
        schema_copy = dict(output_schema)
        schema_copy = _ensure_all_properties_required(schema_copy)
        payload["outputSchema"] = schema_copy

    import urllib.request
    import urllib.error

    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {token}",
    }

    req = urllib.request.Request(
        endpoint_url,
        data=json.dumps(payload).encode("utf-8"),
        headers=headers,
        method="POST",
    )

    try:
        with urllib.request.urlopen(req, timeout=_CLOUD_TIMEOUT) as resp:
            body = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as http_err:
        status = http_err.code
        try:
            err_body = json.loads(http_err.read().decode("utf-8"))
            err_msg = err_body.get("error", {}).get("message", str(http_err))
        except Exception:
            err_msg = str(http_err)

        if status == 402:
            raise InsufficientCreditsError(err_msg)
        if status in (401, 403):
            # Clear JWT cache on auth errors
            try:
                config.clear_token_cache()
            except Exception:
                pass
            raise CloudFallbackError(f"Auth error ({status}): {err_msg}")
        if status >= 500:
            raise CloudFallbackError(f"Server error ({status}): {err_msg}")
        raise CloudInvocationError(f"Cloud error ({status}): {err_msg}")
    except (urllib.error.URLError, OSError, TimeoutError) as net_err:
        raise CloudFallbackError(f"Network error: {net_err}")

    # Parse cloud response
    result = body.get("result", "")
    total_cost = body.get("totalCost", 0.0)
    model_name = body.get("modelName", "cloud")
    thinking_output = body.get("thinkingOutput", "")

    # Validate with pydantic if specified
    if output_pydantic is not None and result:
        result = _validate_with_pydantic(result, output_pydantic)

    return {
        "result": result,
        "cost": total_cost,
        "model_name": model_name,
        "thinking_output": thinking_output,
    }


# ---------------------------------------------------------------------------
# JSON parsing & repair
# ---------------------------------------------------------------------------


def _extract_json_from_fenced(text: str) -> Optional[str]:
    """Extract JSON from ```json ... ``` fenced blocks."""
    pattern = re.compile(r"```(?:json)?\s*\n?(.*?)\n?\s*```", re.DOTALL)
    match = pattern.search(text)
    if match:
        return match.group(1).strip()
    return None


def _extract_balanced_json(text: str) -> Optional[str]:
    """Extract first balanced JSON object or array from text."""
    for start_char, end_char in [("{", "}"), ("[", "]")]:
        idx = text.find(start_char)
        if idx == -1:
            continue
        depth = 0
        in_string = False
        escape_next = False
        for i in range(idx, len(text)):
            ch = text[i]
            if escape_next:
                escape_next = False
                continue
            if ch == "\\":
                escape_next = True
                continue
            if ch == '"':
                in_string = not in_string
                continue
            if in_string:
                continue
            if ch == start_char:
                depth += 1
            elif ch == end_char:
                depth -= 1
                if depth == 0:
                    return text[idx : i + 1]
    return None


def _clean_fences(text: str) -> str:
    """Remove markdown code fences from text."""
    text = re.sub(r"^```(?:json)?\s*\n?", "", text, flags=re.MULTILINE)
    text = re.sub(r"\n?\s*```\s*$", "", text, flags=re.MULTILINE)
    return text.strip()


def _repair_truncated_json(text: str) -> Optional[str]:
    """Attempt to repair truncated JSON by closing open brackets/braces."""
    closers = [
        "",
        "}",
        '"}',
        '"]}',
        '"}]',
        '"}]}',
        "]}",
        "]}",
        "]",
        '"]',
        '"}]}',
        '"}}',
    ]
    for closer in closers:
        candidate = text + closer
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            continue

    # Try counting brackets
    opens = text.count("{") - text.count("}") 
    open_brackets = text.count("[") - text.count("]")
    if opens >= 0 and open_brackets >= 0:
        suffix = "]" * open_brackets + "}" * opens
        candidate = text + suffix
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            # Try with closing quote first
            candidate = text + '"' + suffix
            try:
                json.loads(candidate)
                return candidate
            except json.JSONDecodeError:
                pass
    return None


def _parse_json_response(text: str) -> Any:
    """Parse JSON from LLM response with multiple strategies."""
    text = text.strip()

    # Direct parse
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass

    # Fenced block
    fenced = _extract_json_from_fenced(text)
    if fenced:
        try:
            return json.loads(fenced)
        except json.JSONDecodeError:
            repaired = _repair_truncated_json(fenced)
            if repaired:
                try:
                    return json.loads(repaired)
                except json.JSONDecodeError:
                    pass

    # Balanced extraction
    balanced = _extract_balanced_json(text)
    if balanced:
        try:
            return json.loads(balanced)
        except json.JSONDecodeError:
            pass

    # Clean fences and try again
    cleaned = _clean_fences(text)
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError:
        pass

    # Repair truncated
    repaired = _repair_truncated_json(cleaned)
    if repaired:
        try:
            return json.loads(repaired)
        except json.JSONDecodeError:
            pass

    raise json.JSONDecodeError("Failed to parse JSON from response", text, 0)


# ---------------------------------------------------------------------------
# Python validation & repair
# ---------------------------------------------------------------------------


def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines in code fields.

    Preserves \\n inside string literals while converting top-level \\\\n to \\n.
    """
    # Replace \\n outside of string literals
    result: List[str] = []
    i = 0
    in_string = False
    string_char = ""
    while i < len(text):
        ch = text[i]

        if not in_string and ch in ('"', "'"):
            # Check for triple quotes
            triple = text[i : i + 3]
            if triple in ('"""', "'''"):
                in_string = True
                string_char = triple
                result.append(triple)
                i += 3
                continue
            in_string = True
            string_char = ch
            result.append(ch)
            i += 1
            continue

        if in_string:
            if len(string_char) == 3:
                if text[i : i + 3] == string_char:
                    in_string = False
                    result.append(string_char)
                    i += 3
                    continue
            elif ch == string_char and (i == 0 or text[i - 1] != "\\"):
                in_string = False
            result.append(ch)
            i += 1
            continue

        # Outside string: replace \\n with \n
        if text[i : i + 2] == "\\n":
            result.append("\n")
            i += 2
            continue

        result.append(ch)
        i += 1

    return "".join(result)


def _repair_python_syntax(code: str) -> str:
    """Attempt to repair common Python syntax errors."""
    # Fix trailing unmatched quotes
    lines = code.split("\n")
    repaired_lines: List[str] = []
    for line in lines:
        stripped = line.rstrip()
        # Count quotes
        single_count = stripped.count("'") - stripped.count("\\'")
        double_count = stripped.count('"') - stripped.count('\\"')
        if single_count % 2 != 0 and stripped.endswith("'"):
            stripped = stripped + "'"
        if double_count % 2 != 0 and stripped.endswith('"'):
            stripped = stripped + '"'
        repaired_lines.append(stripped)

    return "\n".join(repaired_lines)


def _validate_python_code(code: str) -> bool:
    """Check if code is valid Python by parsing with ast."""
    try:
        ast.parse(code)
        return True
    except SyntaxError:
        return False


def _should_validate_python(
    field_name: str, language: Optional[str]
) -> bool:
    """Determine if a field should be validated as Python code."""
    if language is not None and language.lower() != "python":
        return False
    if field_name.lower() in _PROSE_FIELD_NAMES:
        return False
    return True


# ---------------------------------------------------------------------------
# Response processing
# ---------------------------------------------------------------------------


def _extract_thinking(response: Any) -> str:
    """Extract thinking/reasoning output from response."""
    thinking = ""

    # Check _hidden_params
    try:
        hidden = getattr(response, "_hidden_params", {}) or {}
        if "thinking" in hidden:
            thinking = str(hidden["thinking"])
    except Exception:
        pass

    # Check reasoning_content
    if not thinking:
        try:
            if hasattr(response, "choices") and response.choices:
                msg = response.choices[0].message
                rc = getattr(msg, "reasoning_content", None)
                if rc:
                    thinking = str(rc)
        except Exception:
            pass

    return thinking


def _extract_content(response: Any) -> Optional[str]:
    """Extract text content from LLM response."""
    # Standard completion response
    try:
        if hasattr(response, "choices") and response.choices:
            content = response.choices[0].message.content
            return content
    except (AttributeError, IndexError):
        pass

    # Responses API format
    try:
        if hasattr(response, "output") and response.output:
            for item in response.output:
                if getattr(item, "type", "") == "message":
                    for block in getattr(item, "content", []):
                        if getattr(block, "type", "") in ("output_text", "text"):
                            return getattr(block, "text", None)
    except (AttributeError, TypeError):
        pass

    return None


def _process_structured_response(
    content: str,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
) -> Any:
    """Process and validate structured LLM output."""
    parsed = _parse_json_response(content)

    if output_pydantic is not None:
        try:
            if isinstance(parsed, dict):
                return output_pydantic.model_validate(parsed)
            elif isinstance(parsed, str):
                return output_pydantic.model_validate_json(parsed)
            else:
                return output_pydantic.model_validate(parsed)
        except ValidationError as e:
            raise SchemaValidationError(f"Pydantic validation failed: {e}")

    if output_schema is not None:
        # Basic validation: check it's a dict/list
        return parsed

    return parsed


def _process_code_fields(
    result: Any, language: Optional[str]
) -> Tuple[Any, bool]:
    """Process code fields in result: unescape, repair, validate.

    Returns (processed_result, has_invalid_python).
    """
    has_invalid = False

    if isinstance(result, BaseModel):
        data = result.model_dump()
    elif isinstance(result, dict):
        data = result
    else:
        return result, False

    for field_name, value in data.items():
        if not isinstance(value, str):
            continue

        # Unescape double-escaped newlines in code
        value = _smart_unescape_code(value)
        data[field_name] = value

        if _should_validate_python(field_name, language):
            if not _validate_python_code(value):
                # Try repair
                repaired = _repair_python_syntax(value)
                if _validate_python_code(repaired):
                    data[field_name] = repaired
                else:
                    has_invalid = True

    if isinstance(result, BaseModel):
        try:
            return result.__class__.model_validate(data), has_invalid
        except ValidationError:
            return result, has_invalid

    return data, has_invalid


# ---------------------------------------------------------------------------
# LLM call construction
# ---------------------------------------------------------------------------


def _build_call_kwargs(
    model_row: pd.Series,
    messages: List[Dict[str, Any]],
    temperature: float,
    time_val: float,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
) -> Dict[str, Any]:
    """Build kwargs for litellm.completion()."""
    model_name = str(model_row["model"])
    kwargs: Dict[str, Any] = {
        "model": model_name,
        "messages": messages,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    # Reasoning params
    reasoning_params = _build_reasoning_params(model_row, time_val)
    is_thinking_enabled = "thinking" in reasoning_params

    # Anthropic + thinking: force temperature=1
    is_anthropic = "claude" in model_name.lower() or "anthropic" in str(model_row.get("provider", "")).lower()
    if is_anthropic and is_thinking_enabled:
        kwargs["temperature"] = 1
    else:
        kwargs["temperature"] = temperature

    # Add reasoning params (except _responses_reasoning which is handled by Responses API)
    for k, v in reasoning_params.items():
        if not k.startswith("_"):
            kwargs[k] = v

    # Structured output
    schema_rf = _prepare_json_schema(output_pydantic, output_schema)
    if schema_rf is not None:
        supports_structured = bool(model_row.get("structured_output", False))

        if _is_lm_studio_model(model_row):
            # LM Studio: use extra_body
            kwargs["extra_body"] = {"response_format": schema_rf}
        elif _is_groq_model(model_row):
            # Groq: json_object mode with schema in system prompt
            kwargs["response_format"] = {"type": "json_object"}
            schema_str = json.dumps(
                schema_rf.get("json_schema", {}).get("schema", {}), indent=2
            )
            schema_msg = {
                "role": "system",
                "content": f"Respond with valid JSON matching this schema:\n{schema_str}",
            }
            kwargs["messages"] = [schema_msg] + kwargs["messages"]
        elif supports_structured:
            kwargs["response_format"] = schema_rf
        # else: no response_format, parse from text later

    # Vertex AI
    if _is_vertex_model(model_row):
        vertex_params = _get_vertex_credentials(model_row)
        kwargs.update(vertex_params)

    # Custom base_url
    base_url = str(model_row.get("base_url", "")).strip()
    if _is_lm_studio_model(model_row):
        base_url = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
        kwargs["api_key"] = "lm-studio"
    if base_url:
        kwargs["base_url"] = base_url

    # API key from env
    key_name = str(model_row.get("api_key", "")).strip()
    if key_name and key_name.upper() != "EXISTING_KEY" and key_name != "VERTEX_CREDENTIALS":
        key_val = os.getenv(key_name)
        if key_val:
            kwargs["api_key"] = _sanitize_api_key(key_val)

    return kwargs


def _invoke_completion(
    kwargs: Dict[str, Any], use_batch_mode: bool
) -> Any:
    """Call litellm.completion or litellm.batch_completion."""
    if use_batch_mode:
        # For batch mode, messages should be a list of message lists
        messages_list = kwargs.pop("messages")
        if not isinstance(messages_list[0], list):
            messages_list = [messages_list]
        return litellm.batch_completion(
            messages=messages_list,
            **kwargs,
        )
    return litellm.completion(**kwargs)


def _invoke_responses_api(
    model_row: pd.Series,
    messages: List[Dict[str, Any]],
    time_val: float,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
) -> Any:
    """Call litellm.responses() for gpt-5* models."""
    model_name = str(model_row["model"])
    reasoning_params = _build_reasoning_params(model_row, time_val)

    kwargs: Dict[str, Any] = {
        "model": model_name,
        "input": messages,
    }

    # Text format
    schema_rf = _prepare_json_schema(output_pydantic, output_schema)
    if schema_rf is not None:
        kwargs["text"] = {"format": schema_rf}
    else:
        kwargs["text"] = {"format": {"type": "text"}}

    # Reasoning for Responses API
    responses_reasoning = reasoning_params.get("_responses_reasoning")
    if responses_reasoning:
        kwargs["reasoning"] = responses_reasoning

    # No temperature for Responses API

    # API key
    key_name = str(model_row.get("api_key", "")).strip()
    if key_name and key_name.upper() != "EXISTING_KEY":
        key_val = os.getenv(key_name)
        if key_val:
            kwargs["api_key"] = _sanitize_api_key(key_val)

    base_url = str(model_row.get("base_url", "")).strip()
    if base_url:
        kwargs["base_url"] = base_url

    return litellm.responses(**kwargs)


# ---------------------------------------------------------------------------
# Core: llm_invoke
# ---------------------------------------------------------------------------


def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = 0.5,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    time: float = 0.25,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    """Invoke an LLM with automatic model selection, structured output, and cloud fallback.

    Parameters
    ----------
    prompt : str, optional
        Prompt template with ``{variable}`` placeholders.
    input_json : dict or list of dicts, optional
        Template variables. A list triggers batch mode.
    strength : float
        ``0`` = cheapest, ``0.5`` = base model, ``1`` = highest ELO.
    temperature : float
        Sampling temperature.
    verbose : bool
        Enable detailed logging.
    output_pydantic : Type[BaseModel], optional
        Pydantic model for structured output.
    output_schema : dict, optional
        Raw JSON schema (alternative to *output_pydantic*).
    time : float
        Thinking effort ``0``–``1`` (mapped per model's reasoning_type).
    use_batch_mode : bool
        Use ``litellm.batch_completion`` when True.
    messages : list, optional
        Pre-formatted messages; overrides *prompt* / *input_json*.
    language : str, optional
        Language hint (e.g. ``"python"``).
    use_cloud : bool or None
        ``None`` = auto-detect, ``True`` = force cloud, ``False`` = force local.

    Returns
    -------
    dict
        ``{result, cost, model_name, thinking_output}``
    """
    # ----- bootstrap -----
    _ensure_env_loaded()
    _setup_logging()
    if verbose:
        set_verbose_logging(True)
    _register_callback()
    _setup_cache()

    # Configure litellm.drop_params
    drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true").lower()
    litellm.drop_params = drop_params_env in ("true", "1", "yes")

    # ----- cloud execution path -----
    if use_cloud is not False:
        should_try_cloud = False
        if use_cloud is True:
            should_try_cloud = True
        elif use_cloud is None:
            if os.getenv("PDD_FORCE_LOCAL", "0") != "1":
                try:
                    from .cloud_config import CloudConfig  # type: ignore[import-untyped]
                    should_try_cloud = CloudConfig.is_cloud_enabled()
                except (ImportError, Exception):
                    should_try_cloud = False

        if should_try_cloud:
            try:
                cloud_result = _llm_invoke_cloud(
                    prompt=prompt,
                    input_json=input_json,
                    messages=messages,
                    strength=strength,
                    temperature=temperature,
                    time_val=time,
                    verbose=verbose,
                    output_pydantic=output_pydantic,
                    output_schema=output_schema,
                    use_batch_mode=use_batch_mode,
                    language=language,
                )
                return cloud_result
            except InsufficientCreditsError:
                raise
            except CloudFallbackError as cfe:
                console.print(
                    f"[yellow]☐ Cloud fallback: {cfe}. Using local execution.[/yellow]"
                )
                logger.warning("Cloud fallback: %s", cfe)
            except CloudInvocationError as cie:
                console.print(
                    f"[yellow]☐ Cloud error: {cie}. Using local execution.[/yellow]"
                )
                logger.warning("Cloud invocation error: %s", cie)

    # ----- input validation -----
    if messages is None and prompt is None:
        raise ValueError("Either 'prompt' or 'messages' must be provided.")

    # ----- build messages -----
    if messages is not None:
        built_messages = messages
    else:
        built_messages = _build_messages(prompt, input_json)

    # Detect batch mode from input_json list
    is_batch = use_batch_mode or isinstance(input_json, list)

    # ----- load models -----
    df = _load_model_csv()
    available = _get_available_models(df)
    if available.empty:
        logger.warning("No models with available API keys. Attempting interactive setup.")
        # Try to enable models via interactive key entry
        for idx, row in df.iterrows():
            _ensure_api_key_for_model(row)
        available = _get_available_models(df)
        if available.empty:
            raise RuntimeError("No LLM models available. Check API keys and llm_model.csv.")

    candidates = _select_model_candidates(available, strength)
    if not candidates:
        raise RuntimeError("No model candidates for the given strength parameter.")

    # ----- iterate candidates -----
    global _LAST_CALLBACK_DATA
    last_error: Optional[Exception] = None

    for candidate_idx, model_row in enumerate(candidates):
        model_name = str(model_row["model"])
        logger.info("Trying model: %s (candidate %d/%d)", model_name, candidate_idx + 1, len(candidates))

        # Ensure API key
        if not _ensure_api_key_for_model(model_row):
            logger.debug("Skipping %s: API key not available", model_name)
            continue

        _LAST_CALLBACK_DATA = {}

        try:
            # ----- make LLM call -----
            use_responses_api = _is_gpt5_model(model_name)

            if use_responses_api and not is_batch:
                # Responses API
                call_messages = built_messages if isinstance(built_messages, list) and (
                    not built_messages or isinstance(built_messages[0], dict)
                ) else built_messages  # type: ignore[assignment]
                response = _invoke_responses_api(
                    model_row=model_row,
                    messages=call_messages,  # type: ignore[arg-type]
                    time_val=time,
                    output_pydantic=output_pydantic,
                    output_schema=output_schema,
                )
            else:
                # Standard completion
                call_kwargs = _build_call_kwargs(
                    model_row=model_row,
                    messages=built_messages if isinstance(built_messages, list) and (  # type: ignore[arg-type]
                        not built_messages or isinstance(built_messages[0], dict)
                    ) else built_messages[0] if isinstance(built_messages, list) else built_messages,  # type: ignore[arg-type]
                    temperature=temperature,
                    time_val=time,
                    output_pydantic=output_pydantic,
                    output_schema=output_schema,
                )

                if is_batch:
                    if isinstance(built_messages, list) and built_messages and isinstance(built_messages[0], list):
                        batch_messages = built_messages
                    elif isinstance(built_messages, list) and built_messages and isinstance(built_messages[0], dict):
                        batch_messages = [built_messages]
                    else:
                        batch_messages = [built_messages]  # type: ignore[list-item]
                    call_kwargs["messages"] = batch_messages  # type: ignore[assignment]
                    response = _invoke_completion(call_kwargs, use_batch_mode=True)
                else:
                    response = _invoke_completion(call_kwargs, use_batch_mode=False)

            # ----- process response -----
            if is_batch and isinstance(response, list):
                results: List[Any] = []
                for resp_item in response:
                    content = _extract_content(resp_item)
                    if content is None:
                        results.append(None)
                        continue
                    if output_pydantic or output_schema:
                        parsed = _process_structured_response(
                            content, output_pydantic, output_schema, language
                        )
                        results.append(parsed)
                    else:
                        results.append(content)

                total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                return {
                    "result": results,
                    "cost": total_cost,
                    "model_name": model_name,
                    "thinking_output": "",
                }

            # Single response
            content = _extract_content(response)

            # Handle None content: retry with cache bypass
            if content is None:
                logger.warning("Received None content from %s, retrying with cache bypass", model_name)
                if not use_responses_api:
                    # Modify prompt slightly to bypass cache
                    retry_kwargs = dict(call_kwargs)
                    if retry_kwargs.get("messages"):
                        retry_msgs = [dict(m) for m in retry_kwargs["messages"]]
                        if retry_msgs:
                            retry_msgs[-1]["content"] = retry_msgs[-1].get("content", "") + " "
                        retry_kwargs["messages"] = retry_msgs
                    try:
                        response = _invoke_completion(retry_kwargs, use_batch_mode=False)
                        content = _extract_content(response)
                    except Exception:
                        pass

                if content is None:
                    logger.warning("Still None content after retry on %s", model_name)
                    continue

            # Check for excessive trailing newlines (truncation indicator)
            if content.endswith("\n\n\n\n") and (output_pydantic or output_schema):
                logger.warning("Detected possible truncation, retrying with cache bypass")
                if not use_responses_api:
                    retry_kwargs = dict(call_kwargs)
                    if retry_kwargs.get("messages"):
                        retry_msgs = [dict(m) for m in retry_kwargs["messages"]]
                        if retry_msgs:
                            retry_msgs[-1]["content"] = retry_msgs[-1].get("content", "") + "  "
                        retry_kwargs["messages"] = retry_msgs
                    try:
                        resp2 = _invoke_completion(retry_kwargs, use_batch_mode=False)
                        c2 = _extract_content(resp2)
                        if c2 and not c2.endswith("\n\n\n\n"):
                            content = c2
                            response = resp2
                    except Exception:
                        pass

            thinking = _extract_thinking(response)

            # Process structured output
            if output_pydantic or output_schema:
                try:
                    result = _process_structured_response(
                        content, output_pydantic, output_schema, language
                    )
                except (json.JSONDecodeError, SchemaValidationError) as parse_err:
                    logger.warning(
                        "Structured output parse failed on %s: %s",
                        model_name,
                        parse_err,
                    )
                    raise SchemaValidationError(str(parse_err))

                # Process code fields
                result, has_invalid_python = _process_code_fields(result, language)
                if has_invalid_python and (language is None or language.lower() == "python"):
                    logger.warning("Invalid Python in structured output from %s", model_name)
                    # Retry with cache bypass
                    if not use_responses_api:
                        retry_kwargs = dict(call_kwargs)
                        if retry_kwargs.get("messages"):
                            retry_msgs = [dict(m) for m in retry_kwargs["messages"]]
                            if retry_msgs:
                                retry_msgs[-1]["content"] = retry_msgs[-1].get("content", "") + "   "
                            retry_kwargs["messages"] = retry_msgs
                        try:
                            resp3 = _invoke_completion(retry_kwargs, use_batch_mode=False)
                            c3 = _extract_content(resp3)
                            if c3:
                                r3 = _process_structured_response(
                                    c3, output_pydantic, output_schema, language
                                )
                                r3, still_invalid = _process_code_fields(r3, language)
                                if not still_invalid:
                                    result = r3
                                    response = resp3
                                    thinking = _extract_thinking(resp3)
                        except Exception:
                            pass
            else:
                result = content

            total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)

            if verbose:
                logger.debug("Model: %s, Cost: %.6f", model_name, total_cost)

            return {
                "result": result,
                "cost": total_cost,
                "model_name": model_name,
                "thinking_output": thinking,
            }

        except SchemaValidationError as sve:
            logger.warning("Schema validation error on %s: %s", model_name, sve)
            last_error = sve
            continue

        except litellm.AuthenticationError as auth_err:
            key_name = str(model_row.get("api_key", "")).strip()
            logger.warning("Auth error on %s: %s", model_name, auth_err)

            if _detect_wsl():
                console.print(
                    "[yellow]WSL detected: Check for carriage returns (\\r) in API keys.[/yellow]"
                )

            # If key was newly acquired, re-prompt
            if key_name in _NEWLY_ACQUIRED_KEYS:
                console.print(
                    f"[red]Authentication failed for newly entered key [cyan]{key_name}[/cyan].[/red]"
                )
                _NEWLY_ACQUIRED_KEYS.discard(key_name)
                os.environ.pop(key_name, None)
                new_val = _prompt_for_api_key(key_name)
                if new_val:
                    # Retry with the same model
                    try:
                        if use_responses_api and not is_batch:
                            response = _invoke_responses_api(
                                model_row=model_row,
                                messages=built_messages,  # type: ignore[arg-type]
                                time_val=time,
                                output_pydantic=output_pydantic,
                                output_schema=output_schema,
                            )
                        else:
                            call_kwargs = _build_call_kwargs(
                                model_row=model_row,
                                messages=built_messages,  # type: ignore[arg-type]
                                temperature=temperature,
                                time_val=time,
                                output_pydantic=output_pydantic,
                                output_schema=output_schema,
                            )
                            response = _invoke_completion(call_kwargs, use_batch_mode=is_batch)

                        content = _extract_content(response)
                        if content is not None:
                            thinking = _extract_thinking(response)
                            if output_pydantic or output_schema:
                                result = _process_structured_response(
                                    content, output_pydantic, output_schema, language
                                )
                                result, _ = _process_code_fields(result, language)
                            else:
                                result = content
                            return {
                                "result": result,
                                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                                "model_name": model_name,
                                "thinking_output": thinking,
                            }
                    except Exception as retry_err:
                        logger.warning("Retry after re-prompt failed: %s", retry_err)

            last_error = auth_err
            continue

        except litellm.BadRequestError as bre:
            err_msg = str(bre).lower()
            # Anthropic temperature + thinking auto-adjustment
            if "temperature" in err_msg and "thinking" in err_msg:
                logger.info("Adjusting temperature for thinking mode on %s", model_name)
                try:
                    call_kwargs = _build_call_kwargs(
                        model_row=model_row,
                        messages=built_messages,  # type: ignore[arg-type]
                        temperature=1.0,
                        time_val=time,
                        output_pydantic=output_pydantic,
                        output_schema=output_schema,
                    )
                    call_kwargs["temperature"] = 1
                    response = _invoke_completion(call_kwargs, use_batch_mode=is_batch)
                    content = _extract_content(response)
                    if content is not None:
                        thinking = _extract_thinking(response)
                        if output_pydantic or output_schema:
                            result = _process_structured_response(
                                content, output_pydantic, output_schema, language
                            )
                            result, _ = _process_code_fields(result, language)
                        else:
                            result = content
                        return {
                            "result": result,
                            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                            "model_name": model_name,
                            "thinking_output": thinking,
                        }
                except Exception as adj_err:
                    logger.warning("Temperature adjustment retry failed: %s", adj_err)

            last_error = bre
            continue

        except (
            litellm.RateLimitError,
            litellm.ServiceUnavailableError,
            litellm.Timeout,
            litellm.APIConnectionError,
        ) as transient_err:
            logger.warning("Transient error on %s: %s", model_name, transient_err)
            last_error = transient_err
            continue

        except Exception as exc:
            logger.error("Unexpected error on %s: %s", model_name, exc, exc_info=verbose)
            last_error = exc
            continue

    # All candidates exhausted
    error_msg = f"All {len(candidates)} model candidates exhausted."
    if last_error:
        error_msg += f" Last error: {last_error}"
    raise RuntimeError(error_msg)