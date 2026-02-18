from __future__ import annotations

import ast
import importlib.resources
import io
import json
import logging
import os
import re
import time as time_module
import warnings
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Type, Union

import litellm
import openai
import pandas as pd
from dotenv import load_dotenv
from litellm.caching.caching import Cache
from pydantic import BaseModel, ValidationError
from rich.console import Console

from pdd.path_resolution import get_default_resolver

# ---------------------------------------------------------------------------
# Logging configuration
# ---------------------------------------------------------------------------

logger = logging.getLogger("pdd.llm_invoke")

PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"

if PRODUCTION_MODE:
    logger.setLevel(logging.WARNING)
else:
    logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))

litellm_logger = logging.getLogger("litellm")
litellm_log_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING" if PRODUCTION_MODE else "INFO")
litellm_logger.setLevel(getattr(logging, litellm_log_level, logging.WARNING))

# Suppress LiteLLM "Give Feedback / Get Help" banner
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# litellm.drop_params – ignore unsupported provider params by default
try:
    _drop_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

if not logger.handlers:
    _console_handler = logging.StreamHandler()
    _console_handler.setFormatter(logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s"))
    logger.addHandler(_console_handler)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(_console_handler)

# Verbose‑logging env override
if os.getenv("PDD_VERBOSE_LOGGING") == "1":
    logger.setLevel(logging.DEBUG)
    litellm_logger.setLevel(logging.DEBUG)


def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    """Add a rotating file handler (10 MB, 5 backups)."""
    if not log_file_path:
        return
    try:
        fh = RotatingFileHandler(log_file_path, maxBytes=10 * 1024 * 1024, backupCount=5)
        fh.setFormatter(logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s"))
        logger.addHandler(fh)
        litellm_logger.addHandler(fh)
        logger.info("File logging configured to: %s", log_file_path)
    except Exception as exc:
        logger.warning("Failed to set up file logging: %s", exc)


def set_verbose_logging(verbose: bool = False) -> None:
    want = bool(verbose) or os.getenv("PDD_VERBOSE_LOGGING") == "1"
    if want:
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.WARNING if PRODUCTION_MODE else getattr(logging, PDD_LOG_LEVEL, logging.INFO))
        litellm_logger.setLevel(getattr(logging, litellm_log_level, logging.WARNING))
    try:
        if hasattr(litellm, "set_verbose"):
            litellm.set_verbose = want
        if hasattr(litellm, "suppress_debug_info"):
            litellm.suppress_debug_info = not want
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Console
# ---------------------------------------------------------------------------
console = Console()

# ---------------------------------------------------------------------------
# Project‑root / CSV / .env resolution
# ---------------------------------------------------------------------------

PDD_PATH_ENV = os.getenv("PDD_PATH")

resolver = get_default_resolver()
PROJECT_ROOT: Path = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV: bool = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env
logger.debug("Using PROJECT_ROOT: %s", PROJECT_ROOT)

# Detect installed‑package path
try:
    _installed_pkg_root_path: Optional[Path] = Path(str(importlib.resources.files("pdd")))
except Exception:
    _installed_pkg_root_path = None


def _is_env_path_package_dir(env_path: Path) -> bool:
    try:
        if _installed_pkg_root_path is None:
            return False
        return env_path.resolve() == _installed_pkg_root_path.resolve() or str(env_path.resolve()).startswith(
            str(_installed_pkg_root_path.resolve())
        )
    except Exception:
        return False


def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    try:
        cur = Path.cwd().resolve()
        for _ in range(max_levels):
            if any((cur / m).exists() for m in (".git", "pyproject.toml", ".env")) or (cur / "data").is_dir():
                return cur
            parent = cur.parent
            if parent == cur:
                break
            cur = parent
    except Exception:
        pass
    return Path.cwd().resolve()


project_root_from_cwd = _detect_project_root_from_cwd()

if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
    logger.debug("PDD_PATH points to package; using ENV_PATH from CWD: %s", ENV_PATH)
else:
    ENV_PATH = PROJECT_ROOT / ".env"

# --- Determine LLM_MODEL_CSV_PATH ---
user_model_csv_path = Path.home() / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH: Optional[Path] = user_model_csv_path
    logger.info("Using user‑specific LLM model CSV: %s", LLM_MODEL_CSV_PATH)
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
    logger.info("Using project‑specific LLM model CSV (from PDD_PATH): %s", LLM_MODEL_CSV_PATH)
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
    logger.info("Using project‑specific LLM model CSV (from CWD): %s", LLM_MODEL_CSV_PATH)
else:
    LLM_MODEL_CSV_PATH = None
    logger.info("No local LLM model CSV found, will use package default")

# Load .env
logger.debug("Attempting to load .env from: %s", ENV_PATH)
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)
    logger.debug("Loaded .env file from: %s", ENV_PATH)

DEFAULT_BASE_MODEL: Optional[str] = os.getenv("PDD_MODEL_DEFAULT", None)

# Opt‑in to future pandas downcasting behaviour
try:
    pd.set_option("future.no_silent_downcasting", True)
except Exception:
    pass

# ---------------------------------------------------------------------------
# LiteLLM cache
# ---------------------------------------------------------------------------

LLM_CALL_TIMEOUT = 600  # seconds

GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID", "").strip() or None
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY", "").strip() or None

cache_configured = False
configured_cache: Optional[Cache] = None

if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    logger.info("LiteLLM caching disabled via LITELLM_CACHE_DISABLE=1")
    litellm.cache = None
    cache_configured = True

if not cache_configured and GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    orig_aws_key = os.environ.get("AWS_ACCESS_KEY_ID")
    orig_aws_secret = os.environ.get("AWS_SECRET_ACCESS_KEY")
    try:
        os.environ["AWS_ACCESS_KEY_ID"] = GCS_HMAC_ACCESS_KEY_ID
        os.environ["AWS_SECRET_ACCESS_KEY"] = GCS_HMAC_SECRET_ACCESS_KEY
        configured_cache = Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_region_name=os.getenv("GCS_REGION_NAME", "auto"),
            s3_endpoint_url="https://storage.googleapis.com",
        )
        litellm.cache = configured_cache
        logger.info("LiteLLM cache configured for GCS bucket (S3 compatible): %s", GCS_BUCKET_NAME)
        cache_configured = True
    except Exception as exc:
        warnings.warn(f"Failed to configure LiteLLM S3/GCS cache: {exc}.")
        litellm.cache = None
    finally:
        if orig_aws_key is not None:
            os.environ["AWS_ACCESS_KEY_ID"] = orig_aws_key
        elif "AWS_ACCESS_KEY_ID" in os.environ:
            del os.environ["AWS_ACCESS_KEY_ID"]
        if orig_aws_secret is not None:
            os.environ["AWS_SECRET_ACCESS_KEY"] = orig_aws_secret
        elif "AWS_SECRET_ACCESS_KEY" in os.environ:
            del os.environ["AWS_SECRET_ACCESS_KEY"]

if not cache_configured:
    try:
        sqlite_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_path))
        litellm.cache = configured_cache
        logger.info("LiteLLM disk cache configured at %s", sqlite_path)
        cache_configured = True
    except Exception as exc2:
        warnings.warn(f"Failed to configure LiteLLM disk cache: {exc2}. Caching disabled.")
        litellm.cache = None

# ---------------------------------------------------------------------------
# LiteLLM success callback
# ---------------------------------------------------------------------------

_LAST_CALLBACK_DATA: Dict[str, Any] = {
    "input_tokens": 0,
    "output_tokens": 0,
    "finish_reason": None,
    "cost": 0.0,
}

_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}


def _set_model_rate_map(df: pd.DataFrame) -> None:
    global _MODEL_RATE_MAP
    try:
        _MODEL_RATE_MAP = {
            str(row["model"]): (
                float(row["input"]) if pd.notna(row["input"]) else 0.0,
                float(row["output"]) if pd.notna(row["output"]) else 0.0,
            )
            for _, row in df.iterrows()
        }
    except Exception:
        _MODEL_RATE_MAP = {}


def _litellm_success_callback(
    kwargs: Dict[str, Any],
    completion_response: Any,
    start_time: float,
    end_time: float,
) -> None:
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, "usage", None)
    input_tokens = getattr(usage, "prompt_tokens", 0) or 0
    output_tokens = getattr(usage, "completion_tokens", 0) or 0
    finish_reason = None
    try:
        finish_reason = getattr(completion_response.choices[0], "finish_reason", None)
    except Exception:
        pass

    calculated_cost = 0.0
    try:
        cost_val = litellm.completion_cost(completion_response=completion_response)
        calculated_cost = cost_val if cost_val is not None else 0.0
    except Exception:
        model_name = kwargs.get("model")
        in_tok = getattr(usage, "prompt_tokens", None) or getattr(usage, "input_tokens", 0) or 0
        out_tok = getattr(usage, "completion_tokens", None) or getattr(usage, "output_tokens", 0) or 0
        rates = _MODEL_RATE_MAP.get(str(model_name)) if model_name else None
        if rates is not None:
            calculated_cost = (float(in_tok) * rates[0] + float(out_tok) * rates[1]) / 1_000_000.0

    _LAST_CALLBACK_DATA = {
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "finish_reason": finish_reason,
        "cost": calculated_cost,
    }


litellm.success_callback = [_litellm_success_callback]

# ---------------------------------------------------------------------------
# Custom exceptions
# ---------------------------------------------------------------------------


class SchemaValidationError(Exception):
    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0) -> None:
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index


class CloudFallbackError(Exception):
    pass


class CloudInvocationError(Exception):
    pass


class InsufficientCreditsError(Exception):
    pass


# ---------------------------------------------------------------------------
# WSL helpers
# ---------------------------------------------------------------------------


def _is_wsl_environment() -> bool:
    try:
        if os.getenv("WSL_DISTRO_NAME"):
            return True
        if os.path.exists("/proc/version"):
            with open("/proc/version") as f:
                v = f.read().lower()
                return "microsoft" in v or "wsl" in v
    except Exception:
        pass
    return False


def _get_environment_info() -> Dict[str, str]:
    import platform

    info = {
        "platform": platform.system(),
        "python_version": platform.python_version(),
        "is_wsl": str(_is_wsl_environment()),
    }
    if _is_wsl_environment():
        info["wsl_distro"] = os.getenv("WSL_DISTRO_NAME", "unknown")
    return info


# ---------------------------------------------------------------------------
# API key helpers
# ---------------------------------------------------------------------------


def _sanitize_api_key(key_value: Optional[str]) -> Optional[str]:
    if not key_value:
        return key_value
    sanitized = key_value.strip()
    sanitized = "".join(c for c in sanitized if ord(c) >= 32)
    if key_value != sanitized and "\r" in key_value and _is_wsl_environment():
        logger.info("Detected and fixed WSL line ending issue in API key")
    return sanitized


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    lines: List[str] = []
    if env_path.exists():
        with open(env_path) as f:
            lines = f.readlines()

    new_lines: List[str] = []
    key_replaced = False
    prefix = f"{key_name}="
    prefix_spaced = f"{key_name} ="
    for line in lines:
        stripped = line.strip()
        if stripped.startswith(f"# {prefix}") or stripped.startswith(f"# {prefix_spaced}"):
            continue
        elif stripped.startswith(prefix) or stripped.startswith(prefix_spaced):
            new_lines.append(f'{key_name}="{value}"\n')
            key_replaced = True
        else:
            new_lines.append(line)

    if not key_replaced:
        if new_lines and not new_lines[-1].endswith("\n"):
            new_lines.append("\n")
        new_lines.append(f'{key_name}="{value}"\n')

    with open(env_path, "w") as f:
        f.writelines(new_lines)


def _ensure_api_key(model_info: Dict[str, Any], newly_acquired_keys: Dict[str, bool], verbose: bool) -> bool:
    key_name = model_info.get("api_key")
    if not key_name or key_name == "EXISTING_KEY":
        return True

    key_value = os.getenv(key_name)
    if key_value:
        key_value = _sanitize_api_key(key_value)

    if key_value:
        newly_acquired_keys[key_name] = False
        return True

    logger.warning("API key '%s' for model '%s' is not set.", key_name, model_info.get("model"))

    if os.environ.get("PDD_FORCE"):
        logger.error("API key '%s' not set. In --force mode, skipping.", key_name)
        return False

    try:
        user_key = input(f"Please enter the API key for {key_name}: ").strip()
        if not user_key:
            logger.error("No API key provided.")
            return False

        user_key = _sanitize_api_key(user_key) or ""
        os.environ[key_name] = user_key
        newly_acquired_keys[key_name] = True

        try:
            _save_key_to_env_file(key_name, user_key, ENV_PATH)
            logger.info("API key '%s' saved to %s.", key_name, ENV_PATH)
            logger.warning("SECURITY WARNING: The API key has been saved to your .env file.")
        except IOError as exc:
            logger.error("Failed to update .env file: %s", exc)

        return True
    except EOFError:
        logger.error("Cannot prompt for API key in non-interactive environment.")
        return False
    except Exception as exc:
        logger.error("Unexpected error during API key acquisition: %s", exc)
        return False


# ---------------------------------------------------------------------------
# Schema helpers
# ---------------------------------------------------------------------------


def _ensure_all_properties_required(schema: Any) -> Any:
    if not isinstance(schema, dict):
        return schema
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop_schema in schema["properties"].values():
            _ensure_all_properties_required(prop_schema)
    if schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            _ensure_all_properties_required(def_schema)
    return schema


def _add_additional_properties_false(schema: Any) -> Any:
    if not isinstance(schema, dict):
        return schema
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop_schema in schema["properties"].values():
                _add_additional_properties_false(prop_schema)
    if schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            _add_additional_properties_false(def_schema)
    return schema


# ---------------------------------------------------------------------------
# Cloud helpers
# ---------------------------------------------------------------------------


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, pydantic_class):
        return result
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    if isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    raise ValueError(f"Cannot validate result type {type(result)} with Pydantic model")


def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    strength: float,
    temperature: float,
    verbose: bool,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    time: float,
    use_batch_mode: bool,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]],
    language: Optional[str],
) -> Dict[str, Any]:
    import requests

    from pdd.core.cloud import CloudConfig

    CLOUD_TIMEOUT = 300

    jwt_token = CloudConfig.get_jwt_token(verbose=verbose)
    if not jwt_token:
        raise CloudFallbackError("Could not authenticate with cloud")

    payload: Dict[str, Any] = {
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "useBatchMode": use_batch_mode,
    }
    if language:
        payload["language"] = language
    if messages:
        payload["messages"] = messages
    else:
        payload["prompt"] = prompt
        payload["inputJson"] = input_json

    if output_pydantic:
        payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema:
        payload["outputSchema"] = output_schema

    headers = {"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"}
    cloud_url = CloudConfig.get_endpoint_url("llmInvoke")

    if verbose:
        logger.debug("Cloud llm_invoke request to: %s", cloud_url)

    try:
        response = requests.post(cloud_url, json=payload, headers=headers, timeout=CLOUD_TIMEOUT)

        if response.status_code == 200:
            data = response.json()
            result = data.get("result")
            if output_pydantic and result:
                try:
                    result = _validate_with_pydantic(result, output_pydantic)
                except (ValidationError, ValueError):
                    pass
            return {
                "result": result,
                "cost": data.get("totalCost", 0.0),
                "model_name": data.get("modelName", "cloud_model"),
                "thinking_output": data.get("thinkingOutput"),
            }
        elif response.status_code == 402:
            raise InsufficientCreditsError(response.json().get("error", "Insufficient credits"))
        elif response.status_code in (401, 403):
            try:
                from pdd.auth_service import clear_jwt_cache

                clear_jwt_cache()
            except Exception:
                pass
            server_error = response.json().get("error", "")
            raise CloudFallbackError(
                f"Authentication expired ({server_error or response.status_code}). "
                "Please re-authenticate with: pdd auth logout && pdd auth login"
            )
        elif response.status_code >= 500:
            raise CloudFallbackError(response.json().get("error", f"Server error ({response.status_code})"))
        else:
            raise CloudInvocationError(f"Cloud llm_invoke failed: {response.json().get('error', f'HTTP {response.status_code}')}")

    except requests.exceptions.Timeout:
        raise CloudFallbackError("Cloud request timed out")
    except requests.exceptions.ConnectionError as exc:
        raise CloudFallbackError(f"Cloud connection failed: {exc}")
    except requests.exceptions.RequestException as exc:
        raise CloudFallbackError(f"Cloud request failed: {exc}")


# ---------------------------------------------------------------------------
# Model data loading / selection
# ---------------------------------------------------------------------------


def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    df: Optional[pd.DataFrame] = None

    if csv_path is not None:
        if csv_path.exists():
            try:
                df = pd.read_csv(csv_path)
                logger.debug("Loaded model data from %s", csv_path)
            except Exception as exc:
                logger.warning("Failed to load CSV from %s: %s, trying package default", csv_path, exc)

    if df is None:
        try:
            csv_text = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
            df = pd.read_csv(io.StringIO(csv_text))
            logger.info("Loaded model data from package default")
        except Exception as exc:
            raise FileNotFoundError(f"Failed to load default LLM model CSV from package: {exc}") from exc

    required_cols = ["provider", "model", "input", "output", "coding_arena_elo", "api_key", "structured_output", "reasoning_type"]
    for col in required_cols:
        if col not in df.columns:
            raise RuntimeError(f"Missing required column in CSV: {col}")

    numeric_cols = ["input", "output", "coding_arena_elo", "max_tokens", "max_completion_tokens", "max_reasoning_tokens"]
    for col in numeric_cols:
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce")

    df["input"] = df["input"].fillna(0.0)
    df["output"] = df["output"].fillna(0.0)
    df["coding_arena_elo"] = df["coding_arena_elo"].fillna(0)
    df["max_reasoning_tokens"] = df["max_reasoning_tokens"].fillna(0).astype(int) if "max_reasoning_tokens" in df.columns else 0
    df["avg_cost"] = (df["input"] + df["output"]) / 2
    df["structured_output"] = df["structured_output"].fillna(False).astype(bool) if "structured_output" in df.columns else False
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
    df["api_key"] = df["api_key"].fillna("").astype(str)

    return df


def _select_model_candidates(strength: float, base_model_name: Optional[str], model_df: pd.DataFrame) -> List[Dict[str, Any]]:
    if model_df.empty:
        raise ValueError("Loaded model data is empty. Check CSV file.")

    available_df = model_df[model_df["api_key"].notna()].copy()
    if available_df.empty:
        raise ValueError("No models available after initial filtering.")

    if base_model_name:
        base_model_row = available_df[available_df["model"] == base_model_name]
    else:
        base_model_row = pd.DataFrame()

    if base_model_row.empty:
        # Soft fallback – use first available model
        try:
            base_model = available_df.iloc[0]
        except Exception:
            raise ValueError("No models available for fallback selection.")
    else:
        base_model = base_model_row.iloc[0]

    if strength == 0.5:
        available_df["sort_metric"] = -available_df["coding_arena_elo"]
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")
        effective_base_name = str(base_model["model"])
        if any(c["model"] == effective_base_name for c in candidates):
            candidates.sort(key=lambda x: 0 if x["model"] == effective_base_name else 1)
    elif strength < 0.5:
        base_cost = base_model["avg_cost"]
        cheapest_cost = available_df["avg_cost"].min()
        target_cost = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost) if base_cost > cheapest_cost else cheapest_cost
        available_df["sort_metric"] = abs(available_df["avg_cost"] - target_cost)
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")
    else:
        base_elo = base_model["coding_arena_elo"]
        highest_elo = available_df["coding_arena_elo"].max()
        target_elo = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo) if highest_elo > base_elo else base_elo
        available_df["sort_metric"] = abs(available_df["coding_arena_elo"] - target_elo)
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")

    if not candidates:
        raise RuntimeError("Model selection resulted in an empty candidate list.")

    return candidates


# ---------------------------------------------------------------------------
# JSON extraction helpers
# ---------------------------------------------------------------------------


def _extract_fenced_json_block(text: str) -> Optional[str]:
    try:
        m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, flags=re.IGNORECASE)
        return m.group(1) if m else None
    except Exception:
        return None


def _extract_balanced_json_objects(text: str) -> List[str]:
    results: List[str] = []
    brace_stack = 0
    start_idx = -1
    in_string = False
    escape = False
    for i, ch in enumerate(text):
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
            if brace_stack == 0:
                start_idx = i
            brace_stack += 1
        elif ch == "}":
            if brace_stack > 0:
                brace_stack -= 1
                if brace_stack == 0 and start_idx != -1:
                    results.append(text[start_idx : i + 1])
                    start_idx = -1
    return results


def _is_malformed_json_response(content: Any, threshold: int = 100) -> bool:
    if not content or not isinstance(content, str):
        return False
    stripped = content.strip()
    if not stripped.startswith("{"):
        return False
    if stripped.endswith("}"):
        return False
    trailing_count = 0
    check = stripped
    while check.endswith("\\n"):
        trailing_count += 1
        check = check[:-2]
    if trailing_count >= threshold:
        return True
    if stripped.endswith("\\"):
        return True
    return False


# ---------------------------------------------------------------------------
# Code repair helpers
# ---------------------------------------------------------------------------


_PROSE_FIELD_NAMES = frozenset({
    "reasoning", "explanation", "analysis", "change_instructions",
    "change_description", "planned_modifications", "details",
    "description", "focus", "file_summary",
})


def _is_prose_field_name(field_name: str) -> bool:
    return field_name.lower() in _PROSE_FIELD_NAMES


def _looks_like_python_code(s: Optional[str]) -> bool:
    if not s or len(s) < 10:
        return False
    indicators = ("def ", "class ", "import ", "from ", "if __name__", "return ", "print(")
    return any(ind in s for ind in indicators)


def _repair_python_syntax(code: str) -> str:
    if not code or not code.strip():
        return code
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        pass
    for quote in ['"', "'"]:
        if code.rstrip().endswith(quote):
            candidate = code.rstrip()[:-1]
            try:
                ast.parse(candidate)
                return candidate
            except SyntaxError:
                pass
    for quote in ['"', "'"]:
        if code.lstrip().startswith(quote):
            candidate = code.lstrip()[1:]
            try:
                ast.parse(candidate)
                return candidate
            except SyntaxError:
                pass
    return code


def _smart_unescape_code(code: str) -> str:
    LITERAL_BN = "\\" + "n"
    if LITERAL_BN not in code:
        return code
    if "\n" in code:
        return code  # mixed state – leave alone

    result: List[str] = []
    i = 0
    in_string = False
    string_char: Optional[str] = None
    PLACEHOLDER = "\x00NEWLINE_ESCAPE\x00"

    while i < len(code):
        if i + 1 < len(code) and code[i] == "\\":
            nc = code[i + 1]
            if in_string:
                if nc == "n":
                    result.append(PLACEHOLDER)
                    i += 2
                    continue
                elif nc in ("t", "r", '"', "'", "\\"):
                    result.append(code[i : i + 2])
                    i += 2
                    continue
        if not in_string:
            if i + 2 < len(code) and code[i : i + 3] in ('"""', "'''"):
                in_string = True
                string_char = code[i : i + 3]
                result.append(code[i : i + 3])
                i += 3
                continue
            elif code[i] in ('"', "'"):
                in_string = True
                string_char = code[i]
                result.append(code[i])
                i += 1
                continue
        else:
            if string_char and len(string_char) == 3:
                if i + 2 < len(code) and code[i : i + 3] == string_char:
                    in_string = False
                    result.append(code[i : i + 3])
                    i += 3
                    continue
            elif string_char and code[i] == string_char:
                in_string = False
                result.append(code[i])
                i += 1
                continue
        result.append(code[i])
        i += 1

    intermediate = "".join(result)
    intermediate = intermediate.replace("\\" + "r" + "\\" + "n", "\r\n")
    intermediate = intermediate.replace(LITERAL_BN, "\n")
    intermediate = intermediate.replace("\\" + "t", "\t")
    return intermediate.replace(PLACEHOLDER, "\\n")


def _unescape_code_newlines(obj: Any) -> Any:
    if obj is None:
        return obj

    def _process_string(s: str) -> str:
        if _looks_like_python_code(s):
            s = _smart_unescape_code(s)
            s = _repair_python_syntax(s)
        else:
            bn = "\\" + "n"
            if bn in s:
                s = s.replace("\\" + "r" + "\\" + "n", "\r\n")
                s = s.replace(bn, "\n")
                s = s.replace("\\" + "t", "\t")
        return s

    if isinstance(obj, BaseModel):
        for field_name in obj.model_fields:
            value = getattr(obj, field_name)
            if isinstance(value, str):
                processed = _process_string(value)
                if processed != value:
                    object.__setattr__(obj, field_name, processed)
            elif isinstance(value, (dict, list, BaseModel)):
                _unescape_code_newlines(value)
        return obj
    if isinstance(obj, dict):
        for key, value in obj.items():
            if isinstance(value, str):
                obj[key] = _process_string(value)
            elif isinstance(value, (dict, list)):
                _unescape_code_newlines(value)
        return obj
    if isinstance(obj, list):
        for i, item in enumerate(obj):
            if isinstance(item, str):
                obj[i] = _process_string(item)
            elif isinstance(item, (dict, list, BaseModel)):
                _unescape_code_newlines(item)
        return obj
    return obj


def _has_invalid_python_code(obj: Any, field_name: str = "") -> bool:
    if obj is None:
        return False
    if isinstance(obj, str):
        if _is_prose_field_name(field_name):
            return False
        if _looks_like_python_code(obj):
            try:
                ast.parse(obj)
                return False
            except SyntaxError:
                return True
        return False
    if isinstance(obj, BaseModel):
        for name in obj.model_fields:
            if _has_invalid_python_code(getattr(obj, name), field_name=name):
                return True
        return False
    if isinstance(obj, dict):
        for key, value in obj.items():
            if _has_invalid_python_code(value, field_name=key if isinstance(key, str) else ""):
                return True
        return False
    if isinstance(obj, list):
        for item in obj:
            if _has_invalid_python_code(item, field_name=field_name):
                return True
        return False
    return False


# ---------------------------------------------------------------------------
# Message formatting
# ---------------------------------------------------------------------------


def _format_messages(
    prompt: str,
    input_data: Union[Dict[str, Any], List[Dict[str, Any]]],
    use_batch_mode: bool,
) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    try:
        if use_batch_mode:
            if not isinstance(input_data, list):
                raise ValueError("input_json must be a list of dictionaries when use_batch_mode is True.")
            all_msgs: List[List[Dict[str, str]]] = []
            for item in input_data:
                if not isinstance(item, dict):
                    raise ValueError("Each item in input_json list must be a dictionary for batch mode.")
                formatted = prompt.format(**item)
                all_msgs.append([{"role": "user", "content": formatted}])
            return all_msgs
        else:
            if not isinstance(input_data, dict):
                raise ValueError("input_json must be a dictionary when use_batch_mode is False.")
            formatted = prompt.format(**input_data)
            return [{"role": "user", "content": formatted}]
    except KeyError as exc:
        raise ValueError(f"Prompt formatting error: Missing key {exc} in input_json for prompt string.") from exc
    except Exception as exc:
        raise ValueError(f"Error formatting prompt: {exc}") from exc


# ---------------------------------------------------------------------------
# Main function
# ---------------------------------------------------------------------------


def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = 0.5,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    time: Optional[float] = 0.25,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    set_verbose_logging(verbose)

    # --- 0. Cloud execution path ---
    if use_cloud is None:
        force_local = os.environ.get("PDD_FORCE_LOCAL", "").lower() in ("1", "true", "yes")
        if force_local:
            use_cloud = False
        else:
            try:
                from pdd.core.cloud import CloudConfig
                use_cloud = CloudConfig.is_cloud_enabled()
            except ImportError:
                use_cloud = False

    if use_cloud:
        if verbose:
            logger.debug("Attempting cloud execution...")
        try:
            return _llm_invoke_cloud(
                prompt=prompt,
                input_json=input_json,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                output_pydantic=output_pydantic,
                output_schema=output_schema,
                time=time if time is not None else 0.25,
                use_batch_mode=use_batch_mode,
                messages=messages,
                language=language,
            )
        except CloudFallbackError as exc:
            console.print(f"[yellow]Cloud execution failed ({exc}), falling back to local execution...[/yellow]")
            logger.warning("Cloud fallback: %s", exc)
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as exc:
            console.print(f"[yellow]Cloud error ({exc}), falling back to local execution...[/yellow]")
            logger.warning("Cloud invocation error: %s", exc)

    # --- 1. Validate inputs ---
    if messages:
        if use_batch_mode:
            if not isinstance(messages, list) or not all(isinstance(m, list) for m in messages):
                raise ValueError("'messages' must be a list of lists when use_batch_mode is True.")
            if not all(isinstance(msg, dict) and "role" in msg and "content" in msg for m_list in messages for msg in m_list):
                raise ValueError("Each message must have 'role' and 'content'.")
        else:
            if not isinstance(messages, list) or not all(isinstance(msg, dict) and "role" in msg and "content" in msg for msg in messages):
                raise ValueError("'messages' must be a list of dicts with 'role' and 'content'.")
        formatted_messages = messages
    elif prompt and input_json is not None:
        formatted_messages = _format_messages(prompt, input_json, use_batch_mode)
    else:
        raise ValueError("Either 'messages' or both 'prompt' and 'input_json' must be provided.")

    if time is None:
        time = 0.0

    if not (0.0 <= strength <= 1.0):
        raise ValueError("'strength' must be between 0.0 and 1.0.")
    if not (0.0 <= time <= 1.0):
        raise ValueError("'time' must be between 0.0 and 1.0.")

    # --- 2. Load models ---
    try:
        model_df = _load_model_data(LLM_MODEL_CSV_PATH)
        candidate_models = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    except (FileNotFoundError, ValueError, RuntimeError) as exc:
        logger.error("Model loading/selection failed: %s", exc)
        raise

    if verbose:
        logger.info(
            "Candidate models selected and ordered (with strength): %s",
            [(c["model"],) for c in candidate_models],
        )
        logger.info("Strength: %s, Temperature: %s, Time: %s", strength, temperature, time)
        if input_json is not None:
            logger.info("Input JSON:")
            logger.info(repr(input_json))

    try:
        _set_model_rate_map(model_df)
    except Exception:
        pass

    # --- 3. Iterate candidates ---
    last_exception: Optional[Exception] = None
    newly_acquired_keys: Dict[str, bool] = {}
    response_format: Optional[Dict[str, Any]] = None
    time_kwargs: Dict[str, Any] = {}

    for model_info in candidate_models:
        model_name_litellm = model_info["model"]
        api_key_name = model_info.get("api_key")
        provider = model_info.get("provider", "").lower()

        if verbose:
            logger.info("[ATTEMPT] Trying model: %s (Provider: %s)", model_name_litellm, provider)

        retry_with_same_model = True
        current_temperature = temperature
        temp_adjustment_done = False

        while retry_with_same_model:
            retry_with_same_model = False

            if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
                if verbose:
                    logger.info("[SKIP] Skipping %s due to API key issue.", model_name_litellm)
                break

            litellm_kwargs: Dict[str, Any] = {
                "model": model_name_litellm,
                "messages": formatted_messages,
                "temperature": current_temperature,
                "num_retries": 2,
            }

            # Vertex AI handling
            is_vertex = provider in ("google", "googlevertexai", "vertex_ai") or model_name_litellm.startswith("vertex_ai/")

            if is_vertex and api_key_name == "VERTEX_CREDENTIALS":
                creds_path = os.getenv("VERTEX_CREDENTIALS")
                vp = os.getenv("VERTEX_PROJECT")
                model_loc = model_info.get("location")
                if pd.notna(model_loc) and str(model_loc).strip():
                    vl = str(model_loc).strip()
                else:
                    vl = os.getenv("VERTEX_LOCATION")

                if creds_path and vp and vl:
                    try:
                        with open(creds_path) as f:
                            litellm_kwargs["vertex_credentials"] = json.dumps(json.load(f))
                    except Exception:
                        pass
                    litellm_kwargs["vertex_project"] = vp
                    litellm_kwargs["vertex_location"] = vl
                elif vp and vl:
                    litellm_kwargs["vertex_project"] = vp
                    litellm_kwargs["vertex_location"] = vl
            elif api_key_name:
                kv = os.getenv(api_key_name)
                if kv:
                    litellm_kwargs["api_key"] = _sanitize_api_key(kv)
                if is_vertex:
                    vp2 = os.getenv("VERTEX_PROJECT")
                    model_loc2 = model_info.get("location")
                    vl2 = str(model_loc2).strip() if pd.notna(model_loc2) and str(model_loc2).strip() else os.getenv("VERTEX_LOCATION")
                    if vp2 and vl2:
                        litellm_kwargs["vertex_project"] = vp2
                        litellm_kwargs["vertex_location"] = vl2

            api_base = model_info.get("base_url")
            if pd.notna(api_base) and api_base:
                litellm_kwargs["base_url"] = str(api_base)
                litellm_kwargs["api_base"] = str(api_base)

            model_lower = str(model_name_litellm).lower()
            is_lm_studio = model_lower.startswith("lm_studio/") or provider == "lm_studio"
            is_groq = model_lower.startswith("groq/") or provider == "groq"

            if is_lm_studio:
                if not litellm_kwargs.get("base_url"):
                    lm_base = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                    litellm_kwargs["base_url"] = lm_base
                    litellm_kwargs["api_base"] = lm_base
                if not litellm_kwargs.get("api_key"):
                    litellm_kwargs["api_key"] = os.getenv("LM_STUDIO_API_KEY") or "lm-studio"

            # Structured output
            response_format = None
            if output_pydantic or output_schema:
                supports_structured = model_info.get("structured_output", False)
                if supports_structured:
                    if output_pydantic:
                        schema = output_pydantic.model_json_schema()
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": output_pydantic.__name__, "schema": schema, "strict": True},
                        }
                    else:
                        s = output_schema.copy() if output_schema else {}
                        _ensure_all_properties_required(s)
                        _add_additional_properties_false(s)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": "response", "schema": s, "strict": True},
                        }

                    if is_groq and response_format:
                        schema_for_prompt = output_pydantic.model_json_schema() if output_pydantic else output_schema
                        litellm_kwargs["response_format"] = {"type": "json_object"}
                        schema_instr = (
                            f"You must respond with valid JSON matching this schema:\n```json\n"
                            f"{json.dumps(schema_for_prompt, indent=2)}\n```\n"
                            "Respond ONLY with the JSON object."
                        )
                        msgs = litellm_kwargs.get("messages", [])
                        if msgs and isinstance(msgs, list) and isinstance(msgs[0], dict) and msgs[0].get("role") == "system":
                            msgs[0]["content" ] = schema_instr + "\n\n" + msgs[0]["content"]
                        else:
                            msgs.insert(0, {"role": "system", "content": schema_instr})
                        litellm_kwargs["messages"] = msgs
                    elif is_lm_studio and response_format:
                        litellm_kwargs["extra_body"] = {"response_format": response_format}
                    else:
                        litellm_kwargs["response_format"] = response_format

            # Reasoning parameters
            time_kwargs = {}
            reasoning_type = model_info.get("reasoning_type", "none")
            max_reasoning_tokens_val = int(model_info.get("max_reasoning_tokens", 0) or 0)

            if time and time > 0:
                if reasoning_type == "budget" and max_reasoning_tokens_val > 0:
                    budget = int(time * max_reasoning_tokens_val)
                    if budget > 0 and provider == "anthropic":
                        tp = {"type": "enabled", "budget_tokens": budget}
                        litellm_kwargs["thinking"] = tp
                        time_kwargs["thinking"] = tp
                elif reasoning_type == "effort":
                    effort = "low"
                    if time > 0.7:
                        effort = "high"
                    elif time > 0.3:
                        effort = "medium"

                    if provider == "openai" and model_lower.startswith("gpt-5"):
                        ro = {"effort": effort, "summary": "auto"}
                        litellm_kwargs["reasoning"] = ro
                        time_kwargs["reasoning"] = ro
                    else:
                        litellm_kwargs["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort

            if litellm.cache is not None:
                litellm_kwargs["caching"] = True
                if litellm_kwargs.get("metadata") is None:
                    litellm_kwargs["metadata"] = {}

            # --- Invocation ---
            try:
                start = time_module.time()

                # GPT-5 Responses API
                if not use_batch_mode and provider == "openai" and model_lower.startswith("gpt-5"):
                    try:
                        if isinstance(formatted_messages, list) and formatted_messages and isinstance(formatted_messages[0], dict):
                            input_text = "\n\n".join(f"{m.get('role','user')}: {m.get('content','')}" for m in formatted_messages)
                        else:
                            input_text = str(formatted_messages)

                        reasoning_param = time_kwargs.get("reasoning")
                        text_block: Dict[str, Any] = {"format": {"type": "text"}}
                        if output_pydantic or output_schema:
                            try:
                                s2 = output_pydantic.model_json_schema() if output_pydantic else (output_schema or {})
                                _ensure_all_properties_required(s2)
                                _add_additional_properties_false(s2)
                                text_block = {
                                    "format": {
                                        "type": "json_schema",
                                        "name": output_pydantic.__name__ if output_pydantic else "response",
                                        "strict": True,
                                        "schema": s2,
                                    }
                                }
                            except Exception:
                                pass

                        resp_kwargs: Dict[str, Any] = {"model": model_name_litellm, "input": input_text, "text": text_block}
                        if reasoning_param is not None:
                            resp_kwargs["reasoning"] = reasoning_param

                        resp = litellm.responses(**resp_kwargs)

                        result_text: Optional[str] = None
                        try:
                            for item in resp.output:
                                if getattr(item, "type", None) == "message" and hasattr(item, "content") and item.content:
                                    for ci in item.content:
                                        if hasattr(ci, "text"):
                                            result_text = ci.text
                                            break
                                    if result_text:
                                        break
                        except Exception:
                            pass

                        total_cost = 0.0
                        usage = getattr(resp, "usage", None)
                        if usage:
                            it = getattr(usage, "input_tokens", 0) or 0
                            ot = getattr(usage, "output_tokens", 0) or 0
                            ir = model_info.get("input", 0.0) or 0.0
                            orr = model_info.get("output", 0.0) or 0.0
                            total_cost = (it * ir + ot * orr) / 1_000_000.0

                        final_result: Any = None
                        if output_pydantic and result_text:
                            try:
                                final_result = output_pydantic.model_validate_json(result_text)
                            except Exception:
                                fenced = _extract_fenced_json_block(result_text)
                                cands = [fenced] if fenced else _extract_balanced_json_objects(result_text)
                                for c in cands:
                                    try:
                                        final_result = output_pydantic.model_validate_json(c)
                                        break
                                    except Exception:
                                        continue
                                if final_result is None:
                                    final_result = f"ERROR: Failed to parse. Raw: {repr(result_text)[:200]}"
                        else:
                            final_result = result_text

                        return {"result": final_result, "cost": total_cost, "model_name": model_name_litellm, "thinking_output": None}
                    except Exception as exc:
                        last_exception = exc
                        logger.error("[ERROR] Responses API failed for %s: %s", model_name_litellm, exc)
                        litellm_kwargs.pop("reasoning", None)

                # Anthropic + thinking → temperature=1
                if provider == "anthropic" and "thinking" in litellm_kwargs:
                    litellm_kwargs["temperature"] = 1
                    current_temperature = 1

                if use_batch_mode:
                    response = litellm.batch_completion(**litellm_kwargs)
                else:
                    response = litellm.completion(**litellm_kwargs, timeout=LLM_CALL_TIMEOUT)

                end = time_module.time()
                if verbose:
                    logger.info("[SUCCESS] Invocation successful for %s (%.2fs)", model_name_litellm, end - start)

                retry_provider_kwargs = {
                    k: v
                    for k, v in litellm_kwargs.items()
                    if k in ("vertex_credentials", "vertex_project", "vertex_location", "api_key", "base_url", "api_base")
                }

                # --- Process response ---
                results: List[Any] = []
                thinking_outputs: List[Optional[str]] = []
                response_list = response if use_batch_mode else [response]

                for idx, resp_item in enumerate(response_list):
                    # Thinking output
                    thinking: Optional[str] = None
                    try:
                        hp = getattr(resp_item, "_hidden_params", None)
                        if hp and "thinking" in hp:
                            thinking = hp["thinking"]
                        elif hasattr(resp_item, "choices") and resp_item.choices:
                            rc = getattr(resp_item.choices[0].message, "reasoning_content", None)
                            if rc:
                                thinking = rc
                    except Exception:
                        pass
                    thinking_outputs.append(thinking)

                    try:
                        raw_result = resp_item.choices[0].message.content

                        # None content → retry with cache bypass
                        if raw_result is None:
                            if not use_batch_mode and prompt and input_json is not None:
                                try:
                                    retry_msgs = _format_messages(prompt + " ", input_json, use_batch_mode)
                                    litellm.cache = None
                                    rr = litellm.completion(
                                        model=model_name_litellm,
                                        messages=retry_msgs,
                                        temperature=current_temperature,
                                        response_format=response_format,
                                        timeout=LLM_CALL_TIMEOUT,
                                        **time_kwargs,
                                        **retry_provider_kwargs,
                                    )
                                    litellm.cache = configured_cache
                                    rr_content = rr.choices[0].message.content
                                    if rr_content is not None:
                                        raw_result = rr_content
                                    else:
                                        results.append("ERROR: LLM returned None content even after retry")
                                        continue
                                except Exception:
                                    litellm.cache = configured_cache
                                    results.append("ERROR: LLM returned None content and retry failed")
                                    continue
                            else:
                                results.append("ERROR: LLM returned None content")
                                continue

                        # Malformed JSON → retry
                        if isinstance(raw_result, str) and _is_malformed_json_response(raw_result):
                            if not use_batch_mode and prompt and input_json is not None:
                                try:
                                    retry_msgs2 = _format_messages(prompt + " ", input_json, use_batch_mode)
                                    orig_cache = litellm.cache
                                    litellm.cache = None
                                    rr2 = litellm.completion(
                                        model=model_name_litellm,
                                        messages=retry_msgs2,
                                        temperature=current_temperature,
                                        response_format=response_format,
                                        timeout=LLM_CALL_TIMEOUT,
                                        **time_kwargs,
                                        **retry_provider_kwargs,
                                    )
                                    litellm.cache = orig_cache
                                    rr2c = rr2.choices[0].message.content
                                    if rr2c and not _is_malformed_json_response(rr2c):
                                        raw_result = rr2c
                                except Exception:
                                    litellm.cache = configured_cache

                        # Parse structured output
                        if output_pydantic or output_schema:
                            parsed_result: Any = None
                            json_string_to_parse: Optional[str] = None

                            try:
                                if output_pydantic and isinstance(raw_result, output_pydantic):
                                    parsed_result = raw_result
                                elif isinstance(raw_result, dict):
                                    if output_pydantic:
                                        parsed_result = output_pydantic.model_validate(raw_result)
                                    else:
                                        parsed_result = json.dumps(raw_result)
                                elif isinstance(raw_result, str):
                                    json_string_to_parse = raw_result
                                    fenced = _extract_fenced_json_block(raw_result)
                                    cands2: List[str] = [fenced] if fenced else _extract_balanced_json_objects(raw_result)

                                    if not cands2:
                                        cleaned = raw_result.strip()
                                        if cleaned.startswith("```json"):
                                            cleaned = cleaned[7:]
                                        elif cleaned.startswith("```"):
                                            cleaned = cleaned[3:]
                                        if cleaned.endswith("```"):
                                            cleaned = cleaned[:-3]
                                        cleaned = cleaned.strip()
                                        if cleaned:
                                            cands2.append(cleaned)

                                    pe: Optional[Exception] = None
                                    for cand in cands2:
                                        try:
                                            if output_pydantic:
                                                parsed_result = output_pydantic.model_validate_json(cand)
                                            else:
                                                parsed_result = cand
                                            json_string_to_parse = cand
                                            pe = None
                                            break
                                        except (json.JSONDecodeError, ValidationError, ValueError) as e2:
                                            pe = e2

                                    if parsed_result is None and pe:
                                        # Try truncated JSON repair
                                        stripped = raw_result.strip()
                                        if stripped.startswith("{"):
                                            repairs = [stripped + '"}}', stripped + '"}', stripped.rstrip(",") + "}"]
                                            for attempt in repairs:
                                                try:
                                                    if output_pydantic:
                                                        parsed_result = output_pydantic.model_validate_json(attempt)
                                                    else:
                                                        parsed_result = attempt
                                                    break
                                                except Exception:
                                                    continue
                                        if parsed_result is None:
                                            raise pe  # type: ignore[misc]

                                if parsed_result is None:
                                    raise SchemaValidationError(
                                        f"Could not parse response for item {idx}",
                                        raw_response=raw_result,
                                        item_index=idx,
                                    )

                            except (ValidationError, json.JSONDecodeError, TypeError, ValueError, Exception) as parse_err:
                                raise SchemaValidationError(
                                    f"Failed to parse response: {parse_err}",
                                    raw_response=raw_result,
                                    item_index=idx,
                                ) from parse_err

                            _unescape_code_newlines(parsed_result)

                            # Python syntax check + retry
                            if language in (None, "python") and _has_invalid_python_code(parsed_result):
                                if not use_batch_mode and prompt and input_json is not None:
                                    try:
                                        rm3 = _format_messages(prompt + "  ", input_json, use_batch_mode)
                                        oc3 = litellm.cache
                                        litellm.cache = None
                                        rr3 = litellm.completion(
                                            model=model_name_litellm,
                                            messages=rm3,
                                            temperature=current_temperature,
                                            response_format=response_format,
                                            timeout=LLM_CALL_TIMEOUT,
                                            **time_kwargs,
                                            **retry_provider_kwargs,
                                        )
                                        litellm.cache = oc3
                                        rr3c = rr3.choices[0].message.content
                                        if rr3c is not None:
                                            rp: Any = None
                                            if output_pydantic:
                                                if isinstance(rr3c, output_pydantic):
                                                    rp = rr3c
                                                elif isinstance(rr3c, dict):
                                                    rp = output_pydantic.model_validate(rr3c)
                                                elif isinstance(rr3c, str):
                                                    rp = output_pydantic.model_validate_json(rr3c)
                                            if rp is not None:
                                                _unescape_code_newlines(rp)
                                                if not _has_invalid_python_code(rp):
                                                    parsed_result = rp
                                    except Exception:
                                        litellm.cache = configured_cache
                                else:
                                    logger.warning("Cannot retry invalid Python code – batch mode or missing prompt/input_json")

                            results.append(parsed_result)
                        else:
                            results.append(raw_result)

                    except SchemaValidationError:
                        raise
                    except (AttributeError, IndexError) as exc2:
                        results.append(f"ERROR: Could not extract result: {exc2}")

                total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                final_result2 = results if use_batch_mode else results[0]
                final_thinking = thinking_outputs if use_batch_mode else thinking_outputs[0]

                if verbose:
                    in_tok = _LAST_CALLBACK_DATA.get("input_tokens", 0)
                    out_tok = _LAST_CALLBACK_DATA.get("output_tokens", 0)
                    cost_in = model_info.get("input", 0.0) if pd.notna(model_info.get("input")) else 0.0
                    cost_out = model_info.get("output", 0.0) if pd.notna(model_info.get("output")) else 0.0
                    logger.info("[RESULT] Model Used: %s", model_name_litellm)
                    logger.info("[RESULT] Cost (Input): $%.2f/M tokens", cost_in)
                    logger.info("[RESULT] Cost (Output): $%.2f/M tokens", cost_out)
                    logger.info("[RESULT] Tokens (Prompt): %d", in_tok)
                    logger.info("[RESULT] Tokens (Completion): %d", out_tok)
                    logger.info("[RESULT] Total Cost (from callback): $%s", f"{total_cost:.6g}")
                    logger.info("[RESULT] Max Completion Tokens: Provider Default")
                    if final_thinking:
                        logger.info("[RESULT] Thinking Output:")
                        logger.info(final_thinking)

                return {
                    "result": final_result2,
                    "cost": total_cost,
                    "model_name": model_name_litellm,
                    "thinking_output": final_thinking if final_thinking else None,
                }

            except openai.AuthenticationError as exc:
                last_exception = exc
                err_msg = str(exc)
                if _is_wsl_environment() and ("Illegal header value" in err_msg or "\r" in err_msg):
                    logger.warning("[WSL AUTH ERROR] Detected WSL line ending issue in API key")

                if newly_acquired_keys.get(api_key_name):
                    logger.warning("[AUTH ERROR] Auth failed with newly provided key '%s'. Re-prompting.", api_key_name)
                    if api_key_name and api_key_name in os.environ:
                        del os.environ[api_key_name]
                    newly_acquired_keys[api_key_name or ""] = False
                    retry_with_same_model = True
                else:
                    logger.warning("[AUTH ERROR] Auth failed for %s. Trying next model.", model_name_litellm)
                    break

            except SchemaValidationError as exc:
                last_exception = exc
                logger.warning("[SCHEMA ERROR] Validation failed for %s: %s. Trying next model.", model_name_litellm, exc)
                break

            except Exception as exc:
                last_exception = exc
                lower_err = str(exc).lower()

                if not temp_adjustment_done and "temperature" in lower_err and "thinking" in lower_err:
                    if provider == "anthropic" and "thinking" in litellm_kwargs:
                        current_temperature = 1
                    else:
                        current_temperature = 0.99
                    temp_adjustment_done = True
                    retry_with_same_model = True
                    continue

                logger.error("[ERROR] %s failed (%s): %s. Trying next model.", model_name_litellm, type(exc).__name__, exc)
                break

        continue

    error_msg = "All candidate models failed."
    if last_exception:
        error_msg += f" Last error ({type(last_exception).__name__}): {last_exception}"
    logger.error("[FATAL] %s", error_msg)
    raise RuntimeError(error_msg) from last_exception