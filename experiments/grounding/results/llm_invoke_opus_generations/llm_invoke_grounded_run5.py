from __future__ import annotations

import importlib.resources
import json
import logging
import os
import re
import time as time_module
import warnings
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Type, Union

import litellm
import openai
import pandas as pd
from dotenv import load_dotenv
from litellm.caching.caching import Cache
from pydantic import BaseModel, ValidationError
from rich.console import Console

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

console = Console()

# ------------------------------------------------------------------------------
# Logging Configuration
# ------------------------------------------------------------------------------

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

try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

try:
    _drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_params_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

if not logger.handlers:
    console_handler = logging.StreamHandler()
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(console_handler)


def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    if not log_file_path:
        return

    try:
        from logging.handlers import RotatingFileHandler

        file_handler = RotatingFileHandler(log_file_path, maxBytes=10 * 1024 * 1024, backupCount=5)
        file_handler.setFormatter(
            logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
        )
        logger.addHandler(file_handler)
        litellm_logger.addHandler(file_handler)
        logger.info("File logging configured to: %s", log_file_path)
    except Exception as exc:
        logger.warning("Failed to set up file logging: %s", exc)


def set_verbose_logging(verbose: bool = False) -> None:
    want_verbose = bool(verbose) or os.getenv("PDD_VERBOSE_LOGGING") == "1"
    if want_verbose:
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)
    else:
        if PRODUCTION_MODE:
            logger.setLevel(logging.WARNING)
        else:
            logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))
        litellm_logger.setLevel(getattr(logging, litellm_log_level, logging.WARNING))

    try:
        if hasattr(litellm, "set_verbose"):
            litellm.set_verbose = want_verbose
        if hasattr(litellm, "suppress_debug_info"):
            litellm.suppress_debug_info = not want_verbose
    except Exception:
        pass


# ------------------------------------------------------------------------------
# Exceptions
# ------------------------------------------------------------------------------


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


# ------------------------------------------------------------------------------
# Schema Utilities
# ------------------------------------------------------------------------------


def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
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
            for sub_schema in schema[key]:
                _ensure_all_properties_required(sub_schema)

    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            _ensure_all_properties_required(def_schema)

    return schema


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
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
            for sub_schema in schema[key]:
                _add_additional_properties_false(sub_schema)

    if "$defs" in schema:
        for def_schema in schema["$defs"].values():
            _add_additional_properties_false(def_schema)

    return schema


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    if isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    if isinstance(result, pydantic_class):
        return result
    raise ValueError(f"Cannot validate result type {type(result)} with Pydantic model")


# ------------------------------------------------------------------------------
# Cloud invocation
# ------------------------------------------------------------------------------


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

    from .core.cloud import CloudConfig

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
                except (ValidationError, ValueError) as exc:
                    logger.warning("Cloud response validation failed: %s", exc)
            return {
                "result": result,
                "cost": data.get("totalCost", 0.0),
                "model_name": data.get("modelName", "cloud_model"),
                "thinking_output": data.get("thinkingOutput"),
            }

        if response.status_code == 402:
            error_msg = response.json().get("error", "Insufficient credits")
            raise InsufficientCreditsError(error_msg)

        if response.status_code in (401, 403):
            try:
                from .auth_service import clear_jwt_cache

                clear_jwt_cache()
            except Exception:
                pass

            server_error = response.json().get("error", "")
            error_msg = (
                f"Authentication expired ({server_error or response.status_code}). "
                "Please re-authenticate with: pdd auth logout && pdd auth login"
            )
            raise CloudFallbackError(error_msg)

        if response.status_code >= 500:
            error_msg = response.json().get("error", f"Server error ({response.status_code})")
            raise CloudFallbackError(error_msg)

        error_msg = response.json().get("error", f"HTTP {response.status_code}")
        raise CloudInvocationError(f"Cloud llm_invoke failed: {error_msg}")

    except requests.exceptions.Timeout as exc:
        raise CloudFallbackError("Cloud request timed out") from exc
    except requests.exceptions.ConnectionError as exc:
        raise CloudFallbackError(f"Cloud connection failed: {exc}") from exc
    except requests.exceptions.RequestException as exc:
        raise CloudFallbackError(f"Cloud request failed: {exc}") from exc


# ------------------------------------------------------------------------------
# Environment / project setup
# ------------------------------------------------------------------------------


def _is_wsl_environment() -> bool:
    try:
        if os.path.exists("/proc/version"):
            with open("/proc/version", "r") as handle:
                version_info = handle.read().lower()
                return "microsoft" in version_info or "wsl" in version_info
        if os.getenv("WSL_DISTRO_NAME"):
            return True
        return "/mnt/c/" in os.getenv("PATH", "").lower()
    except Exception:
        return False


def _get_environment_info() -> Dict[str, str]:
    import platform

    info = {
        "platform": platform.system(),
        "platform_release": platform.release(),
        "platform_version": platform.version(),
        "architecture": platform.machine(),
        "is_wsl": str(_is_wsl_environment()),
        "python_version": platform.python_version(),
    }
    if _is_wsl_environment():
        info["wsl_distro"] = os.getenv("WSL_DISTRO_NAME", "unknown")
        info["wsl_interop"] = os.getenv("WSL_INTEROP", "not_set")
    return info


LLM_CALL_TIMEOUT = 120

resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env
logger.debug("Using PROJECT_ROOT: %s", PROJECT_ROOT)

user_pdd_dir = Path.home() / ".pdd"
user_model_csv_path = user_pdd_dir / "llm_model.csv"


def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    try:
        current_dir = Path.cwd().resolve()
        for _ in range(max_levels):
            if (
                (current_dir / ".git").exists()
                or (current_dir / "pyproject.toml").exists()
                or (current_dir / "data").is_dir()
                or (current_dir / ".env").exists()
            ):
                return current_dir
            parent = current_dir.parent
            if parent == current_dir:
                break
            current_dir = parent
    except Exception:
        pass
    return Path.cwd().resolve()


project_root_from_cwd = _detect_project_root_from_cwd()
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"

try:
    _installed_pkg_root = importlib.resources.files("pdd")
    try:
        _installed_pkg_root_path = Path(str(_installed_pkg_root))
    except Exception:
        _installed_pkg_root_path = None
except Exception:
    _installed_pkg_root_path = None


def _is_env_path_package_dir(env_path: Path) -> bool:
    try:
        if _installed_pkg_root_path is None:
            return False
        env_path = env_path.resolve()
        pkg_path = _installed_pkg_root_path.resolve()
        return env_path == pkg_path or str(env_path).startswith(str(pkg_path))
    except Exception:
        return False


if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
    logger.debug("PDD_PATH points to package; using ENV_PATH from CWD: %s", ENV_PATH)
else:
    ENV_PATH = PROJECT_ROOT / ".env"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH: Optional[Path] = user_model_csv_path
    logger.info("Using user-specific LLM model CSV: %s", LLM_MODEL_CSV_PATH)
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
    logger.info("Using project-specific LLM model CSV (from PDD_PATH): %s", LLM_MODEL_CSV_PATH)
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
    logger.info("Using project-specific LLM model CSV (from CWD): %s", LLM_MODEL_CSV_PATH)
else:
    LLM_MODEL_CSV_PATH = None
    logger.info("No local LLM model CSV found, will use package default")

logger.debug("Attempting to load .env from: %s", ENV_PATH)
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)
    logger.debug("Loaded .env file from: %s", ENV_PATH)
else:
    logger.debug(".env file not found at %s. API keys might need to be provided manually.", ENV_PATH)

DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", None)

# ------------------------------------------------------------------------------
# LiteLLM cache setup
# ------------------------------------------------------------------------------

GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_ENDPOINT_URL = "https://storage.googleapis.com"
GCS_REGION_NAME = os.getenv("GCS_REGION_NAME", "auto")
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID")
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")

if GCS_HMAC_ACCESS_KEY_ID:
    GCS_HMAC_ACCESS_KEY_ID = GCS_HMAC_ACCESS_KEY_ID.strip()
if GCS_HMAC_SECRET_ACCESS_KEY:
    GCS_HMAC_SECRET_ACCESS_KEY = GCS_HMAC_SECRET_ACCESS_KEY.strip()

cache_configured = False
configured_cache: Optional[Cache] = None

if GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    original_aws_access_key_id = os.environ.get("AWS_ACCESS_KEY_ID")
    original_aws_secret_access_key = os.environ.get("AWS_SECRET_ACCESS_KEY")
    original_aws_region_name = os.environ.get("AWS_REGION_NAME")

    try:
        os.environ["AWS_ACCESS_KEY_ID"] = GCS_HMAC_ACCESS_KEY_ID
        os.environ["AWS_SECRET_ACCESS_KEY"] = GCS_HMAC_SECRET_ACCESS_KEY
        configured_cache = Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_region_name=GCS_REGION_NAME,
            s3_endpoint_url=GCS_ENDPOINT_URL,
        )
        litellm.cache = configured_cache
        logger.info("LiteLLM cache configured for GCS bucket (S3 compatible): %s", GCS_BUCKET_NAME)
        cache_configured = True
    except Exception as exc:
        warnings.warn(f"Failed to configure LiteLLM S3/GCS cache: {exc}. Attempting SQLite cache fallback.")
        litellm.cache = None
    finally:
        if original_aws_access_key_id is not None:
            os.environ["AWS_ACCESS_KEY_ID"] = original_aws_access_key_id
        elif "AWS_ACCESS_KEY_ID" in os.environ:
            del os.environ["AWS_ACCESS_KEY_ID"]

        if original_aws_secret_access_key is not None:
            os.environ["AWS_SECRET_ACCESS_KEY"] = original_aws_secret_access_key
        elif "AWS_SECRET_ACCESS_KEY" in os.environ:
            del os.environ["AWS_SECRET_ACCESS_KEY"]

        if original_aws_region_name is not None:
            os.environ["AWS_REGION_NAME"] = original_aws_region_name

if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    logger.info("LiteLLM caching disabled via LITELLM_CACHE_DISABLE=1")
    litellm.cache = None
    cache_configured = True

if not cache_configured:
    try:
        sqlite_cache_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_cache_path))
        litellm.cache = configured_cache
        logger.info("LiteLLM disk cache configured at %s", sqlite_cache_path)
        cache_configured = True
    except Exception as exc:
        warnings.warn(f"Failed to configure LiteLLM disk cache: {exc}. Caching is disabled.")
        litellm.cache = None

if not cache_configured:
    warnings.warn("All LiteLLM cache configuration attempts failed. Caching is disabled.")
    litellm.cache = None

# ------------------------------------------------------------------------------
# LiteLLM callback
# ------------------------------------------------------------------------------

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
    input_tokens = getattr(usage, "prompt_tokens", 0)
    output_tokens = getattr(usage, "completion_tokens", 0)
    finish_reason = getattr(completion_response.choices[0], "finish_reason", None)

    calculated_cost = 0.0
    try:
        cost_val = litellm.completion_cost(completion_response=completion_response)
        calculated_cost = cost_val if cost_val is not None else 0.0
    except Exception as exc:
        logger.debug("Attempting cost calculation with fallback method: %s", exc)
        try:
            model_name = kwargs.get("model")
            if model_name and usage:
                in_tok = getattr(usage, "prompt_tokens", None)
                out_tok = getattr(usage, "completion_tokens", None)
                if in_tok is None:
                    in_tok = getattr(usage, "input_tokens", 0)
                if out_tok is None:
                    out_tok = getattr(usage, "output_tokens", 0)

                try:
                    cost_val = litellm.completion_cost(
                        model=model_name,
                        prompt_tokens=in_tok,
                        completion_tokens=out_tok,
                    )
                    calculated_cost = cost_val if cost_val is not None else 0.0
                except TypeError:
                    try:
                        cost_val = litellm.completion_cost(
                            model=model_name,
                            input_tokens=in_tok,
                            output_tokens=out_tok,
                        )
                        calculated_cost = cost_val if cost_val is not None else 0.0
                    except Exception as exc2:
                        rates = _MODEL_RATE_MAP.get(str(model_name))
                        if rates is not None:
                            in_rate, out_rate = rates
                            calculated_cost = (
                                float(in_tok or 0) * in_rate + float(out_tok or 0) * out_rate
                            ) / 1_000_000.0
                        else:
                            calculated_cost = 0.0
                        logger.debug(
                            "Cost calculation failed with LiteLLM token API; used CSV rates if available. Detail: %s",
                            exc2,
                        )
            else:
                calculated_cost = 0.0
        except Exception as exc3:
            calculated_cost = 0.0
            logger.debug("Cost calculation failed with fallback method: %s", exc3)

    _LAST_CALLBACK_DATA["input_tokens"] = input_tokens
    _LAST_CALLBACK_DATA["output_tokens"] = output_tokens
    _LAST_CALLBACK_DATA["finish_reason"] = finish_reason
    _LAST_CALLBACK_DATA["cost"] = calculated_cost


litellm.success_callback = [_litellm_success_callback]

# ------------------------------------------------------------------------------
# Helper Functions
# ------------------------------------------------------------------------------


def _is_malformed_json_response(content: str, threshold: int = 100) -> bool:
    if not content or not isinstance(content, str):
        return False
    stripped = content.strip()
    if not stripped.startswith("{"):
        return False
    if stripped.endswith("}"):
        return False

    trailing_newline_count = 0
    check_content = stripped
    while check_content.endswith("\\n"):
        trailing_newline_count += 1
        check_content = check_content[:-2]

    if trailing_newline_count >= threshold:
        return True

    if not stripped.endswith("}") and not stripped.endswith("]") and not stripped.endswith('"'):
        if stripped.endswith("\\"):
            return True

    return False


def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    if csv_path is not None:
        if not csv_path.exists():
            logger.warning("Specified LLM model CSV not found at %s, trying package default", csv_path)
            csv_path = None
        else:
            try:
                df = pd.read_csv(csv_path)
                logger.debug("Loaded model data from %s", csv_path)
            except Exception as exc:
                logger.warning("Failed to load CSV from %s: %s, trying package default", csv_path, exc)
                csv_path = None

    if csv_path is None:
        try:
            csv_data = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
            import io

            df = pd.read_csv(io.StringIO(csv_data))
            logger.info("Loaded model data from package default")
        except Exception as exc:
            raise FileNotFoundError(
                f"Failed to load default LLM model CSV from package: {exc}"
            ) from exc

    try:
        required_cols = [
            "provider",
            "model",
            "input",
            "output",
            "coding_arena_elo",
            "api_key",
            "structured_output",
            "reasoning_type",
        ]
        for col in required_cols:
            if col not in df.columns:
                raise ValueError(f"Missing required column in CSV: {col}")

        numeric_cols = [
            "input",
            "output",
            "coding_arena_elo",
            "max_tokens",
            "max_completion_tokens",
            "max_reasoning_tokens",
        ]
        for col in numeric_cols:
            if col in df.columns:
                df[col] = pd.to_numeric(df[col], errors="coerce")

        df["input"] = df["input"].fillna(0.0)
        df["output"] = df["output"].fillna(0.0)
        df["coding_arena_elo"] = df["coding_arena_elo"].fillna(0)
        df["max_reasoning_tokens"] = df["max_reasoning_tokens"].fillna(0).astype(int)

        df["avg_cost"] = (df["input"] + df["output"]) / 2

        if "structured_output" in df.columns:
            df["structured_output"] = df["structured_output"].fillna(False).astype(bool)
        else:
            df["structured_output"] = False

        df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
        df["api_key"] = df["api_key"].fillna("").astype(str)

        return df
    except Exception as exc:
        raise RuntimeError(f"Error loading or processing LLM model CSV {csv_path}: {exc}") from exc


def _select_model_candidates(
    strength: float,
    base_model_name: Optional[str],
    model_df: pd.DataFrame,
) -> List[Dict[str, Any]]:
    if model_df.empty:
        raise ValueError("Loaded model data is empty. Check CSV file.")

    available_df = model_df[model_df["api_key"].notna()].copy()
    if available_df.empty:
        logger.warning("No models found after filtering for non-NaN api_key.")
        raise ValueError("No models available after initial filtering (all had NaN 'api_key'?).")

    base_model_row = available_df[available_df["model"] == base_model_name] if base_model_name else pd.DataFrame()
    if base_model_row.empty:
        original_base = model_df[model_df["model"] == base_model_name] if base_model_name else pd.DataFrame()
        if not original_base.empty:
            raise ValueError(
                f"Base model '{base_model_name}' found in CSV but requires API key "
                f"'{original_base.iloc[0]['api_key']}' which might be missing or invalid configuration."
            )
        base_model = available_df.iloc[0]
    else:
        base_model = base_model_row.iloc[0]

    candidates: List[Dict[str, Any]]
    target_metric_value: Optional[str] = None

    if strength == 0.5:
        available_df["sort_metric"] = -available_df["coding_arena_elo"]
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")
        effective_base_name = str(base_model["model"]) if isinstance(base_model, pd.Series) else base_model_name
        if any(c["model"] == effective_base_name for c in candidates):
            candidates.sort(key=lambda x: 0 if x["model"] == effective_base_name else 1)
        target_metric_value = f"Base Model ELO: {base_model['coding_arena_elo']}"
    elif strength < 0.5:
        base_cost = base_model["avg_cost"]
        cheapest_model = available_df.loc[available_df["avg_cost"].idxmin()]
        cheapest_cost = cheapest_model["avg_cost"]
        if base_cost <= cheapest_cost:
            target_cost = cheapest_cost + strength * (base_cost - cheapest_cost)
        else:
            target_cost = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost)
        available_df["sort_metric"] = abs(available_df["avg_cost"] - target_cost)
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")
        target_metric_value = f"Target Cost: {target_cost:.6f}"
    else:
        base_elo = base_model["coding_arena_elo"]
        highest_elo_model = available_df.loc[available_df["coding_arena_elo"].idxmax()]
        highest_elo = highest_elo_model["coding_arena_elo"]
        if highest_elo <= base_elo:
            target_elo = base_elo + (strength - 0.5) * (highest_elo - base_elo)
        else:
            target_elo = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo)
        available_df["sort_metric"] = abs(available_df["coding_arena_elo"] - target_elo)
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")
        target_metric_value = f"Target ELO: {target_elo:.2f}"

    if not candidates:
        raise RuntimeError("Model selection resulted in an empty candidate list.")

    if os.getenv("PDD_DEBUG_SELECTOR"):
        logger.debug("--- DEBUG: _select_model_candidates ---")
        logger.debug("Strength: %s, Base Model: %s", strength, base_model_name)
        logger.debug("Metric: %s", target_metric_value)
        logger.debug("Available DF (Sorted by metric): %s", available_df.sort_values(by="sort_metric"))
        logger.debug("Final Candidates List (Model Names): %s", [c["model"] for c in candidates])
        logger.debug("---------------------------------------")

    return candidates


def _sanitize_api_key(key_value: Optional[str]) -> Optional[str]:
    if not key_value:
        return key_value
    sanitized = key_value.strip()
    if any(ord(c) < 32 for c in sanitized):
        logger.warning("API key contains control characters that may cause issues")
        sanitized = "".join(c for c in sanitized if ord(c) >= 32)
    if sanitized and len(sanitized) < 10:
        logger.warning("API key appears too short (%s characters)", len(sanitized))
    if sanitized and not all(32 <= ord(c) <= 126 for c in sanitized):
        logger.warning("API key contains non-printable characters")
    if key_value != sanitized and "\r" in key_value:
        if _is_wsl_environment():
            logger.info("Detected and fixed WSL line ending issue in API key")
        else:
            logger.info("Detected and fixed line ending issue in API key")
    return sanitized


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    lines: List[str] = []
    if env_path.exists():
        with open(env_path, "r") as handle:
            lines = handle.readlines()

    new_lines: List[str] = []
    key_replaced = False
    prefix = f"{key_name}="
    prefix_spaced = f"{key_name} ="

    for line in lines:
        stripped = line.strip()
        if stripped.startswith(f"# {prefix}") or stripped.startswith(f"# {prefix_spaced}"):
            continue
        if stripped.startswith(prefix) or stripped.startswith(prefix_spaced):
            new_lines.append(f'{key_name}="{value}"\n')
            key_replaced = True
        else:
            new_lines.append(line)

    if not key_replaced:
        if new_lines and not new_lines[-1].endswith("\n"):
            new_lines.append("\n")
        new_lines.append(f'{key_name}="{value}"\n')

    with open(env_path, "w") as handle:
        handle.writelines(new_lines)


def _ensure_api_key(
    model_info: Dict[str, Any],
    newly_acquired_keys: Dict[str, bool],
    verbose: bool,
) -> bool:
    key_name = model_info.get("api_key")

    if not key_name or key_name == "EXISTING_KEY":
        if verbose:
            logger.info("Skipping API key check for model %s (key name: %s)", model_info.get("model"), key_name)
        return True

    key_value = os.getenv(key_name)
    if key_value:
        key_value = _sanitize_api_key(key_value)

    if key_value:
        if verbose:
            logger.info("API key '%s' found in environment.", key_name)
        newly_acquired_keys[key_name] = False
        return True

    logger.warning(
        "API key environment variable '%s' for model '%s' is not set.",
        key_name,
        model_info.get("model"),
    )

    if os.environ.get("PDD_FORCE"):
        logger.error("API key '%s' not set. In --force mode, skipping interactive prompt.", key_name)
        return False

    try:
        user_provided_key = input(f"Please enter the API key for {key_name}: ").strip()
        if not user_provided_key:
            logger.error("No API key provided. Cannot proceed with this model.")
            return False

        user_provided_key = _sanitize_api_key(user_provided_key) or ""
        os.environ[key_name] = user_provided_key
        logger.info("API key '%s' set for the current session.", key_name)
        newly_acquired_keys[key_name] = True

        try:
            _save_key_to_env_file(key_name, user_provided_key, ENV_PATH)
            logger.info("API key '%s' saved to %s.", key_name, ENV_PATH)
            logger.warning(
                "SECURITY WARNING: The API key has been saved to your .env file. "
                "Ensure this file is kept secure and is included in your .gitignore."
            )
        except IOError as exc:
            logger.error("Failed to update .env file at %s: %s", ENV_PATH, exc)

        return True
    except EOFError:
        logger.error("Cannot prompt for API key '%s' in a non-interactive environment.", key_name)
        return False
    except Exception as exc:
        logger.error("An unexpected error occurred during API key acquisition: %s", exc)
        return False


def _format_messages(
    prompt: str,
    input_data: Union[Dict[str, Any], List[Dict[str, Any]]],
    use_batch_mode: bool,
) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    try:
        if use_batch_mode:
            if not isinstance(input_data, list):
                raise ValueError("input_json must be a list of dictionaries when use_batch_mode is True.")
            all_messages: List[List[Dict[str, str]]] = []
            for item in input_data:
                if not isinstance(item, dict):
                    raise ValueError("Each item in input_json list must be a dictionary for batch mode.")
                formatted_prompt = prompt.format(**item)
                all_messages.append([{"role": "user", "content": formatted_prompt}])
            return all_messages
        if not isinstance(input_data, dict):
            raise ValueError("input_json must be a dictionary when use_batch_mode is False.")
        formatted_prompt = prompt.format(**input_data)
        return [{"role": "user", "content": formatted_prompt}]
    except KeyError as exc:
        raise ValueError(f"Prompt formatting error: Missing key {exc} in input_json for prompt string.") from exc
    except Exception as exc:
        raise ValueError(f"Error formatting prompt: {exc}") from exc


def _extract_fenced_json_block(text: str) -> Optional[str]:
    try:
        match = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, flags=re.IGNORECASE)
        if match:
            return match.group(1)
        return None
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


def _looks_like_python_code(s: Optional[str]) -> bool:
    if not s or len(s) < 10:
        return False
    code_indicators = ("def ", "class ", "import ", "from ", "if __name__", "return ", "print(")
    return any(indicator in s for indicator in code_indicators)


_PROSE_FIELD_NAMES = frozenset(
    {
        "reasoning",
        "explanation",
        "analysis",
        "change_instructions",
        "change_description",
        "planned_modifications",
        "details",
        "description",
        "focus",
        "file_summary",
    }
)


def _is_prose_field_name(field_name: str) -> bool:
    return field_name.lower() in _PROSE_FIELD_NAMES


def _repair_python_syntax(code: str) -> str:
    import ast

    if not code or not code.strip():
        return code

    try:
        ast.parse(code)
        return code
    except SyntaxError:
        pass

    repaired = code
    for quote in ['"', "'"]:
        if repaired.rstrip().endswith(quote):
            candidate = repaired.rstrip()[:-1]
            try:
                ast.parse(candidate)
                logger.info("[INFO] Repaired code by removing trailing %r", quote)
                return candidate
            except SyntaxError:
                pass

    for quote in ['"', "'"]:
        if repaired.lstrip().startswith(quote):
            candidate = repaired.lstrip()[1:]
            try:
                ast.parse(candidate)
                logger.info("[INFO] Repaired code by removing leading %r", quote)
                return candidate
            except SyntaxError:
                pass

    for quote in ['"', "'"]:
        stripped = repaired.strip()
        if stripped.startswith(quote) and stripped.endswith(quote):
            candidate = stripped[1:-1]
            try:
                ast.parse(candidate)
                logger.info("[INFO] Repaired code by removing surrounding %r", quote)
                return candidate
            except SyntaxError:
                pass

    return code


def _smart_unescape_code(code: str) -> str:
    literal_backslash_n = "\\" + "n"
    if literal_backslash_n not in code:
        return code

    has_actual_newlines = "\n" in code
    if has_actual_newlines:
        return code

    result: List[str] = []
    i = 0
    in_string = False
    string_char: Optional[str] = None

    PLACEHOLDER = "\x00NEWLINE_ESCAPE\x00"

    while i < len(code):
        if i + 1 < len(code) and code[i] == "\\":
            next_char = code[i + 1]
            if in_string:
                if next_char == "n":
                    result.append(PLACEHOLDER)
                    i += 2
                    continue
                if next_char == "t":
                    result.append("\\t")
                    i += 2
                    continue
                if next_char == "r":
                    result.append("\\r")
                    i += 2
                    continue
                if next_char in ('"', "'", "\\"):
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
            if code[i] in ('"', "'"):
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
            elif code[i] == string_char:
                in_string = False
                result.append(code[i])
                i += 1
                continue

        result.append(code[i])
        i += 1

    intermediate = "".join(result)
    intermediate = intermediate.replace("\\r\\n", "\r\n")
    intermediate = intermediate.replace(literal_backslash_n, "\n")
    intermediate = intermediate.replace("\\t", "\t")

    return intermediate.replace(PLACEHOLDER, "\\n")


def _unescape_code_newlines(obj: Any) -> Any:
    if obj is None:
        return obj

    def _process_string(s: str) -> str:
        result = s
        if _looks_like_python_code(result):
            result = _smart_unescape_code(result)
            result = _repair_python_syntax(result)
        else:
            if "\\n" in result:
                result = result.replace("\\r\\n", "\r\n")
                result = result.replace("\\n", "\n")
                result = result.replace("\\t", "\t")
        return result

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
        for idx, item in enumerate(obj):
            if isinstance(item, str):
                obj[idx] = _process_string(item)
            elif isinstance(item, (dict, list, BaseModel)):
                _unescape_code_newlines(item)
        return obj

    return obj


def _has_invalid_python_code(obj: Any, field_name: str = "") -> bool:
    import ast

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
            value = getattr(obj, name)
            if _has_invalid_python_code(value, field_name=name):
                return True
        return False

    if isinstance(obj, dict):
        for key, value in obj.items():
            fname = key if isinstance(key, str) else ""
            if _has_invalid_python_code(value, field_name=fname):
                return True
        return False

    if isinstance(obj, list):
        for item in obj:
            if _has_invalid_python_code(item, field_name=field_name):
                return True
        return False

    return False


# ------------------------------------------------------------------------------
# Main Function
# ------------------------------------------------------------------------------


def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    time: Optional[float] = DEFAULT_TIME,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    set_verbose_logging(verbose)

    if verbose:
        logger.debug("llm_invoke start - Arguments received:")
        logger.debug("  prompt: %s", "provided" if prompt else "None")
        logger.debug("  input_json: %s", "provided" if input_json is not None else "None")
        logger.debug("  strength: %s", strength)
        logger.debug("  temperature: %s", temperature)
        logger.debug("  verbose: %s", verbose)
        logger.debug("  output_pydantic: %s", output_pydantic.__name__ if output_pydantic else "None")
        logger.debug("  time: %s", time)
        logger.debug("  use_batch_mode: %s", use_batch_mode)
        logger.debug("  messages: %s", "provided" if messages else "None")
        logger.debug("  use_cloud: %s", use_cloud)

    if use_cloud is None:
        force_local = os.environ.get("PDD_FORCE_LOCAL", "").lower() in ("1", "true", "yes")
        if force_local:
            use_cloud = False
        else:
            try:
                from .core.cloud import CloudConfig

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
                time=time or 0.0,
                use_batch_mode=use_batch_mode,
                messages=messages,
                language=language,
            )
        except CloudFallbackError as exc:
            console.print(
                f"[yellow]Cloud execution failed ({exc}), falling back to local execution...[/yellow]"
            )
            logger.warning("Cloud fallback: %s", exc)
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as exc:
            console.print(f"[yellow]Cloud error ({exc}), falling back to local execution...[/yellow]")
            logger.warning("Cloud invocation error: %s", exc)

    if messages:
        if verbose:
            logger.info("Using provided 'messages' input.")
        if use_batch_mode:
            if not isinstance(messages, list) or not all(isinstance(m_list, list) for m_list in messages):
                raise ValueError("'messages' must be a list of lists when use_batch_mode is True.")
            if not all(
                isinstance(msg, dict) and "role" in msg and "content" in msg
                for m_list in messages
                for msg in m_list
            ):
                raise ValueError(
                    "Each message in the lists within 'messages' must be a dictionary with 'role' and 'content'."
                )
        else:
            if not isinstance(messages, list) or not all(
                isinstance(msg, dict) and "role" in msg and "content" in msg for msg in messages
            ):
                raise ValueError("'messages' must be a list of dictionaries with 'role' and 'content'.")
        formatted_messages = messages
    elif prompt and input_json is not None:
        if not isinstance(prompt, str) or not prompt:
            raise ValueError("'prompt' must be a non-empty string when 'messages' is not provided.")
        formatted_messages = _format_messages(prompt, input_json, use_batch_mode)
    else:
        raise ValueError("Either 'messages' or both 'prompt' and 'input_json' must be provided.")

    if time is None:
        time = 0.0

    if not (0.0 <= strength <= 1.0):
        raise ValueError("'strength' must be between 0.0 and 1.0.")
    if not (0.0 <= temperature <= 2.0):
        warnings.warn("'temperature' is outside the typical range (0.0-2.0).")
    if not (0.0 <= time <= 1.0):
        raise ValueError("'time' must be between 0.0 and 1.0.")

    try:
        model_df = _load_model_data(LLM_MODEL_CSV_PATH)
        candidate_models = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    except (FileNotFoundError, ValueError, RuntimeError) as exc:
        logger.error("Failed during model loading or selection: %s", exc)
        raise

    if verbose:
        min_cost = model_df["avg_cost"].min()
        max_elo = model_df["coding_arena_elo"].max()
        base_cost = (
            model_df[model_df["model"] == DEFAULT_BASE_MODEL]["avg_cost"].iloc[0]
            if not model_df[model_df["model"] == DEFAULT_BASE_MODEL].empty
            else min_cost
        )
        base_elo = (
            model_df[model_df["model"] == DEFAULT_BASE_MODEL]["coding_arena_elo"].iloc[0]
            if not model_df[model_df["model"] == DEFAULT_BASE_MODEL].empty
            else max_elo
        )

        def calc_strength(candidate: Dict[str, Any]) -> float:
            avg_cost = candidate.get("avg_cost", min_cost)
            elo = candidate.get("coding_arena_elo", base_elo)
            if strength < 0.5:
                if base_cost == min_cost:
                    return 0.5
                rel = (avg_cost - min_cost) / (base_cost - min_cost)
                return max(0.0, min(0.5, rel * 0.5))
            if strength > 0.5:
                if max_elo == base_elo:
                    return 0.5
                rel = (elo - base_elo) / (max_elo - base_elo)
                return max(0.5, min(1.0, 0.5 + rel * 0.5))
            return 0.5

        model_strengths_formatted = [
            (c["model"], f"{float(calc_strength(c)):.3f}") for c in candidate_models
        ]
        logger.info("Candidate models selected and ordered (with strength): %s", model_strengths_formatted)
        logger.info("Strength: %s, Temperature: %s, Time: %s", strength, temperature, time)
        if use_batch_mode:
            logger.info("Batch mode enabled.")
        if output_pydantic:
            logger.info("Pydantic output requested: %s", output_pydantic.__name__)
        if input_json is not None:
            logger.info("Input JSON:")
            logger.info(repr(input_json))
        else:
            logger.info("Input: Using pre-formatted 'messages'.")

    last_exception: Optional[Exception] = None
    newly_acquired_keys: Dict[str, bool] = {}
    response_format: Optional[Dict[str, Any]] = None
    time_kwargs: Dict[str, Any] = {}

    try:
        _set_model_rate_map(model_df)
    except Exception:
        pass

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
                    logger.info(
                        "[SKIP] Skipping %s due to API key/credentials issue after prompt.",
                        model_name_litellm,
                    )
                break

            litellm_kwargs: Dict[str, Any] = {
                "model": model_name_litellm,
                "messages": formatted_messages,
                "temperature": current_temperature,
                "num_retries": 2,
            }

            api_key_name_from_csv = model_info.get("api_key")
            is_vertex_model = (
                provider.lower() == "google"
                or provider.lower() == "googlevertexai"
                or provider.lower() == "vertex_ai"
                or model_name_litellm.startswith("vertex_ai/")
            )

            if is_vertex_model and api_key_name_from_csv == "VERTEX_CREDENTIALS":
                credentials_file_path = os.getenv("VERTEX_CREDENTIALS")
                vertex_project_env = os.getenv("VERTEX_PROJECT")
                model_location = model_info.get("location")
                if pd.notna(model_location) and str(model_location).strip():
                    vertex_location_env = str(model_location).strip()
                    if verbose:
                        logger.info(
                            "[INFO] Using per-model location override: '%s' for model '%s'",
                            vertex_location_env,
                            model_name_litellm,
                        )
                else:
                    vertex_location_env = os.getenv("VERTEX_LOCATION")

                if credentials_file_path and vertex_project_env and vertex_location_env:
                    try:
                        with open(credentials_file_path, "r") as handle:
                            loaded_credentials = json.load(handle)
                        vertex_credentials_json_string = json.dumps(loaded_credentials)
                        litellm_kwargs["vertex_credentials"] = vertex_credentials_json_string
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.info(
                                "[INFO] For Vertex AI: using vertex_credentials from '%s', project '%s', location '%s'.",
                                credentials_file_path,
                                vertex_project_env,
                                vertex_location_env,
                            )
                    except FileNotFoundError:
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.warning(
                                "[WARN] Vertex credentials file not found at '%s'. Using ADC with project '%s', location '%s'.",
                                credentials_file_path,
                                vertex_project_env,
                                vertex_location_env,
                            )
                    except json.JSONDecodeError:
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.error(
                                "[ERROR] Failed to decode JSON from Vertex credentials file: '%s'. Using ADC with project '%s', location '%s'.",
                                credentials_file_path,
                                vertex_project_env,
                                vertex_location_env,
                            )
                    except Exception as exc:
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.error(
                                "[ERROR] Failed to load Vertex credentials from '%s': %s. Using ADC with project '%s', location '%s'.",
                                credentials_file_path,
                                exc,
                                vertex_project_env,
                                vertex_location_env,
                            )
                else:
                    if verbose:
                        logger.warning(
                            "[WARN] For Vertex AI (using '%s'): One or more required environment variables (VERTEX_CREDENTIALS, VERTEX_PROJECT, VERTEX_LOCATION) are missing.",
                            api_key_name_from_csv,
                        )

            elif api_key_name_from_csv:
                key_value = os.getenv(api_key_name_from_csv)
                if key_value:
                    key_value = _sanitize_api_key(key_value)
                    litellm_kwargs["api_key"] = key_value
                    if verbose:
                        logger.info(
                            "[INFO] Explicitly passing API key from env var '%s' as 'api_key' parameter to LiteLLM.",
                            api_key_name_from_csv,
                        )
                    if is_vertex_model:
                        vertex_project_env = os.getenv("VERTEX_PROJECT")
                        model_location = model_info.get("location")
                        if pd.notna(model_location) and str(model_location).strip():
                            vertex_location_env = str(model_location).strip()
                            if verbose:
                                logger.info(
                                    "[INFO] Using per-model location override: '%s' for model '%s'",
                                    vertex_location_env,
                                    model_name_litellm,
                                )
                        else:
                            vertex_location_env = os.getenv("VERTEX_LOCATION")
                        if vertex_project_env and vertex_location_env:
                            litellm_kwargs["vertex_project"] = vertex_project_env
                            litellm_kwargs["vertex_location"] = vertex_location_env
                            if verbose:
                                logger.info(
                                    "[INFO] For Vertex AI model (using direct API key '%s'), also passing vertex_project='%s' and vertex_location='%s' from env vars.",
                                    api_key_name_from_csv,
                                    vertex_project_env,
                                    vertex_location_env,
                                )
                        elif verbose:
                            logger.warning(
                                "[WARN] For Vertex AI model (using direct API key '%s'), VERTEX_PROJECT or VERTEX_LOCATION env vars not set.",
                                api_key_name_from_csv,
                            )
                elif verbose:
                    logger.warning(
                        "[WARN] API key name '%s' found in CSV, but the environment variable '%s' is not set or empty.",
                        api_key_name_from_csv,
                        api_key_name_from_csv,
                    )
            elif verbose:
                logger.info(
                    "[INFO] No API key name specified in CSV for model '%s'. LiteLLM will use its default authentication mechanisms.",
                    model_name_litellm,
                )

            api_base = model_info.get("base_url")
            if pd.notna(api_base) and api_base:
                litellm_kwargs["base_url"] = str(api_base)
                litellm_kwargs["api_base"] = str(api_base)

            model_name_lower = str(model_name_litellm).lower()
            provider_lower_for_model = provider.lower()
            is_lm_studio = model_name_lower.startswith("lm_studio/") or provider_lower_for_model == "lm_studio"
            is_groq = model_name_lower.startswith("groq/") or provider_lower_for_model == "groq"

            if is_lm_studio:
                if not litellm_kwargs.get("base_url"):
                    lm_studio_base = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                    litellm_kwargs["base_url"] = lm_studio_base
                    litellm_kwargs["api_base"] = lm_studio_base
                    if verbose:
                        logger.info("[INFO] Using LM Studio base_url: %s", lm_studio_base)
                if not litellm_kwargs.get("api_key"):
                    lm_studio_key = os.getenv("LM_STUDIO_API_KEY") or "lm-studio"
                    litellm_kwargs["api_key"] = lm_studio_key
                    if verbose:
                        logger.info("[INFO] Using LM Studio api_key placeholder (set LM_STUDIO_API_KEY to customize).")

            if output_pydantic or output_schema:
                supports_structured = model_info.get("structured_output", False)
                if supports_structured:
                    if output_pydantic:
                        if verbose:
                            logger.info(
                                "[INFO] Requesting structured output (Pydantic: %s) for %s",
                                output_pydantic.__name__,
                                model_name_litellm,
                            )
                        schema = output_pydantic.model_json_schema()
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": output_pydantic.__name__, "schema": schema, "strict": True},
                        }
                    else:
                        if verbose:
                            logger.info(
                                "[INFO] Requesting structured output (JSON Schema) for %s",
                                model_name_litellm,
                            )
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": "response", "schema": output_schema, "strict": False},
                        }
                        _ensure_all_properties_required(response_format["json_schema"]["schema"])
                        _add_additional_properties_false(response_format["json_schema"]["schema"])

                    litellm_kwargs["response_format"] = response_format

                    if is_lm_studio and response_format and response_format.get("type") == "json_object":
                        schema = response_format.get("response_schema", {})
                        lm_studio_response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": "response", "strict": True, "schema": schema},
                        }
                        litellm_kwargs["extra_body"] = {"response_format": lm_studio_response_format}
                        if "response_format" in litellm_kwargs:
                            del litellm_kwargs["response_format"]
                        if verbose:
                            logger.info(
                                "[INFO] Using extra_body for LM Studio response_format to bypass drop_params"
                            )

                    if is_groq and response_format:
                        schema = output_pydantic.model_json_schema() if output_pydantic else output_schema
                        litellm_kwargs["response_format"] = {"type": "json_object"}
                        schema_instruction = (
                            f"You must respond with valid JSON matching this schema:\n```json\n"
                            f"{json.dumps(schema, indent=2)}\n```\n"
                            "Respond ONLY with the JSON object, no other text."
                        )
                        messages_list = litellm_kwargs.get("messages", [])
                        if messages_list and messages_list[0].get("role") == "system":
                            messages_list[0]["content"] = (
                                schema_instruction + "\n\n" + messages_list[0]["content"]
                            )
                        else:
                            messages_list.insert(0, {"role": "system", "content": schema_instruction})
                        litellm_kwargs["messages"] = messages_list
                        if verbose:
                            logger.info(
                                "[INFO] Using JSON object mode with schema in prompt for Groq (avoiding tool_use issues)"
                            )
                else:
                    schema_name = output_pydantic.__name__ if output_pydantic else "JSON Schema"
                    if verbose:
                        logger.warning(
                            "[WARN] Model %s does not support structured output via CSV flag. Output might not be valid %s.",
                            model_name_litellm,
                            schema_name,
                        )

            reasoning_type = model_info.get("reasoning_type", "none")
            max_reasoning_tokens_val = model_info.get("max_reasoning_tokens", 0)

            if time > 0:
                if reasoning_type == "budget":
                    if max_reasoning_tokens_val > 0:
                        budget = int(time * max_reasoning_tokens_val)
                        if budget > 0:
                            if provider == "anthropic":
                                thinking_param = {"type": "enabled", "budget_tokens": budget}
                                litellm_kwargs["thinking"] = thinking_param
                                time_kwargs["thinking"] = thinking_param
                                if verbose:
                                    logger.info(
                                        "[INFO] Requesting Anthropic thinking (budget type) with budget: %s tokens for %s",
                                        budget,
                                        model_name_litellm,
                                    )
                            else:
                                if verbose:
                                    logger.warning(
                                        "[WARN] Reasoning type is 'budget' for %s, but no specific LiteLLM budget parameter known for this provider.",
                                        model_name_litellm,
                                    )
                        elif verbose:
                            logger.info(
                                "[INFO] Calculated reasoning budget is 0 for %s, skipping reasoning parameter.",
                                model_name_litellm,
                            )
                    elif verbose:
                        logger.warning(
                            "[WARN] Reasoning type is 'budget' for %s, but 'max_reasoning_tokens' is missing or zero in CSV.",
                            model_name_litellm,
                        )

                elif reasoning_type == "effort":
                    effort = "low"
                    if time > 0.7:
                        effort = "high"
                    elif time > 0.3:
                        effort = "medium"

                    model_lower = str(model_name_litellm).lower()
                    provider_lower = str(provider).lower()

                    if provider_lower == "openai" and model_lower.startswith("gpt-5"):
                        reasoning_obj = {"effort": effort, "summary": "auto"}
                        litellm_kwargs["reasoning"] = reasoning_obj
                        time_kwargs["reasoning"] = reasoning_obj
                        if verbose:
                            logger.info(
                                "[INFO] Requesting OpenAI reasoning.effort='%s' for %s (Responses API)",
                                effort,
                                model_name_litellm,
                            )
                    elif provider_lower == "openai" and model_lower.startswith("o") and "mini" not in model_lower:
                        litellm_kwargs["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort
                        if verbose:
                            logger.info(
                                "[INFO] Requesting reasoning_effort='%s' for %s", effort, model_name_litellm
                            )
                    else:
                        litellm_kwargs["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort
                        if verbose:
                            logger.info(
                                "[INFO] Requesting generic reasoning_effort='%s' for %s", effort, model_name_litellm
                            )
                elif reasoning_type == "none":
                    if verbose:
                        logger.info(
                            "[INFO] Model %s has reasoning_type='none'. No reasoning parameter sent.",
                            model_name_litellm,
                        )
                else:
                    if verbose:
                        logger.warning(
                            "[WARN] Unknown reasoning_type '%s' for model %s in CSV.",
                            reasoning_type,
                            model_name_litellm,
                        )

            try:
                start_time = time_module.time()

                if litellm.cache is not None:
                    litellm_kwargs["caching"] = True
                    if litellm_kwargs.get("metadata") is None:
                        litellm_kwargs["metadata"] = {}
                # OpenAI gpt-5 responses path
                model_lower_for_call = str(model_name_litellm).lower()
                provider_lower_for_call = str(provider).lower()
                if (
                    not use_batch_mode
                    and provider_lower_for_call == "openai"
                    and model_lower_for_call.startswith("gpt-5")
                ):
                    try:
                        if isinstance(formatted_messages, list) and formatted_messages and isinstance(
                            formatted_messages[0], dict
                        ):
                            input_text = "\n\n".join(
                                f"{m.get('role','user')}: {m.get('content','')}" for m in formatted_messages
                            )
                        else:
                            input_text = str(formatted_messages)

                        reasoning_param = time_kwargs.get("reasoning")
                        text_block = {"format": {"type": "text"}}

                        if output_pydantic or output_schema:
                            try:
                                if output_pydantic:
                                    schema = output_pydantic.model_json_schema()
                                    name = output_pydantic.__name__
                                else:
                                    schema = output_schema
                                    name = "response"
                                _ensure_all_properties_required(schema)
                                _add_additional_properties_false(schema)
                                text_block = {
                                    "format": {
                                        "type": "json_schema",
                                        "name": name,
                                        "strict": True,
                                        "schema": schema,
                                    }
                                }
                                if verbose:
                                    logger.info(
                                        "[INFO] Using structured output via text.format for Responses API"
                                    )
                            except Exception as schema_exc:
                                logger.warning(
                                    "[WARN] Failed to derive JSON schema: %s. Proceeding with plain text format.",
                                    schema_exc,
                                )

                        responses_kwargs = {"model": model_name_litellm, "input": input_text, "text": text_block}
                        if reasoning_param is not None:
                            responses_kwargs["reasoning"] = reasoning_param

                        resp = litellm.responses(**responses_kwargs)

                        result_text = None
                        try:
                            for item in resp.output:
                                if getattr(item, "type", None) == "message" and hasattr(item, "content") and item.content:
                                    for content_item in item.content:
                                        if hasattr(content_item, "text"):
                                            result_text = content_item.text
                                            break
                                    if result_text:
                                        break
                        except Exception:
                            result_text = None

                        total_cost = 0.0
                        usage = getattr(resp, "usage", None)
                        if usage is not None:
                            in_tok = getattr(usage, "input_tokens", 0) or 0
                            out_tok = getattr(usage, "output_tokens", 0) or 0
                            in_rate = model_info.get("input", 0.0) or 0.0
                            out_rate = model_info.get("output", 0.0) or 0.0
                            total_cost = (in_tok * in_rate + out_tok * out_rate) / 1_000_000.0

                        final_result: Any
                        if output_pydantic and result_text:
                            try:
                                final_result = output_pydantic.model_validate_json(result_text)
                            except Exception as exc:
                                logger.warning(
                                    "[WARN] Pydantic parse failed on Responses output: %s. Attempting JSON repair...",
                                    exc,
                                )
                                fenced = _extract_fenced_json_block(result_text)
                                candidates: List[str] = []
                                if fenced:
                                    candidates.append(fenced)
                                else:
                                    candidates.extend(_extract_balanced_json_objects(result_text))
                                cleaned = result_text.strip()
                                if cleaned.startswith("```json"):
                                    cleaned = cleaned[7:]
                                elif cleaned.startswith("```"):
                                    cleaned = cleaned[3:]
                                if cleaned.endswith("```"):
                                    cleaned = cleaned[:-3]
                                cleaned = cleaned.strip()
                                if cleaned and cleaned not in candidates:
                                    candidates.append(cleaned)

                                parse_succeeded = False
                                for cand in candidates:
                                    try:
                                        final_result = output_pydantic.model_validate_json(cand)
                                        parse_succeeded = True
                                        logger.info("[SUCCESS] JSON repair succeeded for Responses output")
                                        break
                                    except Exception:
                                        continue
                                if not parse_succeeded:
                                    logger.error(
                                        "[ERROR] All JSON repair attempts failed for Responses output. Original error: %s",
                                        exc,
                                    )
                                    final_result = (
                                        "ERROR: Failed to parse structured output from Responses API. Raw: "
                                        f"{repr(result_text)[:200]}"
                                    )
                        else:
                            final_result = result_text

                        if verbose:
                            logger.info("[RESULT] Model Used: %s", model_name_litellm)
                            logger.info("[RESULT] Total Cost (estimated): $%.6g", total_cost)

                        return {
                            "result": final_result,
                            "cost": total_cost,
                            "model_name": model_name_litellm,
                            "thinking_output": None,
                        }
                    except Exception as exc:
                        last_exception = exc
                        logger.error(
                            "[ERROR] OpenAI Responses call failed for %s: %s", model_name_litellm, exc
                        )
                        if "reasoning" in litellm_kwargs:
                            litellm_kwargs.pop("reasoning", None)

                if use_batch_mode:
                    if verbose:
                        logger.info("[INFO] Calling litellm.batch_completion for %s...", model_name_litellm)
                    response = litellm.batch_completion(**litellm_kwargs)
                else:
                    if provider.lower() == "anthropic" and "thinking" in litellm_kwargs:
                        if litellm_kwargs.get("temperature") != 1:
                            if verbose:
                                logger.info(
                                    "[INFO] Anthropic thinking enabled: forcing temperature=1 for compliance."
                                )
                            litellm_kwargs["temperature"] = 1
                            current_temperature = 1
                    if verbose:
                        logger.info("[INFO] Calling litellm.completion for %s...", model_name_litellm)
                    response = litellm.completion(**litellm_kwargs, timeout=LLM_CALL_TIMEOUT)

                end_time = time_module.time()
                if verbose:
                    logger.info(
                        "[SUCCESS] Invocation successful for %s (took %.2fs)",
                        model_name_litellm,
                        end_time - start_time,
                    )

                retry_provider_kwargs = {
                    k: v
                    for k, v in litellm_kwargs.items()
                    if k in ("vertex_credentials", "vertex_project", "vertex_location", "api_key", "base_url", "api_base")
                }

                results: List[Any] = []
                thinking_outputs: List[Any] = []

                response_list = response if use_batch_mode else [response]

                for i, resp_item in enumerate(response_list):
                    thinking = None
                    try:
                        if (
                            hasattr(resp_item, "_hidden_params")
                            and resp_item._hidden_params
                            and "thinking" in resp_item._hidden_params
                        ):
                            thinking = resp_item._hidden_params["thinking"]
                        elif (
                            hasattr(resp_item, "choices")
                            and resp_item.choices
                            and hasattr(resp_item.choices[0], "message")
                            and hasattr(resp_item.choices[0].message, "get")
                            and resp_item.choices[0].message.get("reasoning_content")
                        ):
                            thinking = resp_item.choices[0].message.get("reasoning_content")
                    except (AttributeError, IndexError, KeyError, TypeError):
                        pass
                    thinking_outputs.append(thinking)

                    try:
                        raw_result = resp_item.choices[0].message.content
                        if raw_result is None:
                            logger.warning(
                                "[WARNING] LLM returned None content for item %s, retrying with cache bypass...",
                                i,
                            )
                            if not use_batch_mode and prompt and input_json is not None:
                                modified_prompt = prompt + " "
                                retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                litellm.cache = None
                                retry_response = litellm.completion(
                                    model=model_name_litellm,
                                    messages=retry_messages,
                                    temperature=current_temperature,
                                    response_format=response_format,
                                    timeout=LLM_CALL_TIMEOUT,
                                    **time_kwargs,
                                    **retry_provider_kwargs,
                                )
                                litellm.cache = configured_cache
                                retry_raw_result = retry_response.choices[0].message.content
                                if retry_raw_result is not None:
                                    raw_result = retry_raw_result
                                else:
                                    results.append("ERROR: LLM returned None content even after cache bypass")
                                    continue
                            else:
                                results.append("ERROR: LLM returned None content and cannot retry")
                                continue

                        if isinstance(raw_result, str) and _is_malformed_json_response(raw_result):
                            logger.warning(
                                "[WARNING] Detected malformed JSON response with excessive trailing newlines for item %s. Retrying with cache bypass...",
                                i,
                            )
                            if not use_batch_mode and prompt and input_json is not None:
                                modified_prompt = prompt + " "
                                retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                original_cache = litellm.cache
                                litellm.cache = None
                                retry_response = litellm.completion(
                                    model=model_name_litellm,
                                    messages=retry_messages,
                                    temperature=current_temperature,
                                    response_format=response_format,
                                    timeout=LLM_CALL_TIMEOUT,
                                    **time_kwargs,
                                    **retry_provider_kwargs,
                                )
                                litellm.cache = original_cache
                                retry_raw_result = retry_response.choices[0].message.content
                                if retry_raw_result is not None and not _is_malformed_json_response(retry_raw_result):
                                    raw_result = retry_raw_result

                        if output_pydantic or output_schema:
                            parsed_result = None
                            json_string_to_parse: Optional[str] = None

                            try:
                                if output_pydantic and isinstance(raw_result, output_pydantic):
                                    parsed_result = raw_result
                                elif isinstance(raw_result, dict):
                                    if output_pydantic:
                                        parsed_result = output_pydantic.model_validate(raw_result)
                                    else:
                                        import jsonschema

                                        jsonschema.validate(instance=raw_result, schema=output_schema)
                                        parsed_result = json.dumps(raw_result)
                                elif isinstance(raw_result, str):
                                    json_string_to_parse = raw_result
                                    fenced = _extract_fenced_json_block(raw_result)
                                    candidates: List[str] = []
                                    if fenced:
                                        candidates.append(fenced)
                                    else:
                                        candidates.extend(_extract_balanced_json_objects(raw_result))
                                    if not candidates:
                                        raise ValueError("No JSON-like content found")

                                    parse_err: Optional[Exception] = None
                                    for cand in candidates:
                                        try:
                                            if output_pydantic:
                                                parsed_result = output_pydantic.model_validate_json(cand)
                                            else:
                                                loaded = json.loads(cand)
                                                try:
                                                    import jsonschema

                                                    jsonschema.validate(instance=loaded, schema=output_schema)
                                                except ImportError:
                                                    pass
                                                parsed_result = cand
                                            json_string_to_parse = cand
                                            parse_err = None
                                            break
                                        except Exception as exc:
                                            parse_err = exc

                                    if parsed_result is None:
                                        if parse_err is not None:
                                            raise parse_err
                                        raise ValueError("Unable to parse any JSON candidates")
                            except Exception as parse_error:
                                target_name = output_pydantic.__name__ if output_pydantic else "JSON Schema"
                                logger.error(
                                    "[ERROR] Failed to parse response into %s for item %s: %s",
                                    target_name,
                                    i,
                                    parse_error,
                                )
                                error_content = json_string_to_parse if json_string_to_parse is not None else raw_result
                                logger.error("[ERROR] Content attempted for parsing: %s", repr(error_content))
                                raise SchemaValidationError(
                                    f"Failed to parse response into {target_name}: {parse_error}",
                                    raw_response=raw_result,
                                    item_index=i,
                                ) from parse_error

                            _unescape_code_newlines(parsed_result)

                            if language in (None, "python") and _has_invalid_python_code(parsed_result):
                                logger.warning(
                                    "[WARNING] Detected invalid Python syntax in code fields for item %s after repair. Retrying with cache bypass...",
                                    i,
                                )
                                if not use_batch_mode and prompt and input_json is not None:
                                    modified_prompt = prompt + "  "
                                    retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                    original_cache = litellm.cache
                                    litellm.cache = None
                                    retry_response = litellm.completion(
                                        model=model_name_litellm,
                                        messages=retry_messages,
                                        temperature=current_temperature,
                                        response_format=response_format,
                                        timeout=LLM_CALL_TIMEOUT,
                                        **time_kwargs,
                                        **retry_provider_kwargs,
                                    )
                                    litellm.cache = original_cache
                                    retry_raw_result = retry_response.choices[0].message.content
                                    retry_parsed = None
                                    if output_pydantic:
                                        if isinstance(retry_raw_result, output_pydantic):
                                            retry_parsed = retry_raw_result
                                        elif isinstance(retry_raw_result, dict):
                                            retry_parsed = output_pydantic.model_validate(retry_raw_result)
                                        elif isinstance(retry_raw_result, str):
                                            retry_parsed = output_pydantic.model_validate_json(retry_raw_result)
                                    elif output_schema and isinstance(retry_raw_result, str):
                                        retry_parsed = retry_raw_result
                                    if retry_parsed is not None:
                                        _unescape_code_newlines(retry_parsed)
                                        if not _has_invalid_python_code(retry_parsed):
                                            parsed_result = retry_parsed

                            results.append(parsed_result)
                        else:
                            results.append(raw_result)
                    except (AttributeError, IndexError) as exc:
                        logger.error(
                            "[ERROR] Could not extract result content from response item %s: %s", i, exc
                        )
                        results.append(f"ERROR: Could not extract result content. Response: {resp_item}")

                total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                final_result = results if use_batch_mode else results[0]
                final_thinking = thinking_outputs if use_batch_mode else thinking_outputs[0]

                if verbose:
                    input_tokens = _LAST_CALLBACK_DATA.get("input_tokens", 0)
                    output_tokens = _LAST_CALLBACK_DATA.get("output_tokens", 0)
                    cost_input_pm = model_info.get("input", 0.0) if pd.notna(model_info.get("input")) else 0.0
                    cost_output_pm = model_info.get("output", 0.0) if pd.notna(model_info.get("output")) else 0.0
                    logger.info("[RESULT] Model Used: %s", model_name_litellm)
                    logger.info("[RESULT] Cost (Input): $%.2f/M tokens", cost_input_pm)
                    logger.info("[RESULT] Cost (Output): $%.2f/M tokens", cost_output_pm)
                    logger.info("[RESULT] Tokens (Prompt): %s", input_tokens)
                    logger.info("[RESULT] Tokens (Completion): %s", output_tokens)
                    logger.info("[RESULT] Total Cost (from callback): $%.6g", total_cost)
                    logger.info("[RESULT] Max Completion Tokens: Provider Default")
                    if final_thinking:
                        logger.info("[RESULT] Thinking Output:")
                        logger.info(final_thinking)

                return {
                    "result": final_result,
                    "cost": total_cost,
                    "model_name": model_name_litellm,
                    "thinking_output": final_thinking if final_thinking else None,
                }

            except openai.AuthenticationError as exc:
                last_exception = exc
                error_message = str(exc)
                if _is_wsl_environment() and ("Illegal header value" in error_message or "\r" in error_message):
                    logger.warning(
                        "[WSL AUTH ERROR] Authentication failed for %s - detected WSL line ending issue",
                        model_name_litellm,
                    )
                    logger.warning(
                        "[WSL AUTH ERROR] This is likely caused by API key environment variables containing carriage returns"
                    )
                    logger.warning(
                        "[WSL AUTH ERROR] Try setting your API key again or check your .env file for line ending issues"
                    )
                    env_info = _get_environment_info()
                    logger.debug("Environment info: %s", env_info)

                if newly_acquired_keys.get(api_key_name):
                    logger.warning(
                        "[AUTH ERROR] Authentication failed for %s with the newly provided key for '%s'. Please check the key and try again.",
                        model_name_litellm,
                        api_key_name,
                    )
                    if api_key_name in os.environ:
                        del os.environ[api_key_name]
                    newly_acquired_keys[api_key_name] = False
                    retry_with_same_model = True
                else:
                    logger.warning(
                        "[AUTH ERROR] Authentication failed for %s using existing key '%s'. Trying next model.",
                        model_name_litellm,
                        api_key_name,
                    )
                    break

            except SchemaValidationError as exc:
                last_exception = exc
                logger.warning(
                    "[SCHEMA ERROR] Validation failed for %s: %s. Trying next model.",
                    model_name_litellm,
                    exc,
                )
                if verbose:
                    logger.debug("Raw response that failed validation: %s", repr(exc.raw_response))
                break

            except (
                openai.RateLimitError,
                openai.APITimeoutError,
                openai.APIConnectionError,
                openai.APIStatusError,
                openai.BadRequestError,
                openai.InternalServerError,
                Exception,
            ) as exc:
                last_exception = exc
                error_type = type(exc).__name__
                error_str = str(exc)
                lower_err = error_str.lower()
                if (not temp_adjustment_done) and ("temperature" in lower_err) and ("thinking" in lower_err):
                    anthropic_thinking_sent = ("thinking" in litellm_kwargs) and (provider.lower() == "anthropic")
                    if anthropic_thinking_sent:
                        adjusted_temp = 1
                        logger.warning(
                            "[WARN] %s: Anthropic with thinking requires temperature=1. Retrying with temperature=%s.",
                            model_name_litellm,
                            adjusted_temp,
                        )
                    else:
                        adjusted_temp = 0.99
                        logger.warning(
                            "[WARN] %s: Provider rejected temperature=1 without thinking. Retrying with temperature=%s.",
                            model_name_litellm,
                            adjusted_temp,
                        )
                    current_temperature = adjusted_temp
                    temp_adjustment_done = True
                    retry_with_same_model = True
                    continue

                logger.error(
                    "[ERROR] Invocation failed for %s (%s): %s. Trying next model.",
                    model_name_litellm,
                    error_type,
                    exc,
                )
                if verbose:
                    logger.debug("Detailed exception traceback for %s:", model_name_litellm, exc_info=True)
                break

        continue

    error_message = "All candidate models failed."
    if last_exception:
        error_message += f" Last error ({type(last_exception).__name__}): {last_exception}"
    logger.error("[FATAL] %s", error_message)
    raise RuntimeError(error_message) from last_exception