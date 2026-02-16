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

# -----------------------------------------------------------------------------
# Logging Configuration
# -----------------------------------------------------------------------------
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

# Suppress LiteLLM debug messages
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# drop_params default
try:
    _drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_params_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

if not logger.handlers:
    console_handler = logging.StreamHandler()
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(console_handler)


def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    """Configure rotating file handler for logging."""
    if not log_file_path:
        return
    try:
        from logging.handlers import RotatingFileHandler

        file_handler = RotatingFileHandler(
            log_file_path, maxBytes=10 * 1024 * 1024, backupCount=5
        )
        file_handler.setFormatter(
            logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
        )
        logger.addHandler(file_handler)
        litellm_logger.addHandler(file_handler)
        logger.info(f"File logging configured to: {log_file_path}")
    except Exception as e:
        logger.warning(f"Failed to set up file logging: {e}")


def set_verbose_logging(verbose: bool = False) -> None:
    """Enable/disable verbose logging."""
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

    if want_verbose:
        logger.debug("Verbose logging enabled (including LiteLLM debug output)")


# -----------------------------------------------------------------------------
# Exceptions
# -----------------------------------------------------------------------------
class SchemaValidationError(Exception):
    """Raised when LLM response fails Pydantic/JSON schema validation."""

    def __init__(
        self, message: str, raw_response: Any = None, item_index: int = 0
    ) -> None:
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index


class CloudFallbackError(Exception):
    """Cloud failed and should fall back to local."""


class CloudInvocationError(Exception):
    """Cloud failed with non-recoverable error."""


class InsufficientCreditsError(Exception):
    """Cloud failed due to insufficient credits."""


# -----------------------------------------------------------------------------
# Project Root + CSV Path Resolution
# -----------------------------------------------------------------------------
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env

try:
    _installed_pkg_root = importlib.resources.files("pdd")
    _installed_pkg_root_path = Path(str(_installed_pkg_root))
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


def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    """Search upwards from CWD for markers."""
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
user_model_csv_path = Path.home() / ".pdd" / "llm_model.csv"

if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
else:
    ENV_PATH = PROJECT_ROOT / ".env"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH = user_model_csv_path
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
else:
    LLM_MODEL_CSV_PATH = None

if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", None)

# -----------------------------------------------------------------------------
# LiteLLM Cache Configuration
# -----------------------------------------------------------------------------
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

if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    litellm.cache = None
    cache_configured = True

if not cache_configured and GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
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
        cache_configured = True
    except Exception as e:
        warnings.warn(f"Failed to configure LiteLLM S3/GCS cache: {e}")
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

if not cache_configured:
    try:
        sqlite_cache_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_cache_path))
        litellm.cache = configured_cache
        cache_configured = True
    except Exception as e:
        warnings.warn(f"Failed to configure LiteLLM disk cache: {e}")
        litellm.cache = None

# -----------------------------------------------------------------------------
# Callback
# -----------------------------------------------------------------------------
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
    except Exception:
        try:
            model_name = kwargs.get("model")
            in_tok = getattr(usage, "prompt_tokens", 0)
            out_tok = getattr(usage, "completion_tokens", 0)
            rates = _MODEL_RATE_MAP.get(str(model_name))
            if rates is not None:
                in_rate, out_rate = rates
                calculated_cost = (
                    float(in_tok) * in_rate + float(out_tok) * out_rate
                ) / 1_000_000.0
        except Exception:
            calculated_cost = 0.0

    _LAST_CALLBACK_DATA["input_tokens"] = input_tokens
    _LAST_CALLBACK_DATA["output_tokens"] = output_tokens
    _LAST_CALLBACK_DATA["finish_reason"] = finish_reason
    _LAST_CALLBACK_DATA["cost"] = calculated_cost


litellm.success_callback = [_litellm_success_callback]

# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------
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


def _validate_with_pydantic(
    result: Any, pydantic_class: Type[BaseModel]
) -> BaseModel:
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    if isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    if isinstance(result, pydantic_class):
        return result
    raise ValueError(f"Cannot validate result type {type(result)} with Pydantic model")


def _is_wsl_environment() -> bool:
    try:
        if os.path.exists("/proc/version"):
            with open("/proc/version", "r") as f:
                if "microsoft" in f.read().lower():
                    return True
        if os.getenv("WSL_DISTRO_NAME"):
            return True
        if "/mnt/c/" in os.getenv("PATH", "").lower():
            return True
    except Exception:
        return False
    return False


def _get_environment_info() -> Dict[str, str]:
    import platform

    info = {
        "platform": platform.system(),
        "platform_release": platform.release(),
        "platform_version": platform.version(),
        "architecture": platform.machine(),
        "python_version": platform.python_version(),
        "is_wsl": str(_is_wsl_environment()),
    }
    if _is_wsl_environment():
        info["wsl_distro"] = os.getenv("WSL_DISTRO_NAME", "unknown")
    return info


def _is_malformed_json_response(content: str, threshold: int = 100) -> bool:
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


def _sanitize_api_key(key_value: Optional[str]) -> Optional[str]:
    if key_value is None:
        return None
    sanitized = key_value.strip()
    if any(ord(c) < 32 for c in sanitized):
        sanitized = "".join(c for c in sanitized if ord(c) >= 32)
    if "\r" in key_value and _is_wsl_environment():
        logger.info("Detected WSL CRLF issue in API key; sanitized.")
    return sanitized


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    lines: List[str] = []
    if env_path.exists():
        with open(env_path, "r") as f:
            lines = f.readlines()

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

    with open(env_path, "w") as f:
        f.writelines(new_lines)


def _ensure_api_key(
    model_info: Dict[str, Any],
    newly_acquired_keys: Dict[str, bool],
    verbose: bool,
) -> bool:
    key_name = model_info.get("api_key")
    if not key_name or key_name == "EXISTING_KEY":
        return True

    key_value = os.getenv(key_name)
    if key_value:
        key_value = _sanitize_api_key(key_value)

    if key_value:
        newly_acquired_keys[key_name] = False
        return True

    logger.warning(
        f"API key environment variable '{key_name}' for model '{model_info.get('model')}' is not set."
    )
    if os.environ.get("PDD_FORCE"):
        return False

    try:
        user_key = input(f"Please enter the API key for {key_name}: ").strip()
        if not user_key:
            return False
        user_key = _sanitize_api_key(user_key) or ""
        os.environ[key_name] = user_key
        newly_acquired_keys[key_name] = True
        try:
            _save_key_to_env_file(key_name, user_key, ENV_PATH)
            logger.warning(
                "SECURITY WARNING: API key saved to .env. Ensure .env is in .gitignore."
            )
        except Exception as e:
            logger.error(f"Failed to update .env: {e}")
        return True
    except EOFError:
        return False


def _format_messages(
    prompt: str,
    input_data: Union[Dict[str, Any], List[Dict[str, Any]]],
    use_batch_mode: bool,
) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    try:
        if use_batch_mode:
            if not isinstance(input_data, list):
                raise ValueError("input_json must be a list for batch mode.")
            result: List[List[Dict[str, str]]] = []
            for item in input_data:
                if not isinstance(item, dict):
                    raise ValueError("Each item in input_json must be a dict.")
                formatted = prompt.format(**item)
                result.append([{"role": "user", "content": formatted}])
            return result
        if not isinstance(input_data, dict):
            raise ValueError("input_json must be a dict when not in batch mode.")
        formatted = prompt.format(**input_data)
        return [{"role": "user", "content": formatted}]
    except KeyError as e:
        raise ValueError(f"Prompt formatting error: Missing key {e!s}") from e
    except Exception as e:
        raise ValueError(f"Error formatting prompt: {e}") from e


def _extract_fenced_json_block(text: str) -> Optional[str]:
    m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, flags=re.IGNORECASE)
    if m:
        return m.group(1)
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
        else:
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
    indicators = ("def ", "class ", "import ", "from ", "if __name__", "return ", "print(")
    return any(ind in s for ind in indicators)


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

    if not code.strip():
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
                return candidate
            except SyntaxError:
                pass
    return code


def _smart_unescape_code(code: str) -> str:
    if "\\n" not in code:
        return code
    if "\n" in code:
        return code
    return code.replace("\\r\\n", "\r\n").replace("\\n", "\n").replace("\\t", "\t")


def _unescape_code_newlines(obj: Any) -> Any:
    if obj is None:
        return obj

    def _process_string(s: str) -> str:
        if _looks_like_python_code(s):
            return _repair_python_syntax(_smart_unescape_code(s))
        return s.replace("\\r\\n", "\r\n").replace("\\n", "\n").replace("\\t", "\t")

    if isinstance(obj, BaseModel):
        for field_name in obj.model_fields:
            val = getattr(obj, field_name)
            if isinstance(val, str):
                object.__setattr__(obj, field_name, _process_string(val))
            elif isinstance(val, (dict, list, BaseModel)):
                _unescape_code_newlines(val)
        return obj
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str):
                obj[k] = _process_string(v)
            elif isinstance(v, (dict, list, BaseModel)):
                _unescape_code_newlines(v)
        return obj
    if isinstance(obj, list):
        for i, item in enumerate(obj):
            if isinstance(item, str):
                obj[i] = _process_string(item)
            elif isinstance(item, (dict, list, BaseModel)):
                _unescape_code_newlines(v)
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
            if _has_invalid_python_code(getattr(obj, name), field_name=name):
                return True
    if isinstance(obj, dict):
        for key, value in obj.items():
            if _has_invalid_python_code(value, field_name=str(key)):
                return True
    if isinstance(obj, list):
        for item in obj:
            if _has_invalid_python_code(item, field_name=field_name):
                return True
    return False


# -----------------------------------------------------------------------------
# Model Loading + Selection
# -----------------------------------------------------------------------------
def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    if csv_path is not None and csv_path.exists():
        df = pd.read_csv(csv_path)
    else:
        try:
            csv_data = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
            df = pd.read_csv(pd.io.common.StringIO(csv_data))
        except Exception as e:
            raise FileNotFoundError(f"Failed to load default LLM model CSV: {e}")

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
            raise RuntimeError(f"Missing required column {col} in CSV")

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
    df["max_reasoning_tokens"] = df.get("max_reasoning_tokens", 0).fillna(0).astype(int)
    df["avg_cost"] = (df["input"] + df["output"]) / 2
    df["structured_output"] = df["structured_output"].fillna(False).astype(bool)
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
    df["api_key"] = df["api_key"].fillna("").astype(str)
    return df


def _select_model_candidates(
    strength: float, base_model_name: Optional[str], model_df: pd.DataFrame
) -> List[Dict[str, Any]]:
    if model_df.empty:
        raise ValueError("Loaded model data is empty.")

    available_df = model_df[model_df["api_key"].notna()].copy()
    if available_df.empty:
        raise ValueError("No models available after filtering.")

    base_model_row = (
        available_df[available_df["model"] == base_model_name]
        if base_model_name
        else pd.DataFrame()
    )

    if base_model_row.empty:
        base_model = available_df.iloc[0]
    else:
        base_model = base_model_row.iloc[0]

    if strength == 0.5:
        available_df["sort_metric"] = -available_df["coding_arena_elo"]
        candidates = available_df.sort_values(by="sort_metric").to_dict("records")
        if any(c["model"] == base_model["model"] for c in candidates):
            candidates.sort(key=lambda x: 0 if x["model"] == base_model["model"] else 1)
        return candidates

    if strength < 0.5:
        base_cost = base_model["avg_cost"]
        cheapest_model = available_df.loc[available_df["avg_cost"].idxmin()]
        cheapest_cost = cheapest_model["avg_cost"]
        target_cost = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost)
        available_df["sort_metric"] = abs(available_df["avg_cost"] - target_cost)
        return available_df.sort_values(by="sort_metric").to_dict("records")

    base_elo = base_model["coding_arena_elo"]
    highest_elo_model = available_df.loc[available_df["coding_arena_elo"].idxmax()]
    highest_elo = highest_elo_model["coding_arena_elo"]
    target_elo = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo)
    available_df["sort_metric"] = abs(available_df["coding_arena_elo"] - target_elo)
    return available_df.sort_values(by="sort_metric").to_dict("records")


# -----------------------------------------------------------------------------
# Cloud Execution
# -----------------------------------------------------------------------------
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

    try:
        response = requests.post(cloud_url, json=payload, headers=headers, timeout=300)
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
        if response.status_code == 402:
            raise InsufficientCreditsError(response.json().get("error", "Insufficient credits"))
        if response.status_code in (401, 403):
            try:
                from .auth_service import clear_jwt_cache

                clear_jwt_cache()
            except Exception:
                pass
            server_error = response.json().get("error", "")
            raise CloudFallbackError(
                f"Authentication expired ({server_error or response.status_code}). "
                "Please re-authenticate with: pdd auth logout && pdd auth login"
            )
        if response.status_code >= 500:
            raise CloudFallbackError(response.json().get("error", "Server error"))
        raise CloudInvocationError(
            f"Cloud llm_invoke failed: {response.json().get('error', response.status_code)}"
        )
    except requests.exceptions.Timeout:
        raise CloudFallbackError("Cloud request timed out")
    except requests.exceptions.ConnectionError as e:
        raise CloudFallbackError(f"Cloud connection failed: {e}")
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")


# -----------------------------------------------------------------------------
# Main Function
# -----------------------------------------------------------------------------
LLM_CALL_TIMEOUT = 120


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

    if use_cloud is None:
        force_local = os.environ.get("PDD_FORCE_LOCAL", "").lower() in ("1", "true", "yes")
        if force_local:
            use_cloud = False
        else:
            try:
                from .core.cloud import CloudConfig

                use_cloud = CloudConfig.is_cloud_enabled()
            except Exception:
                use_cloud = False

    if use_cloud:
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
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud execution failed ({e}), falling back to local...[/yellow]")
            logger.warning(f"Cloud fallback: {e}")
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as e:
            console.print(f"[yellow]Cloud error ({e}), falling back to local...[/yellow]")
            logger.warning(f"Cloud invocation error: {e}")

    if messages:
        if use_batch_mode and not all(isinstance(m, list) for m in messages):
            raise ValueError("'messages' must be list of lists when use_batch_mode=True.")
        if not use_batch_mode and not all(isinstance(m, dict) for m in messages):
            raise ValueError("'messages' must be list of dicts when use_batch_mode=False.")
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

    model_df = _load_model_data(LLM_MODEL_CSV_PATH)
    _set_model_rate_map(model_df)
    candidates = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)

    last_exception: Optional[Exception] = None
    newly_acquired_keys: Dict[str, bool] = {}

    for model_info in candidates:
        model_name = model_info["model"]
        provider = str(model_info.get("provider", "")).lower()

        if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
            continue

        litellm_kwargs: Dict[str, Any] = {
            "model": model_name,
            "messages": formatted_messages,
            "temperature": temperature,
            "num_retries": 2,
        }

        api_key_name = model_info.get("api_key")
        is_vertex = provider in {"google", "googlevertexai", "vertex_ai"} or str(model_name).startswith("vertex_ai/")
        if is_vertex and api_key_name == "VERTEX_CREDENTIALS":
            credentials_file_path = os.getenv("VERTEX_CREDENTIALS")
            vertex_project = os.getenv("VERTEX_PROJECT")
            model_location = model_info.get("location")
            vertex_location = (
                str(model_location).strip()
                if model_location and str(model_location).strip()
                else os.getenv("VERTEX_LOCATION")
            )
            if credentials_file_path and vertex_project and vertex_location:
                try:
                    with open(credentials_file_path, "r") as f:
                        creds = json.load(f)
                    litellm_kwargs["vertex_credentials"] = json.dumps(creds)
                except Exception:
                    pass
                litellm_kwargs["vertex_project"] = vertex_project
                litellm_kwargs["vertex_location"] = vertex_location
        elif api_key_name:
            key_val = _sanitize_api_key(os.getenv(api_key_name))
            if key_val:
                litellm_kwargs["api_key"] = key_val
                if is_vertex:
                    vertex_project = os.getenv("VERTEX_PROJECT")
                    vertex_location = os.getenv("VERTEX_LOCATION")
                    if vertex_project and vertex_location:
                        litellm_kwargs["vertex_project"] = vertex_project
                        litellm_kwargs["vertex_location"] = vertex_location

        api_base = model_info.get("base_url")
        if pd.notna(api_base) and api_base:
            litellm_kwargs["base_url"] = str(api_base)
            litellm_kwargs["api_base"] = str(api_base)

        is_lm_studio = str(model_name).lower().startswith("lm_studio/") or provider == "lm_studio"
        if is_lm_studio:
            if not litellm_kwargs.get("base_url"):
                base = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                litellm_kwargs["base_url"] = base
                litellm_kwargs["api_base"] = base
            if not litellm_kwargs.get("api_key"):
                litellm_kwargs["api_key"] = os.getenv("LM_STUDIO_API_KEY") or "lm-studio"

        response_format: Optional[Dict[str, Any]] = None
        if output_pydantic or output_schema:
            if model_info.get("structured_output", False):
                schema = (
                    output_pydantic.model_json_schema() if output_pydantic else output_schema
                )
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)
                response_format = {
                    "type": "json_schema",
                    "json_schema": {
                        "name": output_pydantic.__name__ if output_pydantic else "response",
                        "schema": schema,
                        "strict": True,
                    },
                }
                litellm_kwargs["response_format"] = response_format

        # Reasoning parameters
        reasoning_type = model_info.get("reasoning_type", "none")
        max_reasoning_tokens_val = model_info.get("max_reasoning_tokens", 0)
        time_kwargs: Dict[str, Any] = {}
        if time > 0:
            if reasoning_type == "budget" and max_reasoning_tokens_val > 0:
                budget = int(time * max_reasoning_tokens_val)
                if provider == "anthropic" and budget > 0:
                    thinking_param = {"type": "enabled", "budget_tokens": budget}
                    litellm_kwargs["thinking"] = thinking_param
                    time_kwargs["thinking"] = thinking_param
                    litellm_kwargs["temperature"] = 1
            elif reasoning_type == "effort":
                effort = "low" if time <= 0.3 else "medium" if time <= 0.7 else "high"
                if provider == "openai" and str(model_name).lower().startswith("gpt-5"):
                    litellm_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                else:
                    litellm_kwargs["reasoning_effort"] = effort

        try:
            if litellm.cache is not None:
                litellm_kwargs["caching"] = True
                if litellm_kwargs.get("metadata") is None:
                    litellm_kwargs["metadata"] = {}

            if use_batch_mode:
                response = litellm.batch_completion(**litellm_kwargs)
            else:
                response = litellm.completion(
                    **litellm_kwargs, timeout=LLM_CALL_TIMEOUT
                )

            results: List[Any] = []
            thinking_outputs: List[Any] = []
            response_list = response if use_batch_mode else [response]

            for i, resp_item in enumerate(response_list):
                raw_result = resp_item.choices[0].message.content
                if raw_result is None:
                    raise RuntimeError("LLM returned None content")

                parsed_result: Any = raw_result
                if output_pydantic or output_schema:
                    try:
                        if output_pydantic and isinstance(raw_result, output_pydantic):
                            parsed_result = raw_result
                        elif isinstance(raw_result, dict) and output_pydantic:
                            parsed_result = output_pydantic.model_validate(raw_result)
                        elif isinstance(raw_result, str):
                            candidates: List[str] = []
                            fenced = _extract_fenced_json_block(raw_result)
                            if fenced:
                                candidates.append(fenced)
                            else:
                                candidates.extend(_extract_balanced_json_objects(raw_result))
                            if not candidates:
                                candidates.append(raw_result.strip("` \n"))

                            for cand in candidates:
                                try:
                                    parsed_result = (
                                        output_pydantic.model_validate_json(cand)
                                        if output_pydantic
                                        else cand
                                    )
                                    break
                                except Exception:
                                    continue
                            else:
                                raise ValueError("Unable to parse JSON")
                        else:
                            raise ValueError("Unsupported structured output result type")
                    except Exception as e:
                        raise SchemaValidationError(
                            f"Failed to parse response into structured output: {e}",
                            raw_response=raw_result,
                            item_index=i,
                        ) from e

                _unescape_code_newlines(parsed_result)
                if language in (None, "python") and _has_invalid_python_code(parsed_result):
                    logger.warning(
                        f"Invalid Python syntax detected for item {i}; returning best-effort output."
                    )

                results.append(parsed_result)

                thinking = None
                try:
                    if (
                        hasattr(resp_item, "_hidden_params")
                        and resp_item._hidden_params
                        and "thinking" in resp_item._hidden_params
                    ):
                        thinking = resp_item._hidden_params["thinking"]
                    elif (
                        hasattr(resp_item.choices[0].message, "reasoning_content")
                    ):
                        thinking = resp_item.choices[0].message.reasoning_content
                except Exception:
                    pass
                thinking_outputs.append(thinking)

            total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
            return {
                "result": results if use_batch_mode else results[0],
                "cost": total_cost,
                "model_name": model_name,
                "thinking_output": thinking_outputs if use_batch_mode else thinking_outputs[0],
            }

        except SchemaValidationError as e:
            last_exception = e
            logger.warning(f"Schema validation failed for {model_name}: {e}")
            continue
        except openai.AuthenticationError as e:
            last_exception = e
            if _is_wsl_environment():
                logger.warning(
                    "Authentication failed in WSL; check API key for CRLF issues."
                )
                logger.debug(f"Env info: {_get_environment_info()}")
            if newly_acquired_keys.get(api_key_name):
                if api_key_name in os.environ:
                    del os.environ[api_key_name]
                newly_acquired_keys[api_key_name] = False
                continue
            break
        except Exception as e:
            last_exception = e
            logger.error(f"Invocation failed for {model_name}: {e}")
            continue

    error_message = "All candidate models failed."
    if last_exception:
        error_message += f" Last error ({type(last_exception).__name__}): {last_exception}"
    raise RuntimeError(error_message) from last_exception