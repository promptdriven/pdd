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
from pydantic import BaseModel, ValidationError
from rich.console import Console

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

# -----------------------------------------------------------------------------
# Console
# -----------------------------------------------------------------------------
console = Console()

# -----------------------------------------------------------------------------
# Logging configuration
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

# Suppress LiteLLM verbose banners
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# Drop unsupported provider params
try:
    litellm.drop_params = str(os.getenv("LITELLM_DROP_PARAMS", "true")).lower() in (
        "1",
        "true",
        "yes",
        "on",
    )
except Exception:
    litellm.drop_params = True

if not logger.handlers:
    handler = logging.StreamHandler()
    handler.setFormatter(logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s"))
    logger.addHandler(handler)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(handler)


def setup_file_logging(log_file_path: Optional[str]) -> None:
    """Configure rotating file handler (10MB, 5 backups)."""
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
        logger.warning(f"Failed to configure file logging: {e}")


def set_verbose_logging(verbose: bool) -> None:
    """Toggle DEBUG logging + LiteLLM verbosity."""
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


# -----------------------------------------------------------------------------
# Exceptions
# -----------------------------------------------------------------------------
class SchemaValidationError(Exception):
    """Raised when LLM response fails validation and should trigger fallback."""

    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0) -> None:
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index


class CloudFallbackError(Exception):
    """Raised for recoverable cloud errors; triggers local fallback."""


class CloudInvocationError(Exception):
    """Raised for non-recoverable cloud invocation errors."""


class InsufficientCreditsError(Exception):
    """Raised when cloud reports insufficient credits (402)."""


# -----------------------------------------------------------------------------
# Path / project root / CSV resolution
# -----------------------------------------------------------------------------
def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    """Search up from CWD for project markers."""
    try:
        current = Path.cwd().resolve()
        for _ in range(max_levels):
            if (
                (current / ".git").exists()
                or (current / "pyproject.toml").exists()
                or (current / "data").is_dir()
                or (current / ".env").exists()
            ):
                return current
            parent = current.parent
            if parent == current:
                break
            current = parent
    except Exception:
        pass
    return Path.cwd().resolve()


try:
    _installed_pkg_root = importlib.resources.files("pdd")
    _installed_pkg_root_path = Path(str(_installed_pkg_root))
except Exception:
    _installed_pkg_root_path = None


def _is_env_path_package_dir(env_path: Path) -> bool:
    """Return True if env_path points to installed package root (or subpath)."""
    try:
        if _installed_pkg_root_path is None:
            return False
        env_path = env_path.resolve()
        pkg_path = _installed_pkg_root_path.resolve()
        return env_path == pkg_path or str(env_path).startswith(str(pkg_path))
    except Exception:
        return False


resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env

project_root_from_cwd = _detect_project_root_from_cwd()
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"

ENV_PATH = (
    project_root_from_cwd / ".env"
    if _is_env_path_package_dir(PROJECT_ROOT)
    else PROJECT_ROOT / ".env"
)

user_model_csv_path = Path.home() / ".pdd" / "llm_model.csv"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH: Optional[Path] = user_model_csv_path
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
else:
    LLM_MODEL_CSV_PATH = None

# Load .env
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

DEFAULT_BASE_MODEL: Optional[str] = os.getenv("PDD_MODEL_DEFAULT", None)

# -----------------------------------------------------------------------------
# LiteLLM cache configuration
# -----------------------------------------------------------------------------
from litellm.caching.caching import Cache  # type: ignore

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
else:
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
            cache_configured = True
        except Exception as e:
            warnings.warn(f"Failed to configure GCS cache: {e}")
            litellm.cache = None
        finally:
            if original_aws_access_key_id is not None:
                os.environ["AWS_ACCESS_KEY_ID"] = original_aws_access_key_id
            else:
                os.environ.pop("AWS_ACCESS_KEY_ID", None)

            if original_aws_secret_access_key is not None:
                os.environ["AWS_SECRET_ACCESS_KEY"] = original_aws_secret_access_key
            else:
                os.environ.pop("AWS_SECRET_ACCESS_KEY", None)

            if original_aws_region_name is not None:
                os.environ["AWS_REGION_NAME"] = original_aws_region_name

if not cache_configured:
    try:
        sqlite_cache_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_cache_path))
        litellm.cache = configured_cache
    except Exception as e:
        warnings.warn(f"Failed to configure disk cache: {e}")
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
            str(row["model"]): (float(row["input"]), float(row["output"]))
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

    cost = 0.0
    try:
        cost_val = litellm.completion_cost(completion_response=completion_response)
        cost = float(cost_val or 0.0)
    except Exception:
        model_name = kwargs.get("model")
        if model_name and usage:
            in_tok = getattr(usage, "prompt_tokens", 0) or getattr(usage, "input_tokens", 0)
            out_tok = getattr(usage, "completion_tokens", 0) or getattr(usage, "output_tokens", 0)
            rates = _MODEL_RATE_MAP.get(str(model_name))
            if rates:
                in_rate, out_rate = rates
                cost = (in_tok * in_rate + out_tok * out_rate) / 1_000_000.0

    _LAST_CALLBACK_DATA.update(
        {
            "input_tokens": input_tokens,
            "output_tokens": output_tokens,
            "finish_reason": finish_reason,
            "cost": cost,
        }
    )


litellm.success_callback = [_litellm_success_callback]

# -----------------------------------------------------------------------------
# JSON schema helpers
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
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _ensure_all_properties_required(sub)
    return schema


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(schema, dict):
        return schema
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values():
                _add_additional_properties_false(prop)
    if schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _add_additional_properties_false(sub)
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


# -----------------------------------------------------------------------------
# Cloud invocation
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

    headers = {
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/json",
    }

    cloud_url = CloudConfig.get_endpoint_url("llmInvoke")
    if verbose:
        logger.debug(f"Cloud llmInvoke request: {cloud_url}")

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
        raise CloudInvocationError(response.json().get("error", f"HTTP {response.status_code}"))
    except requests.exceptions.Timeout as e:
        raise CloudFallbackError(f"Cloud request timed out: {e}")
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")


# -----------------------------------------------------------------------------
# Misc helpers
# -----------------------------------------------------------------------------
def _is_wsl_environment() -> bool:
    try:
        if os.getenv("WSL_DISTRO_NAME"):
            return True
        if os.path.exists("/proc/version"):
            with open("/proc/version", "r") as f:
                return "microsoft" in f.read().lower() or "wsl" in f.read().lower()
        path_env = os.getenv("PATH", "")
        return "/mnt/c/" in path_env.lower()
    except Exception:
        return False


def _get_environment_info() -> Dict[str, str]:
    import platform

    return {
        "platform": platform.system(),
        "platform_release": platform.release(),
        "platform_version": platform.version(),
        "architecture": platform.machine(),
        "python_version": platform.python_version(),
        "is_wsl": str(_is_wsl_environment()),
    }


def _is_malformed_json_response(content: str, threshold: int = 100) -> bool:
    if not content or not isinstance(content, str):
        return False
    stripped = content.strip()
    if not stripped.startswith("{"):
        return False
    if stripped.endswith("}"):
        return False
    trailing = 0
    tmp = stripped
    while tmp.endswith("\\n"):
        trailing += 1
        tmp = tmp[:-2]
    if trailing >= threshold:
        return True
    if stripped.endswith("\\"):
        return True
    return False


def _sanitize_api_key(key_value: Optional[str]) -> Optional[str]:
    if not key_value:
        return key_value
    sanitized = key_value.strip()
    if any(ord(c) < 32 for c in sanitized):
        sanitized = "".join(c for c in sanitized if ord(c) >= 32)
    if key_value != sanitized and "\r" in key_value:
        if _is_wsl_environment():
            logger.info("Detected WSL line ending issue in API key")
    return sanitized


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    lines: List[str] = []
    if env_path.exists():
        lines = env_path.read_text().splitlines(keepends=True)

    new_lines: List[str] = []
    replaced = False
    prefix = f"{key_name}="
    prefix_spaced = f"{key_name} ="

    for line in lines:
        stripped = line.strip()
        if stripped.startswith(f"# {prefix}") or stripped.startswith(f"# {prefix_spaced}"):
            continue
        if stripped.startswith(prefix) or stripped.startswith(prefix_spaced):
            new_lines.append(f'{key_name}="{value}"\n')
            replaced = True
        else:
            new_lines.append(line)

    if not replaced:
        if new_lines and not new_lines[-1].endswith("\n"):
            new_lines.append("\n")
        new_lines.append(f'{key_name}="{value}"\n')

    env_path.write_text("".join(new_lines))


def _ensure_api_key(
    model_info: Dict[str, Any],
    newly_acquired_keys: Dict[str, bool],
    verbose: bool,
) -> bool:
    key_name = model_info.get("api_key")
    if not key_name or key_name == "EXISTING_KEY":
        return True

    key_value = _sanitize_api_key(os.getenv(key_name))
    if key_value:
        newly_acquired_keys[key_name] = False
        return True

    logger.warning(f"API key '{key_name}' for model '{model_info.get('model')}' not set.")
    if os.getenv("PDD_FORCE"):
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
            logger.warning("SECURITY WARNING: API key saved to .env file.")
        except IOError as e:
            logger.error(f"Failed to update .env file: {e}")
        return True
    except EOFError:
        return False
    except Exception as e:
        logger.error(f"Unexpected error during API key input: {e}")
        return False


def _format_messages(
    prompt: str,
    input_data: Union[Dict[str, Any], List[Dict[str, Any]]],
    use_batch_mode: bool,
) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    try:
        if use_batch_mode:
            if not isinstance(input_data, list):
                raise ValueError("input_json must be a list of dicts for batch mode.")
            msgs: List[List[Dict[str, str]]] = []
            for item in input_data:
                if not isinstance(item, dict):
                    raise ValueError("Each batch item must be a dict.")
                formatted = prompt.format(**item)
                msgs.append([{"role": "user", "content": formatted}])
            return msgs
        if not isinstance(input_data, dict):
            raise ValueError("input_json must be a dict when use_batch_mode is False.")
        formatted = prompt.format(**input_data)
        return [{"role": "user", "content": formatted}]
    except KeyError as e:
        raise ValueError(f"Prompt formatting error: Missing key {e} in input_json") from e
    except Exception as e:
        raise ValueError(f"Error formatting prompt: {e}") from e


def _extract_fenced_json_block(text: str) -> Optional[str]:
    try:
        match = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, flags=re.IGNORECASE)
        return match.group(1) if match else None
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

    stripped = code.strip()
    for quote in ['"', "'"]:
        if stripped.startswith(quote) and stripped.endswith(quote):
            candidate = stripped[1:-1]
            try:
                ast.parse(candidate)
                return candidate
            except SyntaxError:
                pass
    return code


def _smart_unescape_code(code: str) -> str:
    if "\\n" not in code:
        return code
    has_actual_newlines = "\n" in code
    if has_actual_newlines:
        return code

    result: List[str] = []
    i = 0
    in_string = False
    string_char: Optional[str] = None
    placeholder = "\x00NEWLINE_ESCAPE\x00"

    while i < len(code):
        if i + 1 < len(code) and code[i] == "\\":
            next_char = code[i + 1]
            if in_string and next_char == "n":
                result.append(placeholder)
                i += 2
                continue

        if not in_string:
            if i + 2 < len(code) and code[i : i + 3] in ('"""', "'''"):
                in_string = True
                string_char = code[i : i + 3]
                result.append(string_char)
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
                if code[i : i + 3] == string_char:
                    in_string = False
                    result.append(string_char)
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
    intermediate = intermediate.replace("\\r\\n", "\r\n").replace("\\n", "\n").replace("\\t", "\t")
    return intermediate.replace(placeholder, "\\n")


def _unescape_code_newlines(obj: Any) -> Any:
    if obj is None:
        return obj

    def _process_string(s: str) -> str:
        if _looks_like_python_code(s):
            return _repair_python_syntax(_smart_unescape_code(s))
        return s.replace("\\r\\n", "\r\n").replace("\\n", "\n").replace("\\t", "\t")

    if isinstance(obj, BaseModel):
        for field in obj.model_fields:
            value = getattr(obj, field)
            if isinstance(value, str):
                object.__setattr__(obj, field, _process_string(value))
            elif isinstance(value, (dict, list, BaseModel)):
                _unescape_code_newlines(value)
        return obj

    if isinstance(obj, dict):
        for key, val in obj.items():
            if isinstance(val, str):
                obj[key] = _process_string(val)
            elif isinstance(val, (dict, list)):
                _unescape_code_newlines(val)
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
        return False
    if isinstance(obj, dict):
        for key, val in obj.items():
            if _has_invalid_python_code(val, field_name=str(key)):
                return True
        return False
    if isinstance(obj, list):
        for item in obj:
            if _has_invalid_python_code(item, field_name=field_name):
                return True
        return False
    return False


# -----------------------------------------------------------------------------
# Model loading and selection
# -----------------------------------------------------------------------------
def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    if csv_path is not None and csv_path.exists():
        try:
            df = pd.read_csv(csv_path)
        except Exception:
            df = pd.DataFrame()
    else:
        df = pd.DataFrame()

    if df.empty:
        try:
            csv_data = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
            df = pd.read_csv(pd.compat.StringIO(csv_data))  # type: ignore[attr-defined]
        except Exception:
            csv_data = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
            df = pd.read_csv(pd.io.common.StringIO(csv_data))  # type: ignore

    required = [
        "provider",
        "model",
        "input",
        "output",
        "coding_arena_elo",
        "api_key",
        "structured_output",
        "reasoning_type",
    ]
    for col in required:
        if col not in df.columns:
            raise RuntimeError(f"Missing required column '{col}' in LLM model CSV")

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
    df["structured_output"] = df["structured_output"].fillna(False).astype(bool)
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
    df["api_key"] = df["api_key"].fillna("").astype(str)
    return df


def _select_model_candidates(
    strength: float, base_model_name: Optional[str], model_df: pd.DataFrame
) -> List[Dict[str, Any]]:
    if model_df.empty:
        raise ValueError("Loaded model data is empty")
    available_df = model_df[model_df["api_key"].notna()].copy()
    if available_df.empty:
        raise ValueError("No models available after filtering")

    if base_model_name:
        base_row = available_df[available_df["model"] == base_model_name]
    else:
        base_row = pd.DataFrame()

    if base_row.empty:
        base_model = available_df.iloc[0]
    else:
        base_model = base_row.iloc[0]

    if strength == 0.5:
        available_df["sort_metric"] = -available_df["coding_arena_elo"]
        candidates = available_df.sort_values("sort_metric").to_dict("records")
        base_name = str(base_model["model"])
        candidates.sort(key=lambda x: 0 if x["model"] == base_name else 1)
        return candidates

    if strength < 0.5:
        base_cost = float(base_model["avg_cost"])
        cheapest_model = available_df.loc[available_df["avg_cost"].idxmin()]
        cheapest_cost = float(cheapest_model["avg_cost"])
        if base_cost <= cheapest_cost:
            target_cost = cheapest_cost + strength * (base_cost - cheapest_cost)
        else:
            target_cost = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost)
        available_df["sort_metric"] = (available_df["avg_cost"] - target_cost).abs()
        return available_df.sort_values("sort_metric").to_dict("records")

    base_elo = float(base_model["coding_arena_elo"])
    highest_elo = float(available_df["coding_arena_elo"].max())
    if highest_elo <= base_elo:
        target_elo = base_elo + (strength - 0.5) * (highest_elo - base_elo)
    else:
        target_elo = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo)
    available_df["sort_metric"] = (available_df["coding_arena_elo"] - target_elo).abs()
    return available_df.sort_values("sort_metric").to_dict("records")


# -----------------------------------------------------------------------------
# Main function
# -----------------------------------------------------------------------------
LLM_CALL_TIMEOUT = 120


def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict, List[Dict]]] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict] = None,
    time: Optional[float] = DEFAULT_TIME,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict], List[List[Dict]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    set_verbose_logging(verbose)

    # Cloud execution
    if use_cloud is None:
        force_local = os.getenv("PDD_FORCE_LOCAL", "").lower() in ("1", "true", "yes")
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
                time=float(time or 0),
                use_batch_mode=use_batch_mode,
                messages=messages,
                language=language,
            )
        except CloudFallbackError as e:
            console.print(
                f"[yellow]Cloud execution failed ({e}), falling back to local...[/yellow]"
            )
            logger.warning(f"Cloud fallback: {e}")
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as e:
            console.print(f"[yellow]Cloud error ({e}), falling back to local...[/yellow]")
            logger.warning(f"Cloud invocation error: {e}")

    # Input validation
    if messages:
        if use_batch_mode:
            if not isinstance(messages, list) or not all(isinstance(m, list) for m in messages):
                raise ValueError("'messages' must be list of lists when use_batch_mode is True.")
            for mlist in messages:
                for msg in mlist:
                    if not isinstance(msg, dict) or "role" not in msg or "content" not in msg:
                        raise ValueError("Each message must have 'role' and 'content'.")
        else:
            if not isinstance(messages, list) or not all(
                isinstance(m, dict) and "role" in m and "content" in m for m in messages
            ):
                raise ValueError("'messages' must be list of dicts with 'role' and 'content'.")
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

    # Model loading and selection
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)
    candidate_models = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    _set_model_rate_map(model_df)

    last_exception: Optional[Exception] = None
    newly_acquired_keys: Dict[str, bool] = {}

    for model_info in candidate_models:
        model_name = model_info["model"]
        provider = str(model_info.get("provider", "")).lower()

        if verbose:
            logger.info(f"[ATTEMPT] Trying model: {model_name}")

        retry_with_same_model = True
        current_temperature = temperature
        temp_adjustment_done = False

        while retry_with_same_model:
            retry_with_same_model = False

            if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
                break

            # LiteLLM kwargs
            litellm_kwargs: Dict[str, Any] = {
                "model": model_name,
                "messages": formatted_messages,
                "temperature": current_temperature,
                "num_retries": 2,
            }

            # Vertex AI credentials
            api_key_name = model_info.get("api_key")
            is_vertex = (
                provider == "google"
                or provider == "vertex_ai"
                or str(model_name).startswith("vertex_ai/")
            )
            if is_vertex and api_key_name == "VERTEX_CREDENTIALS":
                cred_path = os.getenv("VERTEX_CREDENTIALS")
                vertex_project = os.getenv("VERTEX_PROJECT")
                model_location = model_info.get("location")
                vertex_location = (
                    str(model_location).strip()
                    if pd.notna(model_location) and str(model_location).strip()
                    else os.getenv("VERTEX_LOCATION")
                )
                if cred_path and vertex_project and vertex_location:
                    try:
                        with open(cred_path, "r") as f:
                            creds = json.load(f)
                        litellm_kwargs["vertex_credentials"] = json.dumps(creds)
                    except Exception:
                        pass
                    litellm_kwargs["vertex_project"] = vertex_project
                    litellm_kwargs["vertex_location"] = vertex_location

            # API key for other providers
            if api_key_name and api_key_name != "VERTEX_CREDENTIALS":
                key_value = _sanitize_api_key(os.getenv(api_key_name))
                if key_value:
                    litellm_kwargs["api_key"] = key_value

            # base_url override
            api_base = model_info.get("base_url")
            if pd.notna(api_base) and api_base:
                litellm_kwargs["base_url"] = str(api_base)
                litellm_kwargs["api_base"] = str(api_base)

            # LM Studio handling
            is_lm_studio = str(model_name).lower().startswith("lm_studio/") or provider == "lm_studio"
            if is_lm_studio:
                if not litellm_kwargs.get("base_url"):
                    lm_base = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                    litellm_kwargs["base_url"] = lm_base
                    litellm_kwargs["api_base"] = lm_base
                if not litellm_kwargs.get("api_key"):
                    litellm_kwargs["api_key"] = os.getenv("LM_STUDIO_API_KEY") or "lm-studio"

            # Structured output handling
            response_format: Optional[Dict[str, Any]] = None
            if output_pydantic or output_schema:
                supports_structured = bool(model_info.get("structured_output", False))
                if supports_structured:
                    if output_pydantic:
                        schema = output_pydantic.model_json_schema()
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {
                                "name": output_pydantic.__name__,
                                "schema": schema,
                                "strict": True,
                            },
                        }
                    else:
                        schema = output_schema or {}
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": "response", "schema": schema, "strict": True},
                        }
                    litellm_kwargs["response_format"] = response_format

                    # LM Studio uses extra_body
                    if is_lm_studio and response_format:
                        litellm_kwargs["extra_body"] = {"response_format": response_format}
                        litellm_kwargs.pop("response_format", None)

                    # Groq: json_object + schema instruction in prompt
                    if str(model_name).lower().startswith("groq/") or provider == "groq":
                        litellm_kwargs["response_format"] = {"type": "json_object"}
                        schema_json = schema if output_pydantic else output_schema
                        schema_instr = (
                            "You must respond with valid JSON matching this schema:\n"
                            f"```json\n{json.dumps(schema_json, indent=2)}\n```\n"
                            "Respond ONLY with the JSON object, no other text."
                        )
                        msgs = litellm_kwargs["messages"]
                        if msgs and msgs[0].get("role") == "system":
                            msgs[0]["content"] = schema_instr + "\n\n" + msgs[0]["content"]
                        else:
                            msgs.insert(0, {"role": "system", "content": schema_instr})
                        litellm_kwargs["messages"] = msgs

            # Reasoning params
            reasoning_type = model_info.get("reasoning_type", "none")
            max_reasoning_tokens = int(model_info.get("max_reasoning_tokens", 0) or 0)
            time_kwargs: Dict[str, Any] = {}
            if time and time > 0:
                if reasoning_type == "budget" and max_reasoning_tokens > 0:
                    budget = int(time * max_reasoning_tokens)
                    if provider == "anthropic" and budget > 0:
                        litellm_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                        time_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                elif reasoning_type == "effort":
                    effort = "low"
                    if time > 0.7:
                        effort = "high"
                    elif time > 0.3:
                        effort = "medium"
                    if provider == "openai" and str(model_name).lower().startswith("gpt-5"):
                        litellm_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                        time_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                    else:
                        litellm_kwargs["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort

            # Caching
            if litellm.cache is not None:
                litellm_kwargs["caching"] = True
                if litellm_kwargs.get("metadata") is None:
                    litellm_kwargs["metadata"] = {}

            # OpenAI Responses API for GPT-5
            model_lower = str(model_name).lower()
            if not use_batch_mode and provider == "openai" and model_lower.startswith("gpt-5"):
                try:
                    if isinstance(formatted_messages, list) and formatted_messages:
                        input_text = "\n\n".join(
                            f"{m.get('role','user')}: {m.get('content','')}"
                            for m in formatted_messages
                        )
                    else:
                        input_text = str(formatted_messages)

                    text_block = {"format": {"type": "text"}}
                    if output_pydantic or output_schema:
                        if output_pydantic:
                            schema = output_pydantic.model_json_schema()
                            name = output_pydantic.__name__
                        else:
                            schema = output_schema or {}
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

                    responses_kwargs: Dict[str, Any] = {
                        "model": model_name,
                        "input": input_text,
                        "text": text_block,
                    }
                    if "reasoning" in time_kwargs:
                        responses_kwargs["reasoning"] = time_kwargs["reasoning"]

                    resp = litellm.responses(**responses_kwargs)
                    result_text = None
                    try:
                        for item in resp.output:
                            if getattr(item, "type", None) == "message":
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
                        total_cost = (
                            in_tok * float(model_info.get("input", 0.0))
                            + out_tok * float(model_info.get("output", 0.0))
                        ) / 1_000_000.0

                    final_result: Any = result_text
                    if output_pydantic and result_text:
                        try:
                            final_result = output_pydantic.model_validate_json(result_text)
                        except Exception:
                            # Attempt repair and return error string if failed
                            fenced = _extract_fenced_json_block(result_text)
                            candidates = [fenced] if fenced else _extract_balanced_json_objects(result_text)
                            cleaned = result_text.strip()
                            cleaned = cleaned.replace("```json", "").replace("```", "").strip()
                            if cleaned and cleaned not in candidates:
                                candidates.append(cleaned)
                            parsed_ok = False
                            for cand in candidates:
                                try:
                                    final_result = output_pydantic.model_validate_json(cand)
                                    parsed_ok = True
                                    break
                                except Exception:
                                    continue
                            if not parsed_ok:
                                final_result = (
                                    "ERROR: Failed to parse structured output from Responses API."
                                )

                    return {
                        "result": final_result,
                        "cost": total_cost,
                        "model_name": model_name,
                        "thinking_output": None,
                    }
                except Exception as e:
                    last_exception = e

            # Standard completion / batch
            try:
                if provider == "anthropic" and "thinking" in litellm_kwargs:
                    litellm_kwargs["temperature"] = 1
                    current_temperature = 1

                if use_batch_mode:
                    response = litellm.batch_completion(**litellm_kwargs)
                    response_list = response
                else:
                    response = litellm.completion(**litellm_kwargs, timeout=LLM_CALL_TIMEOUT)
                    response_list = [response]

                results: List[Any] = []
                thinking_outputs: List[Any] = []

                for i, resp_item in enumerate(response_list):
                    thinking = None
                    try:
                        if getattr(resp_item, "_hidden_params", None) and "thinking" in resp_item._hidden_params:
                            thinking = resp_item._hidden_params["thinking"]
                        elif (
                            resp_item.choices
                            and hasattr(resp_item.choices[0], "message")
                            and hasattr(resp_item.choices[0].message, "get")
                        ):
                            thinking = resp_item.choices[0].message.get("reasoning_content")
                    except Exception:
                        pass
                    thinking_outputs.append(thinking)

                    raw_result = resp_item.choices[0].message.content

                    if raw_result is None:
                        if not use_batch_mode and prompt and input_json is not None:
                            modified_prompt = prompt + " "
                            retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                            original_cache = litellm.cache
                            litellm.cache = None
                            retry_response = litellm.completion(
                                model=model_name,
                                messages=retry_messages,
                                temperature=current_temperature,
                                response_format=response_format,
                                timeout=LLM_CALL_TIMEOUT,
                            )
                            litellm.cache = original_cache
                            raw_result = retry_response.choices[0].message.content
                        if raw_result is None:
                            results.append("ERROR: LLM returned None content")
                            continue

                    if isinstance(raw_result, str) and _is_malformed_json_response(raw_result):
                        if not use_batch_mode and prompt and input_json is not None:
                            modified_prompt = prompt + " "
                            retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                            original_cache = litellm.cache
                            litellm.cache = None
                            retry_response = litellm.completion(
                                model=model_name,
                                messages=retry_messages,
                                temperature=current_temperature,
                                response_format=response_format,
                                timeout=LLM_CALL_TIMEOUT,
                            )
                            litellm.cache = original_cache
                            raw_result = retry_response.choices[0].message.content or raw_result

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
                                candidates = [fenced] if fenced else _extract_balanced_json_objects(raw_result)
                                if not candidates:
                                    raise ValueError("No JSON-like content found")
                                for cand in candidates:
                                    try:
                                        if output_pydantic:
                                            parsed_result = output_pydantic.model_validate_json(cand)
                                        else:
                                            json.loads(cand)
                                            parsed_result = cand
                                        json_string_to_parse = cand
                                        break
                                    except Exception:
                                        continue
                                if parsed_result is None:
                                    cleaned = raw_result.strip().replace("```json", "").replace("```", "").strip()
                                    json_string_to_parse = cleaned
                                    if output_pydantic:
                                        parsed_result = output_pydantic.model_validate_json(cleaned)
                                    else:
                                        json.loads(cleaned)
                                        parsed_result = cleaned
                            if parsed_result is None:
                                raise ValueError("Unable to parse structured output")
                        except Exception as e:
                            raise SchemaValidationError(
                                f"Failed to parse structured output: {e}",
                                raw_response=raw_result,
                                item_index=i,
                            ) from e

                        _unescape_code_newlines(parsed_result)

                        if language in (None, "python") and _has_invalid_python_code(parsed_result):
                            if not use_batch_mode and prompt and input_json is not None:
                                modified_prompt = prompt + "  "
                                retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                original_cache = litellm.cache
                                litellm.cache = None
                                retry_response = litellm.completion(
                                    model=model_name,
                                    messages=retry_messages,
                                    temperature=current_temperature,
                                    response_format=response_format,
                                    timeout=LLM_CALL_TIMEOUT,
                                )
                                litellm.cache = original_cache
                                retry_raw = retry_response.choices[0].message.content
                                try:
                                    retry_parsed = (
                                        output_pydantic.model_validate_json(retry_raw)
                                        if output_pydantic
                                        else retry_raw
                                    )
                                    _unescape_code_newlines(retry_parsed)
                                    if not _has_invalid_python_code(retry_parsed):
                                        parsed_result = retry_parsed
                                except Exception:
                                    pass

                        results.append(parsed_result)
                    else:
                        results.append(raw_result)

                total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                final_result = results if use_batch_mode else results[0]
                final_thinking = thinking_outputs if use_batch_mode else thinking_outputs[0]

                return {
                    "result": final_result,
                    "cost": total_cost,
                    "model_name": model_name,
                    "thinking_output": final_thinking,
                }
            except openai.AuthenticationError as e:
                last_exception = e
                if _is_wsl_environment() and ("Illegal header value" in str(e) or "\r" in str(e)):
                    logger.warning("WSL auth error detected; check API key line endings.")
                    logger.debug(_get_environment_info())
                if newly_acquired_keys.get(api_key_name):
                    os.environ.pop(api_key_name, None)
                    newly_acquired_keys[api_key_name] = False
                    retry_with_same_model = True
                else:
                    break
            except SchemaValidationError as e:
                last_exception = e
                break
            except Exception as e:
                last_exception = e
                lower = str(e).lower()
                if (
                    not temp_adjustment_done
                    and "temperature" in lower
                    and "thinking" in lower
                    and provider == "anthropic"
                ):
                    current_temperature = 1
                    temp_adjustment_done = True
                    retry_with_same_model = True
                    continue
                break

    error_message = "All candidate models failed."
    if last_exception:
        error_message += f" Last error ({type(last_exception).__name__}): {last_exception}"
    raise RuntimeError(error_message) from last_exception