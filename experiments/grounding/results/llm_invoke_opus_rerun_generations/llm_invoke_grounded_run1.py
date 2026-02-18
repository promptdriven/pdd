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

import openai
import pandas as pd
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

import litellm
from litellm.caching.caching import Cache

from .path_resolution import get_default_resolver

# ---------------------------------------------------------------------------
# Logging Configuration
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

# Suppress LiteLLM "Give Feedback / Get Help" banners
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# litellm.drop_params
try:
    _drop_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

if not logger.handlers:
    _ch = logging.StreamHandler()
    _ch.setFormatter(logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s"))
    logger.addHandler(_ch)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(_ch)

# Verbose env override
if os.getenv("PDD_VERBOSE_LOGGING") == "1":
    logger.setLevel(logging.DEBUG)
    litellm_logger.setLevel(logging.DEBUG)


def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    """Configure rotating file handler for logging."""
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
    """Toggle DEBUG level for all loggers."""
    want = bool(verbose) or os.getenv("PDD_VERBOSE_LOGGING") == "1"
    if want:
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
            litellm.set_verbose = want
        if hasattr(litellm, "suppress_debug_info"):
            litellm.suppress_debug_info = not want
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Rich console
# ---------------------------------------------------------------------------

console = Console()

# ---------------------------------------------------------------------------
# Constants & Project Root
# ---------------------------------------------------------------------------

LLM_CALL_TIMEOUT = 600  # seconds

PDD_PATH_ENV = os.getenv("PDD_PATH")
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()

# ---------------------------------------------------------------------------
# .env path & loading
# ---------------------------------------------------------------------------


def _is_env_path_package_dir(env_path: Path) -> bool:
    try:
        _pkg = Path(str(importlib.resources.files("pdd"))).resolve()
        env_r = env_path.resolve()
        return env_r == _pkg or str(env_r).startswith(str(_pkg))
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
else:
    ENV_PATH = PROJECT_ROOT / ".env"

if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

# ---------------------------------------------------------------------------
# CSV Path Resolution
# ---------------------------------------------------------------------------

user_model_csv_path = Path.home() / ".pdd" / "llm_model.csv"
PROJECT_ROOT_FROM_ENV = PDD_PATH_ENV is not None and PROJECT_ROOT == Path(PDD_PATH_ENV).expanduser().resolve() if PDD_PATH_ENV else False
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH: Optional[Path] = user_model_csv_path
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
else:
    LLM_MODEL_CSV_PATH = None

# ---------------------------------------------------------------------------
# Default base model
# ---------------------------------------------------------------------------

DEFAULT_BASE_MODEL: Optional[str] = os.getenv("PDD_MODEL_DEFAULT", None)

# ---------------------------------------------------------------------------
# Custom Exceptions
# ---------------------------------------------------------------------------


class SchemaValidationError(Exception):
    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0):
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
# LiteLLM Cache
# ---------------------------------------------------------------------------

GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID", "").strip() or None
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY", "").strip() or None

configured_cache: Optional[Cache] = None
_cache_configured = False

if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    litellm.cache = None
    _cache_configured = True

if not _cache_configured and GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    _orig_aws_ak = os.environ.get("AWS_ACCESS_KEY_ID")
    _orig_aws_sk = os.environ.get("AWS_SECRET_ACCESS_KEY")
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
        _cache_configured = True
    except Exception as _ce:
        warnings.warn(f"Failed to configure S3/GCS cache: {_ce}")
        litellm.cache = None
    finally:
        if _orig_aws_ak is not None:
            os.environ["AWS_ACCESS_KEY_ID"] = _orig_aws_ak
        elif "AWS_ACCESS_KEY_ID" in os.environ:
            del os.environ["AWS_ACCESS_KEY_ID"]
        if _orig_aws_sk is not None:
            os.environ["AWS_SECRET_ACCESS_KEY"] = _orig_aws_sk
        elif "AWS_SECRET_ACCESS_KEY" in os.environ:
            del os.environ["AWS_SECRET_ACCESS_KEY"]

if not _cache_configured:
    try:
        _sqlite_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(_sqlite_path))
        litellm.cache = configured_cache
        _cache_configured = True
    except Exception as _ce2:
        warnings.warn(f"Failed to configure disk cache: {_ce2}")
        litellm.cache = None

# ---------------------------------------------------------------------------
# LiteLLM Callback
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
            str(r["model"]): (float(r["input"]) if pd.notna(r["input"]) else 0.0, float(r["output"]) if pd.notna(r["output"]) else 0.0)
            for _, r in df.iterrows()
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
    in_tok = getattr(usage, "prompt_tokens", 0) or 0
    out_tok = getattr(usage, "completion_tokens", 0) or 0
    fr = getattr(completion_response.choices[0], "finish_reason", None) if getattr(completion_response, "choices", None) else None

    cost = 0.0
    try:
        cost = litellm.completion_cost(completion_response=completion_response) or 0.0
    except Exception:
        model = kwargs.get("model")
        rates = _MODEL_RATE_MAP.get(str(model)) if model else None
        if rates:
            cost = (in_tok * rates[0] + out_tok * rates[1]) / 1_000_000.0

    _LAST_CALLBACK_DATA.update({"input_tokens": in_tok, "output_tokens": out_tok, "finish_reason": fr, "cost": cost})


litellm.success_callback = [_litellm_success_callback]

# ---------------------------------------------------------------------------
# WSL helpers
# ---------------------------------------------------------------------------


def _is_wsl_environment() -> bool:
    try:
        if os.getenv("WSL_DISTRO_NAME"):
            return True
        if os.path.exists("/proc/version"):
            with open("/proc/version") as f:
                txt = f.read().lower()
                return "microsoft" in txt or "wsl" in txt
    except Exception:
        pass
    return False


def _get_environment_info() -> Dict[str, str]:
    import platform

    return {
        "platform": platform.system(),
        "python_version": platform.python_version(),
        "is_wsl": str(_is_wsl_environment()),
    }


# ---------------------------------------------------------------------------
# API key helpers
# ---------------------------------------------------------------------------


def _sanitize_api_key(key_value: Optional[str]) -> Optional[str]:
    if not key_value:
        return key_value
    sanitized = key_value.strip()
    sanitized = "".join(c for c in sanitized if ord(c) >= 32)
    return sanitized


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    lines: List[str] = []
    if env_path.exists():
        with open(env_path) as f:
            lines = f.readlines()

    new_lines: List[str] = []
    replaced = False
    prefix = f"{key_name}="
    for line in lines:
        stripped = line.strip()
        if stripped.startswith(f"# {prefix}") or stripped.startswith(f"# {key_name} ="):
            continue
        if stripped.startswith(prefix) or stripped.startswith(f"{key_name} ="):
            new_lines.append(f'{key_name}="{value}"\n')
            replaced = True
        else:
            new_lines.append(line)

    if not replaced:
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

    logger.warning("API key '%s' for model '%s' not set.", key_name, model_info.get("model"))

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
            logger.warning("SECURITY WARNING: API key saved to %s. Keep this file secure.", ENV_PATH)
        except IOError as exc:
            logger.error("Failed to update .env: %s", exc)
        return True
    except EOFError:
        return False
    except Exception as exc:
        logger.error("Unexpected error acquiring key: %s", exc)
        return False


# ---------------------------------------------------------------------------
# CSV loader
# ---------------------------------------------------------------------------


def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    df: Optional[pd.DataFrame] = None
    if csv_path is not None and csv_path.exists():
        try:
            df = pd.read_csv(csv_path)
        except Exception:
            df = None

    if df is None:
        try:
            raw = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
            df = pd.read_csv(io.StringIO(raw))
        except Exception as exc:
            raise FileNotFoundError(f"Cannot load LLM model CSV: {exc}") from exc

    required = ["provider", "model", "input", "output", "coding_arena_elo", "api_key", "structured_output", "reasoning_type"]
    for col in required:
        if col not in df.columns:
            raise RuntimeError(f"Missing required column in CSV: {col}")

    for col in ["input", "output", "coding_arena_elo", "max_tokens", "max_completion_tokens", "max_reasoning_tokens"]:
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce")

    df["input"] = df["input"].fillna(0.0)
    df["output"] = df["output"].fillna(0.0)
    df["coding_arena_elo"] = df["coding_arena_elo"].fillna(0)
    df["max_reasoning_tokens"] = df.get("max_reasoning_tokens", pd.Series(dtype="int64")).fillna(0).astype(int)
    df["avg_cost"] = (df["input"] + df["output"]) / 2
    df["structured_output"] = df["structured_output"].fillna(False).astype(bool)
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
    df["api_key"] = df["api_key"].fillna("").astype(str)
    return df


# ---------------------------------------------------------------------------
# Model selection
# ---------------------------------------------------------------------------


def _select_model_candidates(strength: float, base_model_name: Optional[str], model_df: pd.DataFrame) -> List[Dict[str, Any]]:
    if model_df.empty:
        raise ValueError("Loaded model data is empty. Check CSV file.")

    available = model_df[model_df["api_key"].notna()].copy()
    if available.empty:
        raise ValueError("No models available after filtering.")

    if base_model_name:
        base_rows = available[available["model"] == base_model_name]
    else:
        base_rows = pd.DataFrame()

    if base_rows.empty:
        base_model = available.iloc[0]
    else:
        base_model = base_rows.iloc[0]

    effective_base = str(base_model["model"])

    if strength == 0.5:
        available["sort_metric"] = -available["coding_arena_elo"]
        candidates = available.sort_values(by="sort_metric").to_dict("records")
        if any(c["model"] == effective_base for c in candidates):
            candidates.sort(key=lambda x: 0 if x["model"] == effective_base else 1)
    elif strength < 0.5:
        base_cost = base_model["avg_cost"]
        cheapest_cost = available["avg_cost"].min()
        target = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost) if base_cost > cheapest_cost else cheapest_cost
        available["sort_metric"] = abs(available["avg_cost"] - target)
        candidates = available.sort_values(by="sort_metric").to_dict("records")
    else:
        base_elo = base_model["coding_arena_elo"]
        highest_elo = available["coding_arena_elo"].max()
        target = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo) if highest_elo > base_elo else base_elo
        available["sort_metric"] = abs(available["coding_arena_elo"] - target)
        candidates = available.sort_values(by="sort_metric").to_dict("records")

    if not candidates:
        raise RuntimeError("Model selection resulted in empty candidate list.")
    return candidates


# ---------------------------------------------------------------------------
# Schema helpers
# ---------------------------------------------------------------------------


def _ensure_all_properties_required(schema: Any) -> Any:
    if not isinstance(schema, dict):
        return schema
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for ps in schema["properties"].values():
            _ensure_all_properties_required(ps)
    if schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for k in ("anyOf", "oneOf", "allOf"):
        if k in schema:
            for s in schema[k]:
                _ensure_all_properties_required(s)
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _ensure_all_properties_required(d)
    return schema


def _add_additional_properties_false(schema: Any) -> Any:
    if not isinstance(schema, dict):
        return schema
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for ps in schema["properties"].values():
                _add_additional_properties_false(ps)
    if schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    for k in ("anyOf", "oneOf", "allOf"):
        if k in schema:
            for s in schema[k]:
                _add_additional_properties_false(s)
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _add_additional_properties_false(d)
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
    time_val: float,
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
        "time": time_val,
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

    cloud_url = CloudConfig.get_endpoint_url("llmInvoke")
    headers = {"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"}

    try:
        resp = requests.post(cloud_url, json=payload, headers=headers, timeout=300)
    except requests.exceptions.Timeout:
        raise CloudFallbackError("Cloud request timed out")
    except requests.exceptions.ConnectionError as exc:
        raise CloudFallbackError(f"Cloud connection failed: {exc}")
    except requests.exceptions.RequestException as exc:
        raise CloudFallbackError(f"Cloud request failed: {exc}")

    if resp.status_code == 200:
        data = resp.json()
        result = data.get("result")
        if output_pydantic and result:
            try:
                result = _validate_with_pydantic(result, output_pydantic)
            except Exception:
                pass
        return {
            "result": result,
            "cost": data.get("totalCost", 0.0),
            "model_name": data.get("modelName", "cloud_model"),
            "thinking_output": data.get("thinkingOutput"),
        }
    elif resp.status_code == 402:
        raise InsufficientCreditsError(resp.json().get("error", "Insufficient credits"))
    elif resp.status_code in (401, 403):
        try:
            from .auth_service import clear_jwt_cache

            clear_jwt_cache()
        except Exception:
            pass
        server_err = resp.json().get("error", "")
        raise CloudFallbackError(
            f"Authentication expired ({server_err or resp.status_code}). "
            "Please re-authenticate with: pdd auth logout && pdd auth login"
        )
    elif resp.status_code >= 500:
        raise CloudFallbackError(resp.json().get("error", f"Server error ({resp.status_code})"))
    else:
        raise CloudInvocationError(f"Cloud llm_invoke failed: {resp.json().get('error', f'HTTP {resp.status_code}')}")


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
            return [[{"role": "user", "content": prompt.format(**item)}] for item in input_data]
        else:
            if not isinstance(input_data, dict):
                raise ValueError("input_json must be a dictionary when use_batch_mode is False.")
            return [{"role": "user", "content": prompt.format(**input_data)}]
    except KeyError as exc:
        raise ValueError(f"Prompt formatting error: Missing key {exc} in input_json") from exc
    except Exception as exc:
        raise ValueError(f"Error formatting prompt: {exc}") from exc


# ---------------------------------------------------------------------------
# JSON extraction
# ---------------------------------------------------------------------------


def _extract_fenced_json_block(text: str) -> Optional[str]:
    m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, flags=re.IGNORECASE)
    return m.group(1) if m else None


def _extract_balanced_json_objects(text: str) -> List[str]:
    results: List[str] = []
    depth = 0
    start = -1
    in_str = False
    esc = False
    for i, ch in enumerate(text):
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
            continue
        if ch == "{":
            if depth == 0:
                start = i
            depth += 1
        elif ch == "}":
            if depth > 0:
                depth -= 1
                if depth == 0 and start != -1:
                    results.append(text[start : i + 1])
                    start = -1
    return results


# ---------------------------------------------------------------------------
# Malformed JSON detection
# ---------------------------------------------------------------------------


def _is_malformed_json_response(content: Any, threshold: int = 100) -> bool:
    if not content or not isinstance(content, str):
        return False
    s = content.strip()
    if not s.startswith("{") or s.endswith("}"):
        return False
    count = 0
    chk = s
    while chk.endswith("\\n"):
        count += 1
        chk = chk[:-2]
    if count >= threshold:
        return True
    if s.endswith("\\"):
        return True
    return False


# ---------------------------------------------------------------------------
# Python code helpers
# ---------------------------------------------------------------------------

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


def _is_prose_field_name(name: str) -> bool:
    return name.lower() in _PROSE_FIELD_NAMES


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
    for q in ['"', "'"]:
        if code.rstrip().endswith(q):
            cand = code.rstrip()[:-1]
            try:
                ast.parse(cand)
                return cand
            except SyntaxError:
                pass
    for q in ['"', "'"]:
        if code.lstrip().startswith(q):
            cand = code.lstrip()[1:]
            try:
                ast.parse(cand)
                return cand
            except SyntaxError:
                pass
    return code


def _smart_unescape_code(code: str) -> str:
    LBN = "\\" + "n"
    if LBN not in code:
        return code
    if "\n" in code:
        return code  # mixed state
    # all-escaped state
    result: List[str] = []
    i = 0
    in_string = False
    string_char: Optional[str] = None
    PLACEHOLDER = "\x00NLE\x00"
    while i < len(code):
        if i + 1 < len(code) and code[i] == "\\":
            nc = code[i + 1]
            if in_string and nc == "n":
                result.append(PLACEHOLDER)
                i += 2
                continue
            if in_string and nc in ("t", "r", "\\", '"', "'"):
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
            if string_char and len(string_char) == 3 and i + 2 < len(code) and code[i : i + 3] == string_char:
                in_string = False
                result.append(code[i : i + 3])
                i += 3
                continue
            if string_char and len(string_char) == 1 and code[i] == string_char:
                in_string = False
                result.append(code[i])
                i += 1
                continue
        result.append(code[i])
        i += 1
    intermediate = "".join(result)
    intermediate = intermediate.replace("\\" + "r" + "\\" + "n", "\r\n")
    intermediate = intermediate.replace(LBN, "\n")
    intermediate = intermediate.replace("\\" + "t", "\t")
    return intermediate.replace(PLACEHOLDER, "\\n")


def _unescape_code_newlines(obj: Any) -> Any:
    if obj is None:
        return obj

    def _proc(s: str) -> str:
        if _looks_like_python_code(s):
            s = _smart_unescape_code(s)
            s = _repair_python_syntax(s)
        else:
            LBN = "\\" + "n"
            if LBN in s:
                s = s.replace("\\" + "r" + "\\" + "n", "\r\n").replace(LBN, "\n").replace("\\" + "t", "\t")
        return s

    if isinstance(obj, BaseModel):
        for fn in obj.model_fields:
            v = getattr(obj, fn)
            if isinstance(v, str):
                p = _proc(v)
                if p != v:
                    object.__setattr__(obj, fn, p)
            elif isinstance(v, (dict, list, BaseModel)):
                _unescape_code_newlines(v)
        return obj
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str):
                obj[k] = _proc(v)
            elif isinstance(v, (dict, list)):
                _unescape_code_newlines(v)
        return obj
    if isinstance(obj, list):
        for i, item in enumerate(obj):
            if isinstance(item, str):
                obj[i] = _proc(item)
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
        return any(_has_invalid_python_code(getattr(obj, n), field_name=n) for n in obj.model_fields)
    if isinstance(obj, dict):
        return any(_has_invalid_python_code(v, field_name=k if isinstance(k, str) else "") for k, v in obj.items())
    if isinstance(obj, list):
        return any(_has_invalid_python_code(item, field_name=field_name) for item in obj)
    return False


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

    # --- Cloud path ---
    if use_cloud is None:
        if os.environ.get("PDD_FORCE_LOCAL", "").lower() in ("1", "true", "yes"):
            use_cloud = False
        else:
            try:
                from .core.cloud import CloudConfig

                use_cloud = CloudConfig.is_cloud_enabled()
            except ImportError:
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
                time_val=time if time is not None else 0.0,
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

    # --- Validate inputs ---
    if messages:
        if use_batch_mode:
            if not isinstance(messages, list) or not all(isinstance(ml, list) for ml in messages):
                raise ValueError("'messages' must be a list of lists when use_batch_mode is True.")
            for ml in messages:
                for msg in ml:
                    if not isinstance(msg, dict) or "role" not in msg or "content" not in msg:
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

    # --- Load models ---
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)
    candidate_models = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    _set_model_rate_map(model_df)

    if verbose:
        logger.info("Candidate models selected and ordered (with strength): %s", [c["model"] for c in candidate_models])
        logger.info("Strength: %s, Temperature: %s, Time: %s", strength, temperature, time)
        if input_json is not None:
            logger.info("Input JSON:")
            logger.info(repr(input_json))

    # --- Iterate candidates ---
    last_exception: Optional[Exception] = None
    newly_acquired_keys: Dict[str, bool] = {}
    response_format: Optional[Dict[str, Any]] = None
    time_kwargs: Dict[str, Any] = {}

    for model_info in candidate_models:
        model_name = model_info["model"]
        provider = str(model_info.get("provider", "")).lower()

        if verbose:
            logger.info("\n[ATTEMPT] Trying model: %s (Provider: %s)", model_name, provider)

        retry_same = True
        current_temp = temperature
        temp_adjusted = False

        while retry_same:
            retry_same = False

            if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
                break

            # --- Build kwargs ---
            lkw: Dict[str, Any] = {
                "model": model_name,
                "messages": formatted_messages,
                "temperature": current_temp,
                "num_retries": 2,
            }

            api_key_name = model_info.get("api_key", "")
            is_vertex = provider in ("google", "googlevertexai", "vertex_ai") or str(model_name).startswith("vertex_ai/")
            model_lower = str(model_name).lower()
            is_lm_studio = model_lower.startswith("lm_studio/") or provider == "lm_studio"
            is_groq = model_lower.startswith("groq/") or provider == "groq"

            # Vertex AI
            if is_vertex and api_key_name == "VERTEX_CREDENTIALS":
                cred_path = os.getenv("VERTEX_CREDENTIALS")
                vproj = os.getenv("VERTEX_PROJECT")
                mloc = model_info.get("location")
                vloc = str(mloc).strip() if pd.notna(mloc) and str(mloc).strip() else os.getenv("VERTEX_LOCATION")
                if cred_path and vproj and vloc:
                    try:
                        with open(cred_path) as f:
                            creds = json.load(f)
                        lkw["vertex_credentials"] = json.dumps(creds)
                    except Exception:
                        pass
                    lkw["vertex_project"] = vproj
                    lkw["vertex_location"] = vloc
                elif vproj and vloc:
                    lkw["vertex_project"] = vproj
                    lkw["vertex_location"] = vloc
            elif api_key_name:
                kv = os.getenv(api_key_name)
                if kv:
                    lkw["api_key"] = _sanitize_api_key(kv)
                if is_vertex:
                    vproj = os.getenv("VERTEX_PROJECT")
                    mloc = model_info.get("location")
                    vloc = str(mloc).strip() if pd.notna(mloc) and str(mloc).strip() else os.getenv("VERTEX_LOCATION")
                    if vproj:
                        lkw["vertex_project"] = vproj
                    if vloc:
                        lkw["vertex_location"] = vloc

            # base_url
            api_base = model_info.get("base_url")
            if pd.notna(api_base) and api_base:
                lkw["base_url"] = str(api_base)
                lkw["api_base"] = str(api_base)

            # LM Studio
            if is_lm_studio:
                if not lkw.get("base_url"):
                    lm_base = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                    lkw["base_url"] = lm_base
                    lkw["api_base"] = lm_base
                if not lkw.get("api_key"):
                    lkw["api_key"] = os.getenv("LM_STUDIO_API_KEY") or "lm-studio"

            # --- Structured output ---
            response_format = None
            if output_pydantic or output_schema:
                supports = model_info.get("structured_output", False)
                if supports:
                    if output_pydantic:
                        schema = output_pydantic.model_json_schema()
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": output_pydantic.__name__, "schema": schema, "strict": True},
                        }
                    else:
                        s = dict(output_schema)  # copy
                        _ensure_all_properties_required(s)
                        _add_additional_properties_false(s)
                        response_format = {"type": "json_schema", "json_schema": {"name": "response", "schema": s, "strict": True}}

                    if is_groq and response_format:
                        schema_for_prompt = output_pydantic.model_json_schema() if output_pydantic else output_schema
                        lkw["response_format"] = {"type": "json_object"}
                        instruction = f"Respond with valid JSON matching this schema:\n```json\n{json.dumps(schema_for_prompt, indent=2)}\n```\nRespond ONLY with JSON."
                        msgs = lkw.get("messages", [])
                        if msgs and isinstance(msgs, list) and isinstance(msgs[0], dict) and msgs[0].get("role") == "system":
                            msgs[0]["content"] = instruction + "\n\n" + msgs[0]["content"]
                        else:
                            msgs.insert(0, {"role": "system", "content": instruction})
                        lkw["messages"] = msgs
                    elif is_lm_studio and response_format:
                        lkw["extra_body"] = {"response_format": response_format}
                    else:
                        lkw["response_format"] = response_format

            # --- Reasoning ---
            time_kwargs = {}
            reasoning_type = model_info.get("reasoning_type", "none")
            max_rt = int(model_info.get("max_reasoning_tokens", 0) or 0)

            if time > 0:
                if reasoning_type == "budget" and max_rt > 0:
                    budget = int(time * max_rt)
                    if budget > 0 and provider == "anthropic":
                        tp = {"type": "enabled", "budget_tokens": budget}
                        lkw["thinking"] = tp
                        time_kwargs["thinking"] = tp
                elif reasoning_type == "effort":
                    effort = "low" if time <= 0.3 else ("high" if time > 0.7 else "medium")
                    if provider == "openai" and model_lower.startswith("gpt-5"):
                        ro = {"effort": effort, "summary": "auto"}
                        lkw["reasoning"] = ro
                        time_kwargs["reasoning"] = ro
                    else:
                        lkw["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort

            # Anthropic temperature
            if provider == "anthropic" and "thinking" in lkw:
                lkw["temperature"] = 1
                current_temp = 1

            # Cache
            if litellm.cache is not None:
                lkw["caching"] = True
                if lkw.get("metadata") is None:
                    lkw["metadata"] = {}

            # Build retry provider kwargs
            retry_provider_kw = {k: v for k, v in lkw.items() if k in ("vertex_credentials", "vertex_project", "vertex_location", "api_key", "base_url", "api_base")}

            # --- Invoke ---
            try:
                # OpenAI gpt-5* via Responses API
                if not use_batch_mode and provider == "openai" and model_lower.startswith("gpt-5"):
                    try:
                        if isinstance(formatted_messages, list) and formatted_messages and isinstance(formatted_messages[0], dict):
                            input_text = "\n\n".join(f"{m.get('role','user')}: {m.get('content','')}" for m in formatted_messages)
                        else:
                            input_text = str(formatted_messages)

                        text_block: Dict[str, Any] = {"format": {"type": "text"}}
                        if output_pydantic or output_schema:
                            try:
                                s2 = output_pydantic.model_json_schema() if output_pydantic else dict(output_schema)  # type: ignore[union-attr]
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

                        rkw: Dict[str, Any] = {"model": model_name, "input": input_text, "text": text_block}
                        reasoning_param = time_kwargs.get("reasoning")
                        if reasoning_param:
                            rkw["reasoning"] = reasoning_param

                        resp = litellm.responses(**rkw)

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

                        usage = getattr(resp, "usage", None)
                        total_cost = 0.0
                        if usage:
                            in_t = getattr(usage, "input_tokens", 0) or 0
                            out_t = getattr(usage, "output_tokens", 0) or 0
                            total_cost = (in_t * (model_info.get("input", 0) or 0) + out_t * (model_info.get("output", 0) or 0)) / 1_000_000.0

                        final_result: Any = result_text
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
                                else:
                                    final_result = f"ERROR: Failed to parse structured output. Raw: {repr(result_text)[:200]}"

                        return {"result": final_result, "cost": total_cost, "model_name": model_name, "thinking_output": None}
                    except Exception as exc:
                        last_exception = exc
                        logger.error("[ERROR] Responses API failed for %s: %s", model_name, exc)
                        lkw.pop("reasoning", None)

                # Batch or single
                if use_batch_mode:
                    response = litellm.batch_completion(**lkw)
                else:
                    response = litellm.completion(**lkw, timeout=LLM_CALL_TIMEOUT)

                if verbose:
                    logger.info("[SUCCESS] Invocation successful for %s", model_name)

                # --- Process response ---
                results: List[Any] = []
                thinking_outputs: List[Optional[str]] = []
                resp_list = response if use_batch_mode else [response]

                for idx, ri in enumerate(resp_list):
                    # Thinking
                    thinking: Optional[str] = None
                    try:
                        hp = getattr(ri, "_hidden_params", None)
                        if hp and "thinking" in hp:
                            thinking = hp["thinking"]
                        elif hasattr(ri, "choices") and ri.choices:
                            rc = getattr(ri.choices[0].message, "reasoning_content", None)
                            if rc:
                                thinking = rc
                    except Exception:
                        pass
                    thinking_outputs.append(thinking)

                    raw = ri.choices[0].message.content

                    # None content retry
                    if raw is None:
                        if not use_batch_mode and prompt and input_json is not None:
                            try:
                                orig_cache = litellm.cache
                                litellm.cache = None
                                retry_msgs = _format_messages(prompt + " ", input_json, False)
                                rr = litellm.completion(model=model_name, messages=retry_msgs, temperature=current_temp, response_format=response_format, timeout=LLM_CALL_TIMEOUT, **time_kwargs, **retry_provider_kw)
                                litellm.cache = orig_cache
                                raw = rr.choices[0].message.content
                            except Exception:
                                pass
                        if raw is None:
                            results.append("ERROR: LLM returned None content")
                            continue

                    # Malformed JSON retry
                    if isinstance(raw, str) and _is_malformed_json_response(raw):
                        if not use_batch_mode and prompt and input_json is not None:
                            try:
                                oc2 = litellm.cache
                                litellm.cache = None
                                rm2 = _format_messages(prompt + " ", input_json, False)
                                rr2 = litellm.completion(model=model_name, messages=rm2, temperature=current_temp, response_format=response_format, timeout=LLM_CALL_TIMEOUT, **time_kwargs, **retry_provider_kw)
                                litellm.cache = oc2
                                r2 = rr2.choices[0].message.content
                                if r2 and not _is_malformed_json_response(r2):
                                    raw = r2
                            except Exception:
                                pass

                    # Parse structured output
                    if output_pydantic or output_schema:
                        parsed: Any = None
                        try:
                            if output_pydantic and isinstance(raw, output_pydantic):
                                parsed = raw
                            elif isinstance(raw, dict):
                                parsed = output_pydantic.model_validate(raw) if output_pydantic else json.dumps(raw)
                            elif isinstance(raw, str):
                                fenced = _extract_fenced_json_block(raw)
                                cands2 = [fenced] if fenced else _extract_balanced_json_objects(raw)
                                if not cands2:
                                    cleaned = raw.strip()
                                    if cleaned.startswith("```json"):
                                        cleaned = cleaned[7:]
                                    elif cleaned.startswith("```"):
                                        cleaned = cleaned[3:]
                                    if cleaned.endswith("```"):
                                        cleaned = cleaned[:-3]
                                    cleaned = cleaned.strip()
                                    if cleaned:
                                        cands2 = [cleaned]

                                for c2 in cands2:
                                    try:
                                        parsed = output_pydantic.model_validate_json(c2) if output_pydantic else c2
                                        break
                                    except Exception:
                                        continue

                                if parsed is None:
                                    # Try JSON repair for truncated responses
                                    cleaned2 = raw.strip()
                                    if cleaned2.startswith("{"):
                                        for suffix in ['"}', '"}}', '"}}}', "}"]:
                                            try:
                                                attempt = cleaned2.rstrip(",").rstrip("\\n").rstrip("\\") + suffix
                                                parsed = output_pydantic.model_validate_json(attempt) if output_pydantic else attempt
                                                break
                                            except Exception:
                                                continue

                            if parsed is None:
                                raise SchemaValidationError(f"Failed to parse response for item {idx}", raw_response=raw, item_index=idx)

                        except SchemaValidationError:
                            raise
                        except (ValidationError, json.JSONDecodeError, TypeError, ValueError) as pe:
                            raise SchemaValidationError(f"Parse error: {pe}", raw_response=raw, item_index=idx) from pe

                        _unescape_code_newlines(parsed)

                        if language in (None, "python") and _has_invalid_python_code(parsed):
                            if not use_batch_mode and prompt and input_json is not None:
                                try:
                                    oc3 = litellm.cache
                                    litellm.cache = None
                                    rm3 = _format_messages(prompt + "  ", input_json, False)
                                    rr3 = litellm.completion(model=model_name, messages=rm3, temperature=current_temp, response_format=response_format, timeout=LLM_CALL_TIMEOUT, **time_kwargs, **retry_provider_kw)
                                    litellm.cache = oc3
                                    rraw3 = rr3.choices[0].message.content
                                    if rraw3 and output_pydantic:
                                        try:
                                            p3 = output_pydantic.model_validate_json(rraw3) if isinstance(rraw3, str) else output_pydantic.model_validate(rraw3)
                                            _unescape_code_newlines(p3)
                                            if not _has_invalid_python_code(p3):
                                                parsed = p3
                                        except Exception:
                                            pass
                                except Exception:
                                    pass
                            else:
                                logger.warning("Cannot retry invalid Python code - batch mode or missing prompt/input_json")

                        results.append(parsed)
                    else:
                        results.append(raw)

                total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                final = results if use_batch_mode else results[0]
                final_thinking = thinking_outputs if use_batch_mode else thinking_outputs[0]

                if verbose:
                    in_tok = _LAST_CALLBACK_DATA.get("input_tokens", 0)
                    out_tok = _LAST_CALLBACK_DATA.get("output_tokens", 0)
                    logger.info("[RESULT] Model Used: %s", model_name)
                    logger.info("[RESULT] Cost (Input): $%.2f/M tokens", model_info.get("input", 0) or 0)
                    logger.info("[RESULT] Cost (Output): $%.2f/M tokens", model_info.get("output", 0) or 0)
                    logger.info("[RESULT] Tokens (Prompt): %s", in_tok)
                    logger.info("[RESULT] Tokens (Completion): %s", out_tok)
                    logger.info("[RESULT] Total Cost (from callback): $%s", f"{total_cost:.6g}")
                    logger.info("[RESULT] Max Completion Tokens: Provider Default")
                    if final_thinking:
                        logger.info("[RESULT] Thinking Output:")
                        logger.info(final_thinking)

                return {"result": final, "cost": total_cost, "model_name": model_name, "thinking_output": final_thinking if final_thinking else None}

            except openai.AuthenticationError as exc:
                last_exception = exc
                if _is_wsl_environment() and ("Illegal header" in str(exc) or "\r" in str(exc)):
                    logger.warning("[WSL AUTH ERROR] Detected WSL line ending issue in API key")
                if newly_acquired_keys.get(model_info.get("api_key", "")):
                    akn = model_info.get("api_key", "")
                    if akn in os.environ:
                        del os.environ[akn]
                    newly_acquired_keys[akn] = False
                    retry_same = True
                else:
                    break

            except SchemaValidationError as exc:
                last_exception = exc
                logger.warning("[SCHEMA ERROR] Validation failed for %s: %s", model_name, exc)
                break

            except Exception as exc:
                last_exception = exc
                le = str(exc).lower()
                if not temp_adjusted and "temperature" in le and "thinking" in le:
                    if "thinking" in lkw and provider == "anthropic":
                        current_temp = 1
                    else:
                        current_temp = 0.99
                    temp_adjusted = True
                    retry_same = True
                    continue
                logger.error("[ERROR] %s failed (%s): %s", model_name, type(exc).__name__, exc)
                break

        continue

    msg = "All candidate models failed."
    if last_exception:
        msg += f" Last error ({type(last_exception).__name__}): {last_exception}"
    raise RuntimeError(msg) from last_exception