from __future__ import annotations

import ast
import json
import logging
import os
import re
import time as time_module
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Type, Union

import litellm
import pandas as pd
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

from .path_resolution import get_default_resolver

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

LLM_CALL_TIMEOUT: int = 120
CLOUD_CALL_TIMEOUT: int = 300

_console = Console()

# ---------------------------------------------------------------------------
# Module-level state
# ---------------------------------------------------------------------------

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_MODEL_DF: Optional[pd.DataFrame] = None
_PROJECT_ROOT: Optional[Path] = None
_ENV_LOADED: bool = False
_CACHE_INITIALIZED: bool = False
_CALLBACKS_REGISTERED: bool = False
_NEWLY_ACQUIRED_KEYS: Set[str] = set()

_PROSE_FIELD_NAMES: Set[str] = {
    "reasoning",
    "explanation",
    "analysis",
    "description",
    "summary",
    "thought",
    "thoughts",
    "rationale",
    "justification",
    "note",
    "notes",
    "comment",
    "comments",
    "hint",
    "hints",
    "context",
    "background",
    "overview",
    "detail",
    "details",
    "message",
    "feedback",
}

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")


def _configure_logging() -> None:
    """Configure loggers based on environment variables."""
    env = os.getenv("PDD_ENVIRONMENT", "").lower()
    verbose = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"

    if verbose:
        default_level = "DEBUG"
    elif env == "production":
        default_level = "WARNING"
    else:
        default_level = "INFO"

    pdd_level_name = os.getenv("PDD_LOG_LEVEL", default_level).upper()
    litellm_level_name = os.getenv(
        "LITELLM_LOG_LEVEL", "WARNING" if env == "production" else "WARNING"
    ).upper()

    logger.setLevel(getattr(logging, pdd_level_name, logging.INFO))
    litellm_logger.setLevel(getattr(logging, litellm_level_name, logging.WARNING))

    if not logger.handlers:
        handler = logging.StreamHandler()
        handler.setFormatter(
            logging.Formatter("%(asctime)s [%(name)s] %(levelname)s: %(message)s")
        )
        logger.addHandler(handler)


def setup_file_logging(log_dir: Optional[Path] = None) -> None:
    """Add a rotating file handler (10 MB, 5 backups) to the pdd logger."""
    if log_dir is None:
        log_dir = _get_project_root() / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        str(log_dir / "pdd_llm_invoke.log"),
        maxBytes=10 * 1024 * 1024,
        backupCount=5,
    )
    handler.setFormatter(
        logging.Formatter("%(asctime)s [%(name)s] %(levelname)s: %(message)s")
    )
    logger.addHandler(handler)


def set_verbose_logging(enabled: bool = True) -> None:
    """Toggle DEBUG level on the pdd and litellm loggers."""
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    litellm_logger.setLevel(level)


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------


class SchemaValidationError(Exception):
    """Structured-output failed schema validation – triggers model fallback."""


class CloudFallbackError(Exception):
    """Recoverable cloud error (network, timeout, auth, 5xx).  Falls back to local.
    On 401/403 the JWT cache is cleared before raising."""


class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""


class InsufficientCreditsError(Exception):
    """402 Payment Required.  Does NOT fall back to local."""


# ---------------------------------------------------------------------------
# Startup helpers
# ---------------------------------------------------------------------------


def _get_project_root() -> Path:
    global _PROJECT_ROOT
    if _PROJECT_ROOT is not None:
        return _PROJECT_ROOT
    try:
        resolver = get_default_resolver()
        _PROJECT_ROOT = resolver.resolve_project_root()
    except Exception:
        _PROJECT_ROOT = Path.cwd()
    return _PROJECT_ROOT


def _load_env() -> None:
    global _ENV_LOADED
    if _ENV_LOADED:
        return
    root = _get_project_root()
    env_path = root / ".env"
    if env_path.exists():
        load_dotenv(str(env_path), override=False)
    _ENV_LOADED = True
    _configure_logging()

    drop = os.getenv("LITELLM_DROP_PARAMS", "true").lower()
    litellm.drop_params = drop in ("true", "1", "yes")


def _resolve_model_csv() -> Path:
    """Resolve ``llm_model.csv`` in priority order."""
    # (a) ~/.pdd/llm_model.csv
    home_csv = Path.home() / ".pdd" / "llm_model.csv"
    if home_csv.exists():
        return home_csv

    # (b) <PROJECT_ROOT>/.pdd/llm_model.csv when PDD_PATH points to a real project
    pdd_path_str = os.getenv("PDD_PATH")
    if pdd_path_str:
        pdd_p = Path(pdd_path_str).resolve()
        try:
            import pdd as _pdd_pkg

            pkg_dir = Path(_pdd_pkg.__file__).parent.resolve()
            inside_package = str(pdd_p).startswith(str(pkg_dir))
        except Exception:
            inside_package = False
        if not inside_package:
            candidate = pdd_p / ".pdd" / "llm_model.csv"
            if candidate.exists():
                return candidate

    # project root
    root = _get_project_root()
    root_csv = root / ".pdd" / "llm_model.csv"
    if root_csv.exists():
        return root_csv

    # (c) <cwd>/.pdd/llm_model.csv
    cwd_csv = Path.cwd() / ".pdd" / "llm_model.csv"
    if cwd_csv.exists():
        return cwd_csv

    # (d) packaged pdd/data/llm_model.csv
    try:
        resolver = get_default_resolver()
        return resolver.resolve_data_file("data/llm_model.csv")
    except Exception:
        pass
    try:
        import pdd as _pdd_pkg

        pkg_data = Path(_pdd_pkg.__file__).parent / "data" / "llm_model.csv"
        if pkg_data.exists():
            return pkg_data
    except Exception:
        pass
    raise FileNotFoundError("Cannot locate llm_model.csv in any search path")


def _load_model_csv() -> pd.DataFrame:
    global _MODEL_DF, _MODEL_RATE_MAP
    if _MODEL_DF is not None:
        return _MODEL_DF

    csv_path = _resolve_model_csv()
    logger.debug("Loading model CSV from %s", csv_path)
    df = pd.read_csv(csv_path)
    df.columns = [c.strip() for c in df.columns]

    for col in ("input", "output", "coding_arena_elo", "max_reasoning_tokens"):
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)

    for _, row in df.iterrows():
        model_name = str(row.get("model", "")).strip()
        if model_name:
            _MODEL_RATE_MAP[model_name] = {
                "input": float(row.get("input", 0)),
                "output": float(row.get("output", 0)),
            }

    _MODEL_DF = df
    return _MODEL_DF


# ---------------------------------------------------------------------------
# WSL diagnostics
# ---------------------------------------------------------------------------


def _is_wsl() -> bool:
    if os.getenv("WSL_DISTRO_NAME"):
        return True
    try:
        with open("/proc/version", "r") as fh:
            return "microsoft" in fh.read().lower()
    except OSError:
        return False


def _sanitize_api_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")


# ---------------------------------------------------------------------------
# API Key Management
# ---------------------------------------------------------------------------


def _save_key_to_env(key_name: str, key_val: str) -> None:
    """Write *key_name=key_val* to the project ``.env``, replacing in-place."""
    root = _get_project_root()
    env_path = root / ".env"

    if env_path.exists():
        lines = env_path.read_text().splitlines()
    else:
        lines = []

    new_lines: List[str] = []
    found = False
    for line in lines:
        stripped = line.strip()
        # Remove old commented-out versions of this key
        if stripped.startswith("#") and key_name in stripped:
            continue
        # Replace existing key in-place
        if stripped.startswith(f"{key_name}="):
            new_lines.append(f"{key_name}={key_val}")
            found = True
            continue
        new_lines.append(line)

    if not found:
        new_lines.append(f"{key_name}={key_val}")

    env_path.write_text("\n".join(new_lines) + "\n")
    logger.warning("Security: API key '%s' saved to %s", key_name, env_path)


def _check_api_key(key_name: str) -> Optional[str]:
    """Return a valid key value or *None*.  May prompt interactively."""
    if not key_name or key_name == "EXISTING_KEY":
        return None  # no check needed

    existing = os.getenv(key_name)
    if existing:
        return _sanitize_api_key(existing)

    if os.getenv("PDD_FORCE"):
        logger.debug("PDD_FORCE set – skipping interactive prompt for %s", key_name)
        return None

    _console.print(
        f"\n[yellow]API key [bold]{key_name}[/bold] not found in environment.[/yellow]"
    )
    try:
        raw = input(f"Enter value for {key_name} (or press Enter to skip): ")
    except (EOFError, KeyboardInterrupt):
        return None

    if not raw.strip():
        return None

    key_val = _sanitize_api_key(raw)
    os.environ[key_name] = key_val
    _save_key_to_env(key_name, key_val)
    _NEWLY_ACQUIRED_KEYS.add(key_name)
    return key_val


def _get_available_models(df: pd.DataFrame) -> pd.DataFrame:
    """Return the subset of *df* whose API key is present or obtainable."""
    checked: Dict[str, Optional[str]] = {}
    indices: List[int] = []

    for idx, row in df.iterrows():
        key_name = str(row.get("api_key", "")).strip()
        if not key_name or key_name == "EXISTING_KEY":
            indices.append(int(idx))
            continue

        if key_name not in checked:
            existing = os.getenv(key_name)
            if existing:
                checked[key_name] = _sanitize_api_key(existing)
            else:
                checked[key_name] = _check_api_key(key_name)

        if checked[key_name]:
            indices.append(int(idx))

    return df.loc[indices].copy().reset_index(drop=True)


# ---------------------------------------------------------------------------
# Model Selection
# ---------------------------------------------------------------------------


def _select_model(
    df: pd.DataFrame,
    strength: float,
    base_model_name: Optional[str] = None,
) -> pd.DataFrame:
    """Return *df* rows ordered by candidate preference for *strength*."""
    if df.empty:
        raise RuntimeError("No models available with valid API keys")

    df = df.copy()

    # Locate base model
    base_idx: Optional[int] = None
    if base_model_name:
        matches = df.index[df["model"] == base_model_name].tolist()
        if matches:
            base_idx = matches[0]

    # Soft fallback – first available row
    if base_idx is None:
        base_idx = df.index[0]

    if abs(strength - 0.5) < 1e-9:
        # Base first, then descending ELO
        order = [base_idx] + [
            i
            for i in df.sort_values("coding_arena_elo", ascending=False).index
            if i != base_idx
        ]
        return df.loc[order].reset_index(drop=True)

    if strength < 0.5:
        base_cost = float(df.loc[base_idx, "input"]) + float(
            df.loc[base_idx, "output"]
        )
        cheapest_cost = float((df["input"] + df["output"]).min())
        t = strength / 0.5
        target = cheapest_cost + t * (base_cost - cheapest_cost)
        df["_dist"] = abs(df["input"] + df["output"] - target)
        return df.sort_values("_dist").drop(columns=["_dist"]).reset_index(drop=True)

    # strength > 0.5
    base_elo = float(df.loc[base_idx, "coding_arena_elo"])
    max_elo = float(df["coding_arena_elo"].max())
    t = (strength - 0.5) / 0.5
    target = base_elo + t * (max_elo - base_elo)
    df["_dist"] = abs(df["coding_arena_elo"] - target)
    return df.sort_values("_dist").drop(columns=["_dist"]).reset_index(drop=True)


# ---------------------------------------------------------------------------
# Schema enforcement
# ---------------------------------------------------------------------------


def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively make every ``properties`` key required."""
    schema = dict(schema)

    if "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        schema["properties"] = {
            k: _ensure_all_properties_required(v) if isinstance(v, dict) else v
            for k, v in schema["properties"].items()
        }

    if "items" in schema and isinstance(schema["items"], dict):
        schema["items"] = _ensure_all_properties_required(schema["items"])

    for kw in ("anyOf", "oneOf", "allOf"):
        if kw in schema:
            schema[kw] = [
                _ensure_all_properties_required(s) if isinstance(s, dict) else s
                for s in schema[kw]
            ]

    if "$defs" in schema:
        schema["$defs"] = {
            k: _ensure_all_properties_required(v) if isinstance(v, dict) else v
            for k, v in schema["$defs"].items()
        }

    return schema


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively inject ``additionalProperties: false`` on every object."""
    schema = dict(schema)

    if schema.get("type") == "object" or "properties" in schema:
        schema["additionalProperties"] = False

    if "properties" in schema:
        schema["properties"] = {
            k: _add_additional_properties_false(v) if isinstance(v, dict) else v
            for k, v in schema["properties"].items()
        }

    if "items" in schema and isinstance(schema["items"], dict):
        schema["items"] = _add_additional_properties_false(schema["items"])

    for kw in ("anyOf", "oneOf", "allOf"):
        if kw in schema:
            schema[kw] = [
                _add_additional_properties_false(s) if isinstance(s, dict) else s
                for s in schema[kw]
            ]

    if "$defs" in schema:
        schema["$defs"] = {
            k: _add_additional_properties_false(v) if isinstance(v, dict) else v
            for k, v in schema["$defs"].items()
        }

    return schema


def _prepare_json_schema(
    schema: Dict[str, Any], name: str = "response"
) -> Dict[str, Any]:
    schema = _ensure_all_properties_required(schema)
    schema = _add_additional_properties_false(schema)
    return {
        "type": "json_schema",
        "json_schema": {"name": name, "schema": schema, "strict": True},
    }


# ---------------------------------------------------------------------------
# JSON parsing / repair
# ---------------------------------------------------------------------------


def _extract_json_from_response(text: str) -> Optional[str]:
    if not text:
        return None

    # Fenced ```json blocks
    fenced = re.findall(r"```(?:json)?\s*\n?(.*?)```", text, re.DOTALL)
    if fenced:
        return fenced[0].strip()

    # Balanced braces
    for open_ch, close_ch in [("{", "}"), ("[", "]")]:
        start = text.find(open_ch)
        if start < 0:
            continue
        depth = 0
        in_str = False
        esc = False
        for i in range(start, len(text)):
            c = text[i]
            if esc:
                esc = False
                continue
            if c == "\\":
                esc = True
                continue
            if c == '"':
                in_str = not in_str
                continue
            if not in_str:
                if c == open_ch:
                    depth += 1
                elif c == close_ch:
                    depth -= 1
                    if depth == 0:
                        return text[start : i + 1]

    # Fence-only cleaning
    cleaned = text.strip()
    if cleaned.startswith("```"):
        lines = cleaned.split("\n")
        lines = lines[1:]  # drop opening fence
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        return "\n".join(lines).strip()

    return text.strip()


def _repair_truncated_json(text: str) -> Optional[str]:
    closures = [
        '"}',
        '"]}',
        '"}}',
        '"]}]}',
        "}",
        "}]",
        "}}",
        "}]}",
        '"]',
        '"]}',
        "]",
        "]}",
    ]
    for c in closures:
        candidate = text + c
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            continue
    return None


def _smart_unescape_code(obj: Any) -> Any:
    """Replace double-escaped newlines while preserving ``\\n`` inside string
    literals."""
    if isinstance(obj, str):
        if "\\\\n" in obj:
            obj = obj.replace("\\\\n", "\n")
        return obj
    if isinstance(obj, dict):
        return {k: _smart_unescape_code(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_smart_unescape_code(v) for v in obj]
    return obj


def _parse_json_response(text: str) -> Any:
    if not text:
        return text

    # Direct
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass

    extracted = _extract_json_from_response(text)
    if extracted:
        try:
            return json.loads(extracted)
        except json.JSONDecodeError:
            repaired = _repair_truncated_json(extracted)
            if repaired:
                try:
                    return json.loads(repaired)
                except json.JSONDecodeError:
                    pass

    repaired = _repair_truncated_json(text.strip())
    if repaired:
        try:
            return json.loads(repaired)
        except json.JSONDecodeError:
            pass

    return text


# ---------------------------------------------------------------------------
# Python syntax repair
# ---------------------------------------------------------------------------


def _repair_python_syntax(code: str) -> str:
    if not code or not code.strip():
        return code
    lines = code.rstrip().split("\n")
    # Trailing triple-quote orphan
    if lines and lines[-1].strip() in ('"""', "'''"):
        lines = lines[:-1]
    return "\n".join(lines)


def _is_valid_python(code: str) -> bool:
    try:
        ast.parse(code)
        return True
    except SyntaxError:
        return False


def _validate_code_fields(result: Any, language: Optional[str]) -> bool:
    """Return ``True`` when all code-like fields are syntactically valid."""
    if language is not None and language.lower() != "python":
        return True

    if isinstance(result, dict):
        for key, value in result.items():
            if key.lower() in _PROSE_FIELD_NAMES:
                continue
            if isinstance(value, str) and value.strip():
                looks_like_code = any(
                    kw in value
                    for kw in ("def ", "class ", "import ", "from ", "return ")
                )
                if looks_like_code and not _is_valid_python(value):
                    repaired = _repair_python_syntax(value)
                    if _is_valid_python(repaired):
                        result[key] = repaired
                    else:
                        return False
            elif isinstance(value, (dict, list)):
                if not _validate_code_fields(value, language):
                    return False
    elif isinstance(result, list):
        for item in result:
            if not _validate_code_fields(item, language):
                return False
    return True


# ---------------------------------------------------------------------------
# Reasoning parameters
# ---------------------------------------------------------------------------


def _build_reasoning_params(
    model_row: pd.Series,
    time_val: float,
    provider: str,
    model_name: str,
) -> Dict[str, Any]:
    rtype = str(model_row.get("reasoning_type", "none")).strip().lower()
    max_tokens = int(model_row.get("max_reasoning_tokens", 0))
    params: Dict[str, Any] = {}

    if rtype == "budget" and max_tokens > 0:
        budget = max(1, int(time_val * max_tokens))
        params["thinking"] = {"type": "enabled", "budget_tokens": budget}

    elif rtype == "effort":
        if time_val <= 0.33:
            effort = "low"
        elif time_val <= 0.66:
            effort = "medium"
        else:
            effort = "high"

        if model_name.startswith("gpt-5"):
            params["reasoning"] = {"effort": effort, "summary": "auto"}
        else:
            params["reasoning_effort"] = effort

    return params


# ---------------------------------------------------------------------------
# Vertex AI
# ---------------------------------------------------------------------------


def _is_vertex_model(provider: str, model_name: str) -> bool:
    return (
        "vertex_ai" in model_name.lower()
        or model_name.startswith("vertex_ai/")
        or (provider.lower() == "google" and "vertex" in model_name.lower())
    )


def _get_vertex_credentials() -> Dict[str, Any]:
    params: Dict[str, Any] = {}
    cred_file = os.getenv("VERTEX_CREDENTIALS")
    if cred_file and Path(cred_file).exists():
        params["vertex_credentials"] = Path(cred_file).read_text()
    project = os.getenv("VERTEX_PROJECT")
    if project:
        params["vertex_project"] = project
    location = os.getenv("VERTEX_LOCATION")
    if location:
        params["vertex_location"] = location
    return params


# ---------------------------------------------------------------------------
# LM Studio
# ---------------------------------------------------------------------------


def _is_lm_studio(model_name: str, provider: str) -> bool:
    combined = f"{provider} {model_name}".lower()
    return "lm_studio" in combined or "lm-studio" in combined or "lmstudio" in combined


# ---------------------------------------------------------------------------
# LiteLLM cache
# ---------------------------------------------------------------------------


def _setup_cache() -> None:
    global _CACHE_INITIALIZED
    if _CACHE_INITIALIZED:
        return
    _CACHE_INITIALIZED = True

    if os.getenv("LITELLM_CACHE_DISABLE", "0") == "1":
        logger.debug("LiteLLM cache disabled via LITELLM_CACHE_DISABLE")
        return

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
            logger.debug("S3/GCS cache configured (bucket=%s)", bucket)
            return
        except Exception as exc:
            logger.warning("S3/GCS cache setup failed: %s", exc)

    try:
        root = _get_project_root()
        litellm.cache = litellm.Cache(
            type="disk",
            disk_cache_dir=str(root),
        )
        logger.debug("Disk cache configured at %s", root)
    except Exception as exc:
        logger.warning("Disk cache setup failed: %s", exc)


# ---------------------------------------------------------------------------
# LiteLLM callback
# ---------------------------------------------------------------------------


def _litellm_success_callback(
    kwargs: Any,
    completion_response: Any,
    start_time: Any,
    end_time: Any,
) -> None:
    global _LAST_CALLBACK_DATA
    try:
        usage: Dict[str, int] = {}
        finish_reason: Optional[str] = None

        resp_usage = getattr(completion_response, "usage", None)
        if resp_usage:
            usage = {
                "prompt_tokens": getattr(resp_usage, "prompt_tokens", 0) or 0,
                "completion_tokens": getattr(resp_usage, "completion_tokens", 0) or 0,
                "total_tokens": getattr(resp_usage, "total_tokens", 0) or 0,
            }

        choices = getattr(completion_response, "choices", None)
        if choices:
            finish_reason = getattr(choices[0], "finish_reason", None)

        cost = 0.0
        try:
            cost = litellm.completion_cost(completion_response=completion_response)
        except Exception:
            model = kwargs.get("model", "") if isinstance(kwargs, dict) else ""
            if model in _MODEL_RATE_MAP:
                rates = _MODEL_RATE_MAP[model]
                cost = (
                    usage.get("prompt_tokens", 0) * rates["input"] / 1_000_000
                    + usage.get("completion_tokens", 0) * rates["output"] / 1_000_000
                )

        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "finish_reason": finish_reason,
            "cost": cost,
        }
    except Exception as exc:
        logger.debug("Callback error: %s", exc)


def _setup_callbacks() -> None:
    global _CALLBACKS_REGISTERED
    if _CALLBACKS_REGISTERED:
        return
    _CALLBACKS_REGISTERED = True
    if _litellm_success_callback not in litellm.success_callback:
        litellm.success_callback.append(_litellm_success_callback)  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# Cost helper
# ---------------------------------------------------------------------------


def _calculate_cost(response: Any, model_name: str) -> float:
    """Best-effort cost calculation with CSV fallback."""
    try:
        return float(litellm.completion_cost(completion_response=response))
    except Exception:
        pass

    if model_name in _MODEL_RATE_MAP:
        rates = _MODEL_RATE_MAP[model_name]
        usage = getattr(response, "usage", None)
        if usage:
            pt = getattr(usage, "prompt_tokens", 0) or 0
            ct = getattr(usage, "completion_tokens", 0) or 0
            return pt * rates["input"] / 1_000_000 + ct * rates["output"] / 1_000_000

    return _LAST_CALLBACK_DATA.get("cost", 0.0)


# ---------------------------------------------------------------------------
# Cloud helpers
# ---------------------------------------------------------------------------


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    schema = _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(
    result: Any, pydantic_class: Type[BaseModel]
) -> BaseModel:
    if isinstance(result, str):
        try:
            result = json.loads(result)
        except json.JSONDecodeError:
            pass
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    raise ValueError(
        f"Cannot validate {type(result).__name__} with {pydantic_class.__name__}"
    )


def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]],
    strength: float,
    temperature: float,
    time_val: float,
    verbose: bool,
    output_schema: Optional[Dict[str, Any]],
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    """Call the remote ``llmInvoke`` cloud function."""
    try:
        from .cloud_config import CloudConfig  # type: ignore[import-untyped]
    except ImportError as exc:
        raise CloudFallbackError("cloud_config module unavailable") from exc

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
    if output_schema is not None:
        payload["outputSchema"] = output_schema
    if language is not None:
        payload["language"] = language

    cloud_config = CloudConfig()
    try:
        resp = cloud_config.call_function(
            "llmInvoke", payload, timeout=CLOUD_CALL_TIMEOUT
        )
    except Exception as exc:
        err_msg = str(exc)
        status = getattr(exc, "status_code", None) or getattr(
            getattr(exc, "response", None), "status_code", None
        )

        if status == 402:
            raise InsufficientCreditsError(err_msg) from exc

        if status in (401, 403):
            try:
                cloud_config.clear_jwt_cache()
            except Exception:
                pass
            raise CloudFallbackError(err_msg) from exc

        if (status and status >= 500) or any(
            kw in err_msg.lower() for kw in ("timeout", "network", "connection")
        ):
            raise CloudFallbackError(err_msg) from exc

        raise CloudInvocationError(err_msg) from exc

    return {
        "result": resp.get("result"),
        "cost": resp.get("totalCost", 0.0),
        "model_name": resp.get("modelName", "cloud"),
        "thinking_output": resp.get("thinkingOutput"),
    }


# ---------------------------------------------------------------------------
# Structured-output builder
# ---------------------------------------------------------------------------


def _build_response_format(
    model_row: pd.Series,
    model_name: str,
    provider: str,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    messages: List[Dict[str, Any]],
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]], List[Dict[str, Any]]]:
    """Return ``(response_format, extra_body, messages)``."""
    if output_pydantic is None and output_schema is None:
        return None, None, messages

    if output_pydantic is not None:
        schema = output_pydantic.model_json_schema()
        schema_name = output_pydantic.__name__
    else:
        assert output_schema is not None
        schema = output_schema
        schema_name = "response"

    supports = str(model_row.get("structured_output", "")).strip().lower() in (
        "true",
        "1",
        "yes",
    )

    # Groq: json_object + schema in system prompt
    if "groq" in provider.lower():
        schema_text = json.dumps(schema, indent=2)
        messages = [
            {
                "role": "system",
                "content": f"Respond with valid JSON matching this schema:\n{schema_text}",
            }
        ] + list(messages)
        return {"type": "json_object"}, None, messages

    if supports:
        prepared = _prepare_json_schema(schema, name=schema_name)
        if _is_lm_studio(model_name, provider):
            return None, {"response_format": prepared}, messages
        return prepared, None, messages

    # Model lacks structured output – instruct via system prompt
    schema_text = json.dumps(schema, indent=2)
    messages = [
        {
            "role": "system",
            "content": f"Respond with valid JSON matching this schema:\n{schema_text}",
        }
    ] + list(messages)
    return None, None, messages


# ---------------------------------------------------------------------------
# Response processing
# ---------------------------------------------------------------------------


def _extract_thinking(response: Any) -> Optional[str]:
    try:
        hp = getattr(response, "_hidden_params", None)
        if hp and "thinking" in hp:
            return hp["thinking"]
    except Exception:
        pass
    try:
        rc = getattr(response.choices[0].message, "reasoning_content", None)
        if rc:
            return rc
    except Exception:
        pass
    return None


def _process_response(
    response: Any,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
    supports_structured: bool,
) -> Any:
    content: Optional[str] = None
    try:
        content = response.choices[0].message.content
    except (IndexError, AttributeError):
        pass

    if content is None:
        return None

    if output_pydantic is not None or output_schema is not None:
        parsed = _parse_json_response(content)

        if isinstance(parsed, str):
            extracted = _extract_json_from_response(parsed)
            if extracted:
                try:
                    parsed = json.loads(extracted)
                except json.JSONDecodeError:
                    pass

        if isinstance(parsed, dict):
            parsed = _smart_unescape_code(parsed)

        if output_pydantic is not None and isinstance(parsed, (dict, list)):
            try:
                return output_pydantic.model_validate(parsed)
            except ValidationError as exc:
                raise SchemaValidationError(
                    f"Pydantic validation failed: {exc}"
                ) from exc

        if output_schema is not None and isinstance(parsed, dict):
            return parsed

        if isinstance(parsed, str):
            raise SchemaValidationError(
                f"Could not parse JSON from response: {content[:200]}"
            )
        return parsed

    return content


def _process_responses_api(
    response: Any,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
) -> Tuple[Any, Optional[str]]:
    """Extract result + thinking from Responses-API response."""
    content: Optional[str] = None
    thinking: Optional[str] = None

    try:
        if hasattr(response, "output"):
            for item in response.output:
                item_type = getattr(item, "type", None)
                if item_type == "message":
                    for ci in getattr(item, "content", []):
                        if getattr(ci, "type", None) == "output_text":
                            content = ci.text
                elif item_type == "reasoning":
                    thinking = getattr(item, "summary", None)
        elif hasattr(response, "choices"):
            content = response.choices[0].message.content
    except Exception as exc:
        logger.warning("Error processing Responses API output: %s", exc)

    if content is None:
        return None, thinking

    if output_pydantic is not None or output_schema is not None:
        parsed = _parse_json_response(content)
        if isinstance(parsed, dict):
            parsed = _smart_unescape_code(parsed)
        if output_pydantic is not None and isinstance(parsed, (dict, list)):
            try:
                return output_pydantic.model_validate(parsed), thinking
            except ValidationError as exc:
                raise SchemaValidationError(str(exc)) from exc
        return parsed, thinking

    return content, thinking


# ---------------------------------------------------------------------------
# Invocation helpers
# ---------------------------------------------------------------------------


def _invoke_single(
    call_params: Dict[str, Any],
    msgs: List[Dict[str, Any]],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    model_row: pd.Series,
    model_name: str,
    provider: str,
    language: Optional[str],
    supports_structured: bool,
    verbose: bool,
    is_anthropic: bool = False,
    has_thinking: bool = False,
) -> Dict[str, Any]:
    msgs = list(msgs)

    response_format, extra_body, msgs = _build_response_format(
        model_row=model_row,
        model_name=model_name,
        provider=provider,
        output_pydantic=output_pydantic,
        output_schema=output_schema,
        messages=msgs,
    )

    params = dict(call_params)
    params["messages"] = msgs
    if response_format is not None:
        params["response_format"] = response_format
    if extra_body is not None:
        params.setdefault("extra_body", {}).update(extra_body)

    if verbose:
        logger.debug("litellm.completion  model=%s", params.get("model"))

    response = litellm.completion(**params)

    # Handle None content – retry with slight prompt modification
    content: Optional[str] = None
    try:
        content = response.choices[0].message.content
    except (IndexError, AttributeError):
        pass

    if content is None:
        logger.info("None content received – retrying with cache bypass")
        if msgs and msgs[-1].get("role") == "user":
            msgs[-1] = dict(msgs[-1])
            msgs[-1]["content"] = msgs[-1]["content"] + " "
        params["messages"] = msgs
        response = litellm.completion(**params)
        try:
            content = response.choices[0].message.content
        except (IndexError, AttributeError):
            pass

    # Malformed JSON (excessive trailing newlines → likely truncation)
    if content and (output_pydantic or output_schema):
        trailing_newlines = len(content) - len(content.rstrip("\n"))
        if trailing_newlines > 5:
            logger.info("Excessive trailing newlines – retrying")
            if msgs and msgs[-1].get("role") == "user":
                msgs[-1] = dict(msgs[-1])
                msgs[-1]["content"] = msgs[-1]["content"].rstrip() + "  "
            params["messages"] = msgs
            response = litellm.completion(**params)

    result = _process_response(
        response, output_pydantic, output_schema, language, supports_structured
    )

    # Validate Python in code fields
    if result is not None and isinstance(result, (dict, BaseModel)):
        check = result.model_dump() if isinstance(result, BaseModel) else result
        if not _validate_code_fields(check, language):
            should_retry = language is None or (
                language and language.lower() == "python"
            )
            if should_retry:
                logger.info("Invalid Python detected – retrying")
                if msgs and msgs[-1].get("role") == "user":
                    msgs[-1] = dict(msgs[-1])
                    msgs[-1]["content"] = msgs[-1]["content"].rstrip() + "   "
                params["messages"] = msgs
                response = litellm.completion(**params)
                result = _process_response(
                    response,
                    output_pydantic,
                    output_schema,
                    language,
                    supports_structured,
                )

    thinking = _extract_thinking(response)
    return {"result": result, "thinking_output": thinking}


def _invoke_batch(
    call_params: Dict[str, Any],
    all_messages: List[List[Dict[str, Any]]],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    model_row: pd.Series,
    model_name: str,
    provider: str,
    language: Optional[str],
    supports_structured: bool,
    verbose: bool,
) -> Dict[str, Any]:
    first_msgs = all_messages[0] if all_messages else [{"role": "user", "content": ""}]
    response_format, extra_body, _ = _build_response_format(
        model_row, model_name, provider, output_pydantic, output_schema, first_msgs
    )

    params = dict(call_params)
    params["messages"] = all_messages  # type: ignore[assignment]
    if response_format is not None:
        params["response_format"] = response_format
    if extra_body is not None:
        params.setdefault("extra_body", {}).update(extra_body)

    if verbose:
        logger.debug("litellm.batch_completion  model=%s  n=%d", model_name, len(all_messages))

    responses = litellm.batch_completion(**params)

    results: List[Any] = []
    for resp in responses:
        try:
            r = _process_response(
                resp, output_pydantic, output_schema, language, supports_structured
            )
            results.append(r)
        except SchemaValidationError:
            raise
        except Exception as exc:
            logger.warning("Batch item error: %s", exc)
            results.append(None)

    return {"result": results, "thinking_output": None}


def _invoke_responses_api(
    call_params: Dict[str, Any],
    all_messages: List[List[Dict[str, Any]]],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    reasoning_params: Dict[str, Any],
    model_row: pd.Series,
    model_name: str,
    provider: str,
    language: Optional[str],
    verbose: bool,
) -> Dict[str, Any]:
    """Call ``litellm.responses()`` for gpt-5* models."""
    msgs = all_messages[0] if all_messages else [{"role": "user", "content": ""}]

    params: Dict[str, Any] = {"model": call_params["model"], "input": msgs}

    # Reasoning
    if "reasoning" in reasoning_params:
        params["reasoning"] = reasoning_params["reasoning"]

    # Structured output via text.format
    if output_pydantic is not None or output_schema is not None:
        if output_pydantic is not None:
            schema = output_pydantic.model_json_schema()
            schema_name = output_pydantic.__name__
        else:
            assert output_schema is not None
            schema = output_schema
            schema_name = "response"

        schema = _ensure_all_properties_required(schema)
        schema = _add_additional_properties_false(schema)
        params["text"] = {
            "format": {
                "type": "json_schema",
                "name": schema_name,
                "schema": schema,
                "strict": True,
            }
        }
    else:
        params["text"] = {"format": {"type": "text"}}

    # Forward credentials
    for key in (
        "api_key",
        "base_url",
        "vertex_credentials",
        "vertex_project",
        "vertex_location",
    ):
        if key in call_params:
            params[key] = call_params[key]

    if verbose:
        logger.debug("litellm.responses  model=%s", model_name)

    try:
        response = litellm.responses(**params)
    except AttributeError:
        # litellm version doesn't have responses() – fall back to completion
        logger.info("litellm.responses unavailable, falling back to completion")
        completion_params = dict(call_params)
        completion_params["messages"] = msgs
        response = litellm.completion(**completion_params)
        result = _process_response(
            response, output_pydantic, output_schema, language, True
        )
        return {"result": result, "thinking_output": _extract_thinking(response)}

    result, thinking = _process_responses_api(response, output_pydantic, output_schema)

    if result is None:
        logger.info("Responses API returned None – retrying")
        response = litellm.responses(**params)
        result, thinking = _process_responses_api(
            response, output_pydantic, output_schema
        )

    return {"result": result, "thinking_output": thinking}


# ---------------------------------------------------------------------------
# Main entry point
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
    """Invoke an LLM and return ``{result, cost, model_name, thinking_output}``."""
    global _LAST_CALLBACK_DATA

    # ------------------------------------------------------------------ init
    _load_env()
    _setup_cache()
    _setup_callbacks()

    if verbose:
        set_verbose_logging(True)

    # ------------------------------------------------- cloud execution path
    if use_cloud is not False:
        should_try_cloud = False
        if use_cloud is True:
            should_try_cloud = True
        elif use_cloud is None:
            if os.getenv("PDD_FORCE_LOCAL", "0") != "1":
                try:
                    from .cloud_config import CloudConfig  # type: ignore[import-untyped]

                    should_try_cloud = CloudConfig.is_cloud_enabled()
                except ImportError:
                    should_try_cloud = False

        if should_try_cloud:
            cloud_schema: Optional[Dict[str, Any]] = None
            if output_pydantic is not None:
                cloud_schema = _pydantic_to_json_schema(output_pydantic)
            elif output_schema is not None:
                cloud_schema = output_schema

            try:
                cloud_result = _llm_invoke_cloud(
                    prompt=prompt,
                    input_json=input_json,
                    messages=messages,
                    strength=strength,
                    temperature=temperature,
                    time_val=time,
                    verbose=verbose,
                    output_schema=cloud_schema,
                    use_batch_mode=use_batch_mode,
                    language=language,
                )
                if (
                    output_pydantic is not None
                    and cloud_result.get("result") is not None
                ):
                    try:
                        cloud_result["result"] = _validate_with_pydantic(
                            cloud_result["result"], output_pydantic
                        )
                    except Exception as exc:
                        logger.warning(
                            "Cloud pydantic validation failed: %s", exc
                        )
                return cloud_result

            except InsufficientCreditsError:
                raise
            except CloudFallbackError as exc:
                _console.print(
                    f"[yellow]Cloud failed, falling back to local: {exc}[/yellow]"
                )
                logger.warning("CloudFallbackError: %s", exc)
            except CloudInvocationError as exc:
                _console.print(
                    f"[yellow]Cloud invocation error, falling back to local: {exc}[/yellow]"
                )
                logger.warning("CloudInvocationError: %s", exc)

    # ----------------------------------------------- build message payloads
    all_messages: List[List[Dict[str, Any]]]

    if messages is not None:
        if (
            isinstance(messages, list)
            and messages
            and isinstance(messages[0], list)
        ):
            use_batch_mode = True
            all_messages = messages  # type: ignore[assignment]
        else:
            all_messages = [messages]  # type: ignore[list-item]
    elif prompt is not None:
        if input_json is not None:
            if isinstance(input_json, list):
                use_batch_mode = True
                all_messages = []
                for item in input_json:
                    try:
                        filled = (
                            prompt.format(**item)
                            if isinstance(item, dict)
                            else prompt.format(item)
                        )
                    except (KeyError, IndexError) as exc:
                        logger.warning("Template format error: %s", exc)
                        filled = prompt
                    all_messages.append([{"role": "user", "content": filled}])
            else:
                try:
                    filled = prompt.format(**input_json)
                except (KeyError, IndexError) as exc:
                    logger.warning("Template format error: %s", exc)
                    filled = prompt
                all_messages = [[{"role": "user", "content": filled}]]
        else:
            all_messages = [[{"role": "user", "content": prompt}]]
    else:
        raise ValueError("Either 'prompt' or 'messages' must be provided")

    # ---------------------------------------------------- load & select models
    df = _load_model_csv()
    available = _get_available_models(df)
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    candidates = _select_model(available, strength, base_model_name)

    # --------------------------------------------------- iterate candidates
    last_error: Optional[Exception] = None

    for _, model_row in candidates.iterrows():
        model_name: str = str(model_row["model"])
        provider: str = str(model_row.get("provider", ""))
        key_name: str = str(model_row.get("api_key", "")).strip()

        logger.info("Trying model %s (provider=%s)", model_name, provider)

        # ---- base call params ----
        call_params: Dict[str, Any] = {
            "model": model_name,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        temp = temperature
        reasoning_params = _build_reasoning_params(
            model_row, time, provider, model_name
        )

        is_anthropic = "anthropic" in provider.lower() or "claude" in model_name.lower()
        if is_anthropic and "thinking" in reasoning_params:
            temp = 1.0

        use_responses_api = model_name.startswith("gpt-5")

        if not use_responses_api:
            call_params["temperature"] = temp

        # Vertex AI
        if _is_vertex_model(provider, model_name):
            call_params.update(_get_vertex_credentials())
            loc = str(model_row.get("location", "")).strip()
            if loc:
                call_params["vertex_location"] = loc

        # LM Studio
        if _is_lm_studio(model_name, provider):
            call_params["base_url"] = os.getenv(
                "LM_STUDIO_API_BASE", "http://localhost:1234/v1"
            )
            call_params["api_key"] = "lm-studio"
        else:
            base_url_csv = str(model_row.get("base_url", "")).strip()
            if base_url_csv:
                call_params["base_url"] = base_url_csv
            if (
                key_name
                and key_name != "EXISTING_KEY"
                and not _is_vertex_model(provider, model_name)
            ):
                env_key = os.getenv(key_name)
                if env_key:
                    call_params["api_key"] = _sanitize_api_key(env_key)

        call_params.update(reasoning_params)

        supports_structured = str(model_row.get("structured_output", "")).strip().lower() in (
        "true",
        "1",
        "yes",
    )

    _LAST_CALLBACK_DATA = {}

    try:
        if use_responses_api and not use_batch_mode:
            invoke_result = _invoke_responses_api(
                call_params=call_params,
                all_messages=all_messages,
                output_pydantic=output_pydantic,
                output_schema=output_schema,
                reasoning_params=reasoning_params,
                model_row=model_row,
                model_name=model_name,
                provider=provider,
                language=language,
                verbose=verbose,
            )
        elif use_batch_mode:
            invoke_result = _invoke_batch(
                call_params=call_params,
                all_messages=all_messages,
                output_pydantic=output_pydantic,
                output_schema=output_schema,
                model_row=model_row,
                model_name=model_name,
                provider=provider,
                language=language,
                supports_structured=supports_structured,
                verbose=verbose,
            )
        else:
            invoke_result = _invoke_single(
                call_params=call_params,
                msgs=all_messages[0],
                output_pydantic=output_pydantic,
                output_schema=output_schema,
                model_row=model_row,
                model_name=model_name,
                provider=provider,
                language=language,
                supports_structured=supports_structured,
                verbose=verbose,
                is_anthropic=is_anthropic,
                has_thinking="thinking" in reasoning_params,
            )

        cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
        if cost == 0.0 and not use_responses_api:
            # Try to compute from the last response if available
            pass

        return {
            "result": invoke_result.get("result"),
            "cost": cost,
            "model_name": model_name,
            "thinking_output": invoke_result.get("thinking_output"),
        }

    except SchemaValidationError as exc:
        logger.warning(
            "Schema validation failed for %s: %s – trying next model",
            model_name,
            exc,
        )
        last_error = exc
        continue

    except litellm.AuthenticationError as exc:
        err_msg = str(exc)
        logger.warning("Auth error for %s: %s", model_name, err_msg)

        if _is_wsl():
            _console.print(
                "[yellow]WSL detected – check for carriage returns (\\r) in API keys.[/yellow]"
            )

        # Re-prompt if key was newly acquired
        if key_name in _NEWLY_ACQUIRED_KEYS:
            _NEWLY_ACQUIRED_KEYS.discard(key_name)
            _console.print(
                f"[yellow]Authentication failed for newly entered key [bold]{key_name}[/bold]. "
                f"Please re-enter.[/yellow]"
            )
            try:
                raw = input(f"Enter value for {key_name} (or press Enter to skip): ")
            except (EOFError, KeyboardInterrupt):
                raw = ""

            if raw.strip():
                new_val = _sanitize_api_key(raw)
                os.environ[key_name] = new_val
                _save_key_to_env(key_name, new_val)
                _NEWLY_ACQUIRED_KEYS.add(key_name)
                call_params["api_key"] = new_val

                try:
                    if use_responses_api and not use_batch_mode:
                        invoke_result = _invoke_responses_api(
                            call_params=call_params,
                            all_messages=all_messages,
                            output_pydantic=output_pydantic,
                            output_schema=output_schema,
                            reasoning_params=reasoning_params,
                            model_row=model_row,
                            model_name=model_name,
                            provider=provider,
                            language=language,
                            verbose=verbose,
                        )
                    elif use_batch_mode:
                        invoke_result = _invoke_batch(
                            call_params=call_params,
                            all_messages=all_messages,
                            output_pydantic=output_pydantic,
                            output_schema=output_schema,
                            model_row=model_row,
                            model_name=model_name,
                            provider=provider,
                            language=language,
                            supports_structured=supports_structured,
                            verbose=verbose,
                        )
                    else:
                        invoke_result = _invoke_single(
                            call_params=call_params,
                            msgs=all_messages[0],
                            output_pydantic=output_pydantic,
                            output_schema=output_schema,
                            model_row=model_row,
                            model_name=model_name,
                            provider=provider,
                            language=language,
                            supports_structured=supports_structured,
                            verbose=verbose,
                            is_anthropic=is_anthropic,
                            has_thinking="thinking" in reasoning_params,
                        )

                    cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                    return {
                        "result": invoke_result.get("result"),
                        "cost": cost,
                        "model_name": model_name,
                        "thinking_output": invoke_result.get("thinking_output"),
                    }
                except Exception as retry_exc:
                    logger.warning("Retry after re-key also failed: %s", retry_exc)
                    last_error = retry_exc
                    continue
            else:
                last_error = exc
                continue
        else:
            last_error = exc
            continue

    except litellm.BadRequestError as exc:
        err_msg = str(exc).lower()
        # Anthropic temperature + thinking incompatibility
        if is_anthropic and "temperature" in err_msg and "thinking" in err_msg:
            logger.info(
                "Anthropic temperature/thinking conflict – retrying with temperature=1"
            )
            call_params["temperature"] = 1.0
            try:
                if use_batch_mode:
                    invoke_result = _invoke_batch(
                        call_params=call_params,
                        all_messages=all_messages,
                        output_pydantic=output_pydantic,
                        output_schema=output_schema,
                        model_row=model_row,
                        model_name=model_name,
                        provider=provider,
                        language=language,
                        supports_structured=supports_structured,
                        verbose=verbose,
                    )
                else:
                    invoke_result = _invoke_single(
                        call_params=call_params,
                        msgs=all_messages[0],
                        output_pydantic=output_pydantic,
                        output_schema=output_schema,
                        model_row=model_row,
                        model_name=model_name,
                        provider=provider,
                        language=language,
                        supports_structured=supports_structured,
                        verbose=verbose,
                        is_anthropic=is_anthropic,
                        has_thinking="thinking" in reasoning_params,
                    )

                cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                return {
                    "result": invoke_result.get("result"),
                    "cost": cost,
                    "model_name": model_name,
                    "thinking_output": invoke_result.get("thinking_output"),
                }
            except Exception as retry_exc:
                logger.warning("Anthropic temp retry failed: %s", retry_exc)
                last_error = retry_exc
                continue
        else:
            logger.warning("BadRequestError for %s: %s", model_name, exc)
            last_error = exc
            continue

    except (
        litellm.RateLimitError,
        litellm.ServiceUnavailableError,
        litellm.Timeout,
        litellm.APIConnectionError,
    ) as exc:
        logger.warning("Transient error for %s: %s", model_name, exc)
        last_error = exc
        continue

    except Exception as exc:
        logger.warning("Unexpected error for %s: %s", model_name, exc)
        last_error = exc
        continue

raise RuntimeError(
    f"All model candidates exhausted. Last error: {last_error}"
)