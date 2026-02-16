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
from typing import Any, Dict, List, Optional, Type, Union

import litellm
import pandas as pd
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

from .path_resolution import get_default_resolver

# ---------------------------------------------------------------------------
# Console
# ---------------------------------------------------------------------------
console = Console(stderr=True)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
LLM_CALL_TIMEOUT: int = 120
_CLOUD_TIMEOUT: int = 300  # 5 minutes

_PROSE_FIELD_NAMES: frozenset[str] = frozenset(
    {
        "reasoning",
        "explanation",
        "analysis",
        "description",
        "summary",
        "thought",
        "rationale",
        "justification",
        "notes",
        "comment",
        "comments",
        "thinking",
        "plan",
        "approach",
        "observation",
        "observations",
        "reflection",
        "review",
    }
)

# Module-level mutable state
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_NEWLY_ACQUIRED_KEYS: set[str] = set()
_model_df: Optional[pd.DataFrame] = None
_cache_initialized: bool = False
_initialized: bool = False
_project_root_cache: Optional[Path] = None

# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------


class SchemaValidationError(Exception):
    """Raised when structured output fails schema validation – triggers model fallback."""


class CloudFallbackError(Exception):
    """Recoverable cloud error – triggers fallback to local execution.

    On 401/403 the caller should clear the JWT cache.
    """


class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""


class InsufficientCreditsError(Exception):
    """402 Payment Required – does **NOT** fall back to local."""


# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logger: logging.Logger = logging.getLogger("pdd.llm_invoke")
_litellm_logger: logging.Logger = logging.getLogger("litellm")


def _configure_logging() -> None:
    """Configure logging levels from environment variables."""
    env = os.getenv("PDD_ENVIRONMENT", "").lower()

    # PDD log level
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = logging.DEBUG
    elif env == "production":
        pdd_level = logging.WARNING
    else:
        pdd_level = getattr(
            logging, os.getenv("PDD_LOG_LEVEL", "INFO").upper(), logging.INFO
        )

    logger.setLevel(pdd_level)

    # LiteLLM log level
    litellm_default = "WARNING"
    litellm_level = getattr(
        logging,
        os.getenv("LITELLM_LOG_LEVEL", litellm_default).upper(),
        logging.WARNING,
    )
    _litellm_logger.setLevel(litellm_level)

    if not logger.handlers:
        handler = logging.StreamHandler()
        handler.setFormatter(
            logging.Formatter("[%(name)s] %(levelname)s: %(message)s")
        )
        logger.addHandler(handler)


def setup_file_logging(log_dir: Optional[str] = None) -> None:
    """Add a rotating file handler (10 MB, 5 backups)."""
    if log_dir is None:
        log_dir = str(Path.home() / ".pdd" / "logs")
    os.makedirs(log_dir, exist_ok=True)
    fh = RotatingFileHandler(
        os.path.join(log_dir, "llm_invoke.log"),
        maxBytes=10 * 1024 * 1024,
        backupCount=5,
    )
    fh.setFormatter(
        logging.Formatter("%(asctime)s [%(name)s] %(levelname)s: %(message)s")
    )
    logger.addHandler(fh)


def set_verbose_logging(enabled: bool = True) -> None:
    """Toggle DEBUG level on the *pdd.llm_invoke* logger."""
    logger.setLevel(logging.DEBUG if enabled else logging.INFO)


# ---------------------------------------------------------------------------
# WSL Diagnostics
# ---------------------------------------------------------------------------


def _is_wsl() -> bool:
    if os.getenv("WSL_DISTRO_NAME"):
        return True
    try:
        with open("/proc/version", "r") as fh:
            return "microsoft" in fh.read().lower()
    except (FileNotFoundError, PermissionError):
        return False


def _sanitize_api_key(key: str) -> str:
    """Strip whitespace and control characters from an API key."""
    return key.strip().replace("\r", "").replace("\n", "")


# ---------------------------------------------------------------------------
# Startup helpers: project root, .env, CSV resolution
# ---------------------------------------------------------------------------


def _resolve_project_root() -> Path:
    resolver = get_default_resolver()
    return resolver.resolve_project_root()


def _load_env() -> Path:
    """Load *.env* from the project root and return that root."""
    project_root = _resolve_project_root()
    env_path = project_root / ".env"
    if env_path.exists():
        load_dotenv(str(env_path), override=False)
    return project_root


def _resolve_model_csv() -> Path:
    """Resolve *llm_model.csv* in priority order:

    (a) ``~/.pdd/llm_model.csv``
    (b) ``<PROJECT_ROOT>/.pdd/llm_model.csv`` when ``$PDD_PATH`` is a real project
    (c) ``<cwd>/.pdd/llm_model.csv``
    (d) packaged ``pdd/data/llm_model.csv``
    """
    # (a)
    home_csv = Path.home() / ".pdd" / "llm_model.csv"
    if home_csv.exists():
        return home_csv

    # (b)
    pdd_path_env = os.getenv("PDD_PATH")
    if pdd_path_env:
        pdd_p = Path(pdd_path_env)
        # Ensure PDD_PATH is not inside the installed package
        try:
            import pdd as _pdd_pkg

            pkg_dir = Path(_pdd_pkg.__file__).parent
            inside_pkg = str(pdd_p.resolve()).startswith(str(pkg_dir.resolve()))
        except (ImportError, AttributeError, TypeError):
            inside_pkg = False
        if not inside_pkg:
            candidate = pdd_p / ".pdd" / "llm_model.csv"
            if candidate.exists():
                return candidate

    # (c)
    cwd_csv = Path.cwd() / ".pdd" / "llm_model.csv"
    if cwd_csv.exists():
        return cwd_csv

    # (d)
    try:
        resolver = get_default_resolver()
        return Path(resolver.resolve_data_file("data/llm_model.csv"))
    except (ValueError, FileNotFoundError, AttributeError):
        pass

    fallback = Path(__file__).parent / "data" / "llm_model.csv"
    if fallback.exists():
        return fallback

    raise FileNotFoundError(
        "Could not locate llm_model.csv in any search location"
    )


# ---------------------------------------------------------------------------
# Model CSV loading
# ---------------------------------------------------------------------------


def _load_model_csv() -> pd.DataFrame:
    global _model_df, _MODEL_RATE_MAP
    if _model_df is not None:
        return _model_df

    csv_path = _resolve_model_csv()
    logger.debug("Loading model CSV from %s", csv_path)
    df = pd.read_csv(str(csv_path))
    df.columns = df.columns.str.strip().str.lower()

    required = {"model", "provider", "input", "output", "api_key"}
    missing = required - set(df.columns)
    if missing:
        raise ValueError(f"Model CSV missing required columns: {missing}")

    # Defaults
    for col, default in (
        ("coding_arena_elo", 0),
        ("structured_output", False),
        ("reasoning_type", "none"),
        ("max_reasoning_tokens", 0),
        ("location", ""),
        ("base_url", ""),
    ):
        if col not in df.columns:
            df[col] = default

    df["coding_arena_elo"] = (
        pd.to_numeric(df["coding_arena_elo"], errors="coerce").fillna(0)
    )
    df["input"] = pd.to_numeric(df["input"], errors="coerce").fillna(0)
    df["output"] = pd.to_numeric(df["output"], errors="coerce").fillna(0)
    df["max_reasoning_tokens"] = (
        pd.to_numeric(df["max_reasoning_tokens"], errors="coerce")
        .fillna(0)
        .astype(int)
    )
    df["structured_output"] = (
        df["structured_output"]
        .astype(str)
        .str.strip()
        .str.lower()
        .isin(("true", "1", "yes"))
    )
    df["reasoning_type"] = (
        df["reasoning_type"].fillna("none").astype(str).str.strip().str.lower()
    )
    df["location"] = df["location"].fillna("").astype(str).str.strip()
    df["base_url"] = df["base_url"].fillna("").astype(str).str.strip()
    df["api_key"] = df["api_key"].fillna("").astype(str).str.strip()

    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row["model"]] = {
            "input": float(row["input"]),
            "output": float(row["output"]),
        }

    _model_df = df
    return df


# ---------------------------------------------------------------------------
# LiteLLM Caching
# ---------------------------------------------------------------------------


def _init_cache(project_root: Path) -> None:
    global _cache_initialized
    if _cache_initialized:
        return

    if os.getenv("LITELLM_CACHE_DISABLE", "0") == "1":
        logger.debug("LiteLLM caching disabled via LITELLM_CACHE_DISABLE=1")
        _cache_initialized = True
        return

    # Prefer S3-compatible GCS cache
    gcs_access = os.getenv("GCS_HMAC_ACCESS_KEY_ID")
    gcs_secret = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
    gcs_bucket = os.getenv("GCS_BUCKET_NAME")

    if gcs_access and gcs_secret and gcs_bucket:
        try:
            litellm.cache = litellm.Cache(
                type="s3",
                s3_bucket_name=gcs_bucket,
                s3_region_name="auto",
                s3_access_key_id=gcs_access,
                s3_secret_access_key=gcs_secret,
                s3_endpoint_url="https://storage.googleapis.com",
            )
            logger.debug("LiteLLM cache: S3-compatible GCS")
            _cache_initialized = True
            return
        except Exception as exc:
            logger.warning("GCS cache init failed (%s), falling back to disk", exc)

    # Disk-based SQLite fallback
    try:
        litellm.cache = litellm.Cache(
            type="disk",
            disk_cache_dir=str(project_root),
            disk_cache_filename="litellm_cache.sqlite",
        )
        logger.debug("LiteLLM cache: disk at %s", project_root)
    except Exception as exc:
        logger.warning("Disk cache init failed: %s", exc)

    _cache_initialized = True


# ---------------------------------------------------------------------------
# LiteLLM Success Callback
# ---------------------------------------------------------------------------


def _litellm_success_callback(
    kwargs: Dict[str, Any],
    completion_response: Any,
    start_time: Any,
    end_time: Any,
) -> None:
    global _LAST_CALLBACK_DATA
    data: Dict[str, Any] = {
        "model": kwargs.get("model", ""),
        "cost": 0.0,
        "usage": {},
        "finish_reason": None,
    }

    # Token usage
    try:
        if hasattr(completion_response, "usage") and completion_response.usage:
            usage = completion_response.usage
            data["usage"] = {
                "prompt_tokens": getattr(usage, "prompt_tokens", 0) or 0,
                "completion_tokens": getattr(usage, "completion_tokens", 0) or 0,
                "total_tokens": getattr(usage, "total_tokens", 0) or 0,
            }
    except Exception:
        pass

    # Finish reason
    try:
        if hasattr(completion_response, "choices") and completion_response.choices:
            data["finish_reason"] = getattr(
                completion_response.choices[0], "finish_reason", None
            )
    except Exception:
        pass

    # Cost
    try:
        data["cost"] = litellm.completion_cost(
            completion_response=completion_response
        )
    except Exception:
        model = data["model"]
        if model in _MODEL_RATE_MAP and data.get("usage"):
            rates = _MODEL_RATE_MAP[model]
            pt = data["usage"].get("prompt_tokens", 0)
            ct = data["usage"].get("completion_tokens", 0)
            data["cost"] = pt * rates["input"] / 1_000_000 + ct * rates["output"] / 1_000_000

    _LAST_CALLBACK_DATA = data


def _register_callback() -> None:
    if _litellm_success_callback not in litellm.success_callback:
        litellm.success_callback.append(_litellm_success_callback)  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# API Key Management
# ---------------------------------------------------------------------------


def _save_key_to_env(env_path: Path, key_name: str, key_value: str) -> None:
    """Save *key_name* to the *.env* file, replacing any existing entry in-place."""
    lines: List[str] = []
    replaced = False

    if env_path.exists():
        with open(env_path, "r") as fh:
            for line in fh:
                stripped = line.strip()
                # Remove old commented-out versions of this key
                if stripped.startswith("#"):
                    uncommented = stripped.lstrip("#").strip()
                    if uncommented.startswith(f"{key_name}=") or uncommented.startswith(
                        f"{key_name} ="
                    ):
                        continue
                # Replace existing key in-place (no comment + append)
                if stripped.startswith(f"{key_name}=") or stripped.startswith(
                    f"{key_name} ="
                ):
                    lines.append(f'{key_name}="{key_value}"\n')
                    replaced = True
                    continue
                lines.append(line)

    if not replaced:
        lines.append(f'{key_name}="{key_value}"\n')

    with open(env_path, "w") as fh:
        fh.writelines(lines)


def _check_and_acquire_api_key(key_name: str, project_root: Path) -> bool:
    """Return *True* when the required key is available (or not needed).

    Interactive prompt when key is missing and ``PDD_FORCE`` is unset.
    """
    if not key_name or key_name.upper() == "EXISTING_KEY":
        return True

    existing = os.getenv(key_name)
    if existing and existing.strip():
        return True

    # Non-interactive
    if os.getenv("PDD_FORCE"):
        logger.debug("PDD_FORCE set – skipping model requiring %s", key_name)
        return False

    # Interactive prompt
    try:
        console.print(
            f"\n[yellow]API key [bold]{key_name}[/bold] not found in environment.[/yellow]"
        )
        raw = input(f"Enter value for {key_name} (or press Enter to skip): ")
    except (EOFError, KeyboardInterrupt):
        return False

    if not raw.strip():
        return False

    value = _sanitize_api_key(raw)
    os.environ[key_name] = value

    env_path = project_root / ".env"
    _save_key_to_env(env_path, key_name, value)

    _NEWLY_ACQUIRED_KEYS.add(key_name)
    logger.warning("Security: API key %s saved to %s", key_name, env_path)
    return True


# ---------------------------------------------------------------------------
# Vertex AI Support
# ---------------------------------------------------------------------------


def _is_vertex_model(row: pd.Series) -> bool:
    provider = str(row.get("provider", "")).lower()
    model = str(row.get("model", ""))
    return "vertex" in provider or model.startswith("vertex_ai/")


def _get_vertex_credentials() -> Optional[Dict[str, Any]]:
    creds_path = os.getenv("VERTEX_CREDENTIALS")
    if creds_path and Path(creds_path).exists():
        try:
            with open(creds_path, "r") as fh:
                return json.load(fh)
        except (json.JSONDecodeError, IOError) as exc:
            logger.warning("Failed to load VERTEX_CREDENTIALS: %s", exc)
    return None


def _build_vertex_params(row: pd.Series) -> Dict[str, Any]:
    params: Dict[str, Any] = {}
    creds = _get_vertex_credentials()
    if creds:
        params["vertex_credentials"] = json.dumps(creds)
    project = os.getenv("VERTEX_PROJECT")
    if project:
        params["vertex_project"] = project
    location = str(row.get("location", "")).strip()
    if location:
        params["vertex_location"] = location
    else:
        env_loc = os.getenv("VERTEX_LOCATION")
        if env_loc:
            params["vertex_location"] = env_loc
    return params


# ---------------------------------------------------------------------------
# LM Studio Support
# ---------------------------------------------------------------------------


def _is_lm_studio_model(row: pd.Series) -> bool:
    model = str(row.get("model", "")).lower()
    provider = str(row.get("provider", "")).lower()
    return any(
        tag in model or tag in provider for tag in ("lm-studio", "lm_studio")
    )


def _get_lm_studio_params() -> Dict[str, Any]:
    base_url = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
    return {"base_url": base_url, "api_key": "lm-studio"}


# ---------------------------------------------------------------------------
# Model Selection
# ---------------------------------------------------------------------------


def _select_model_candidates(
    strength: float, df: pd.DataFrame, project_root: Path
) -> List[pd.Series]:
    """Return an ordered list of model candidates for *strength*."""
    available: List[pd.Series] = []
    for _, row in df.iterrows():
        key_name = str(row["api_key"]).strip()
        if _check_and_acquire_api_key(key_name, project_root):
            available.append(row)

    if not available:
        raise RuntimeError("No models available – all API keys missing or skipped")

    avail_df = pd.DataFrame(available)

    # Base model
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row: Optional[pd.Series] = None
    if base_model_name:
        matches = avail_df[avail_df["model"] == base_model_name]
        if not matches.empty:
            base_row = matches.iloc[0]

    # Soft fallback – first available as surrogate (silently)
    if base_row is None:
        base_row = available[0]

    # strength ≈ 0.5 ──────────────────────────────────────────────
    if abs(strength - 0.5) < 1e-9:
        rest = [r for r in available if r["model"] != base_row["model"]]
        rest.sort(key=lambda r: float(r["coding_arena_elo"]), reverse=True)
        return [base_row] + rest

    # strength < 0.5 ─ interpolate by cost ─────────────────────────
    if strength < 0.5:
        base_cost = float(base_row["input"]) + float(base_row["output"])
        cheapest_cost = min(
            float(r["input"]) + float(r["output"]) for r in available
        )
        t = strength / 0.5
        target_cost = cheapest_cost + t * (base_cost - cheapest_cost)
        return sorted(
            available,
            key=lambda r: abs(
                (float(r["input"]) + float(r["output"])) - target_cost
            ),
        )

    # strength > 0.5 ─ interpolate by ELO ─────────────────────────
    base_elo = float(base_row["coding_arena_elo"])
    highest_elo = max(float(r["coding_arena_elo"]) for r in available)
    t = (strength - 0.5) / 0.5
    target_elo = base_elo + t * (highest_elo - base_elo)
    return sorted(
        available,
        key=lambda r: abs(float(r["coding_arena_elo"]) - target_elo),
    )


# ---------------------------------------------------------------------------
# Schema Helpers
# ---------------------------------------------------------------------------


def _ensure_required_recursive(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict):
        return
    if "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for v in schema["properties"].values():
            _ensure_required_recursive(v)
    if "items" in schema and isinstance(schema["items"], dict):
        _ensure_required_recursive(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _ensure_required_recursive(sub)
    for defs_key in ("$defs", "definitions"):
        if defs_key in schema:
            for d in schema[defs_key].values():
                _ensure_required_recursive(d)


def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively ensure every ``properties`` block has a full ``required`` array."""
    schema = copy.deepcopy(schema)
    _ensure_required_recursive(schema)
    return schema


def _ap_false_recursive(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict):
        return
    if schema.get("type") == "object" or "properties" in schema:
        schema["additionalProperties"] = False
    if "properties" in schema:
        for v in schema["properties"].values():
            _ap_false_recursive(v)
    if "items" in schema and isinstance(schema["items"], dict):
        _ap_false_recursive(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _ap_false_recursive(sub)
    for defs_key in ("$defs", "definitions"):
        if defs_key in schema:
            for d in schema[defs_key].values():
                _ap_false_recursive(d)


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively add ``additionalProperties: false`` on every object schema."""
    schema = copy.deepcopy(schema)
    _ap_false_recursive(schema)
    return schema


# ---------------------------------------------------------------------------
# Reasoning Parameters
# ---------------------------------------------------------------------------


def _build_reasoning_params(
    row: pd.Series, time_val: float, model_name: str
) -> Dict[str, Any]:
    reasoning_type = str(row.get("reasoning_type", "none")).strip().lower()
    max_tokens = int(row.get("max_reasoning_tokens", 0))
    params: Dict[str, Any] = {}

    if reasoning_type == "budget" and max_tokens > 0:
        budget_tokens = max(int(time_val * max_tokens), 1024)
        params["thinking"] = {"type": "enabled", "budget_tokens": budget_tokens}

    elif reasoning_type == "effort":
        if time_val <= 0.33:
            effort = "low"
        elif time_val <= 0.66:
            effort = "medium"
        else:
            effort = "high"

        bare = model_name.split("/")[-1] if "/" in model_name else model_name
        if bare.startswith("gpt-5"):
            # Handled via Responses API
            params["_reasoning_effort"] = effort
        else:
            params["reasoning_effort"] = effort

    return params


# ---------------------------------------------------------------------------
# Structured Output Formatting
# ---------------------------------------------------------------------------


def _prepare_schema(
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
) -> tuple[Dict[str, Any], str]:
    """Return ``(schema, name)`` from either a Pydantic model or raw dict."""
    if output_pydantic is not None:
        raw = output_pydantic.model_json_schema()
        name = output_pydantic.__name__
    else:
        raw = copy.deepcopy(output_schema)  # type: ignore[arg-type]
        name = raw.get("title", "response_schema") if isinstance(raw, dict) else "response_schema"

    schema = _ensure_all_properties_required(raw)
    schema = _add_additional_properties_false(schema)
    schema.pop("title", None)
    schema.pop("description", None)
    return schema, name


def _build_response_format(
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    model_name: str,
    row: pd.Series,
    messages: List[Dict[str, Any]],
) -> tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]], List[Dict[str, Any]]]:
    """Return ``(response_format, extra_body, messages)``."""
    if output_pydantic is None and output_schema is None:
        return None, None, messages

    schema, schema_name = _prepare_schema(output_pydantic, output_schema)
    supports = bool(row.get("structured_output", False))
    is_lm_studio = _is_lm_studio_model(row)
    is_groq = "groq" in str(row.get("provider", "")).lower()

    if is_groq:
        schema_str = json.dumps(schema, indent=2)
        sys_msg: Dict[str, Any] = {
            "role": "system",
            "content": (
                "You must respond with valid JSON matching this schema:\n"
                f"```json\n{schema_str}\n```"
            ),
        }
        return {"type": "json_object"}, None, [sys_msg] + list(messages)

    if supports:
        rf: Dict[str, Any] = {
            "type": "json_schema",
            "json_schema": {
                "name": schema_name,
                "schema": schema,
                "strict": True,
            },
        }
        if is_lm_studio:
            return None, {"response_format": rf}, messages
        return rf, None, messages

    # Model lacks structured output – inject schema instructions
    schema_str = json.dumps(schema, indent=2)
    sys_msg = {
        "role": "system",
        "content": (
            "You must respond with valid JSON matching this schema:\n"
            f"```json\n{schema_str}\n```\n"
            "Respond ONLY with the JSON object, no additional text."
        ),
    }
    return None, None, [sys_msg] + list(messages)


# ---------------------------------------------------------------------------
# Response Parsing
# ---------------------------------------------------------------------------


def _extract_json_from_fenced(text: str) -> Optional[str]:
    matches = re.findall(r"```(?:json)?\s*\n?(.*?)```", text, re.DOTALL)
    return matches[0].strip() if matches else None


def _extract_balanced_json(text: str) -> Optional[str]:
    start = text.find("{")
    if start == -1:
        return None
    depth = 0
    in_string = False
    escape_next = False
    for i in range(start, len(text)):
        c = text[i]
        if escape_next:
            escape_next = False
            continue
        if c == "\\":
            escape_next = True
            continue
        if c == '"':
            in_string = not in_string
            continue
        if in_string:
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    return text[start:]  # truncated


def _repair_truncated_json(text: str) -> Optional[str]:
    closures = [
        "}",
        '"}',
        '"}\n}',
        '"]}\n}',
        '"]}',
        "}]",
        '"}]',
        '"}]}',
        "\"}]}\n}",
        "null}",
        "null]}",
    ]
    for c in closures:
        candidate = text + c
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            continue
    return None


def _clean_fences(text: str) -> str:
    text = text.strip()
    if text.startswith("```json"):
        text = text[7:]
    elif text.startswith("```"):
        text = text[3:]
    if text.endswith("```"):
        text = text[:-3]
    return text.strip()


def _try_parse(text: str) -> Any:
    """Try to parse *text* as JSON using multiple strategies."""
    # Direct
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass

    # Fenced
    fenced = _extract_json_from_fenced(text)
    if fenced:
        try:
            return json.loads(fenced)
        except json.JSONDecodeError:
            rep = _repair_truncated_json(fenced)
            if rep:
                try:
                    return json.loads(rep)
                except json.JSONDecodeError:
                    pass

    # Balanced extraction
    balanced = _extract_balanced_json(text)
    if balanced:
        try:
            return json.loads(balanced)
        except json.JSONDecodeError:
            rep = _repair_truncated_json(balanced)
            if rep:
                try:
                    return json.loads(rep)
                except json.JSONDecodeError:
                    pass

    # Fence cleaning
    cleaned = _clean_fences(text)
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError:
        rep = _repair_truncated_json(cleaned)
        if rep:
            try:
                return json.loads(rep)
            except json.JSONDecodeError:
                pass

    # Last-resort repair on original
    rep = _repair_truncated_json(text.strip())
    if rep:
        try:
            return json.loads(rep)
        except json.JSONDecodeError:
            pass

    raise ValueError(f"Could not parse JSON from response: {text[:200]}…")


def _parse_json_response(
    text: str,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
) -> Any:
    if output_pydantic is None and output_schema is None:
        return text
    return _try_parse(text)


# ---------------------------------------------------------------------------
# Python Validation / Repair
# ---------------------------------------------------------------------------


def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines while preserving ``\\n`` inside string literals."""
    if "\\n" not in text:
        return text
    # Replace only truly double-escaped newlines
    return text.replace("\\\\n", "\n")


def _repair_python_syntax(code: str) -> str:
    lines = [l.rstrip() for l in code.split("\n")]
    code = "\n".join(lines)
    if code.count('"""') % 2 != 0:
        code += '\n"""'
    if code.count("'''") % 2 != 0:
        code += "\n'''"
    return code


def _validate_python_code(code: str) -> bool:
    try:
        ast.parse(code)
        return True
    except SyntaxError:
        return False


def _is_prose_field(name: str) -> bool:
    return name.lower() in _PROSE_FIELD_NAMES


def _validate_code_in_result(result: Any, language: Optional[str]) -> bool:
    """Return *True* when all code fields are valid (or language is not Python)."""
    if language is not None and language.lower() != "python":
        return True
    if not isinstance(result, dict):
        if isinstance(result, str):
            return _validate_python_code(result)
        return True

    code_keywords = ("def ", "class ", "import ", "from ", "if ", "for ", "while ")
    for key, value in result.items():
        if _is_prose_field(key):
            continue
        if isinstance(value, str) and value.strip():
            if any(kw in value for kw in code_keywords):
                if not _validate_python_code(value):
                    repaired = _repair_python_syntax(value)
                    if _validate_python_code(repaired):
                        result[key] = repaired
                    else:
                        return False
    return True


# ---------------------------------------------------------------------------
# Thinking Extraction
# ---------------------------------------------------------------------------


def _extract_thinking(response: Any) -> Optional[str]:
    try:
        hidden = getattr(response, "_hidden_params", None) or {}
        if "thinking" in hidden:
            return str(hidden["thinking"])
    except Exception:
        pass
    try:
        if hasattr(response, "choices") and response.choices:
            rc = getattr(response.choices[0].message, "reasoning_content", None)
            if rc:
                return str(rc)
    except Exception:
        pass
    return None


# ---------------------------------------------------------------------------
# Cloud Execution
# ---------------------------------------------------------------------------


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    """Convert a Pydantic model to JSON Schema for cloud transport."""
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
    return pydantic_class.model_validate(result)


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
    """Execute *llm_invoke* via the cloud ``llmInvoke`` endpoint."""
    try:
        from .cloud_config import CloudConfig  # type: ignore[import-untyped]
    except ImportError:
        raise CloudFallbackError("Cloud config module not available")

    config = CloudConfig()

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
    if output_pydantic is not None:
        payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema is not None:
        payload["outputSchema"] = output_schema

    try:
        import requests as req_lib  # type: ignore[import-untyped]

        url = config.get_function_url("llmInvoke")
        headers = {
            "Authorization": f"Bearer {config.get_auth_token()}",
            "Content-Type": "application/json",
        }

        resp = req_lib.post(url, json=payload, headers=headers, timeout=_CLOUD_TIMEOUT)

        if resp.status_code == 402:
            raise InsufficientCreditsError(resp.text)
        if resp.status_code in (401, 403):
            try:
                config.clear_token_cache()
            except Exception:
                pass
            raise CloudFallbackError(f"Authentication error: {resp.status_code}")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Server error: {resp.status_code} – {resp.text[:200]}")
        if resp.status_code != 200:
            raise CloudInvocationError(f"Cloud error {resp.status_code}: {resp.text[:200]}")

        data = resp.json()
        cloud_result = data.get("result", "")

        if output_pydantic is not None and cloud_result:
            cloud_result = _validate_with_pydantic(cloud_result, output_pydantic)

        return {
            "result": cloud_result,
            "cost": data.get("totalCost", 0.0),
            "model_name": data.get("modelName", "cloud"),
            "thinking_output": data.get("thinkingOutput"),
        }

    except (InsufficientCreditsError, CloudFallbackError, CloudInvocationError):
        raise
    except Exception as exc:
        raise CloudFallbackError(f"Cloud request failed: {exc}")


# ---------------------------------------------------------------------------
# Message Construction
# ---------------------------------------------------------------------------


def _build_messages(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
) -> List[Dict[str, str]]:
    if prompt is None:
        return [{"role": "user", "content": ""}]
    content = prompt
    if isinstance(input_json, dict):
        try:
            content = prompt.format(**input_json)
        except (KeyError, IndexError) as exc:
            logger.warning("Template formatting failed (%s) – using raw prompt", exc)
    return [{"role": "user", "content": content}]


# ---------------------------------------------------------------------------
# OpenAI gpt-5* Responses API
# ---------------------------------------------------------------------------


def _is_gpt5_model(model_name: str) -> bool:
    bare = model_name.split("/")[-1] if "/" in model_name else model_name
    return bare.startswith("gpt-5")


def _invoke_responses_api(
    model: str,
    messages: List[Dict[str, str]],
    reasoning_params: Dict[str, Any],
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    api_key: Optional[str] = None,
) -> Any:
    """Call ``litellm.responses()`` for gpt-5* models."""
    input_items: List[Dict[str, str]] = [
        {"role": m.get("role", "user"), "content": m.get("content", "")}
        for m in messages
    ]

    kwargs: Dict[str, Any] = {
        "model": model,
        "input": input_items,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    effort = reasoning_params.pop("_reasoning_effort", None)
    if effort:
        kwargs["reasoning"] = {"effort": effort, "summary": "auto"}

    # Structured output via text.format
    if output_pydantic is not None or output_schema is not None:
        schema, schema_name = _prepare_schema(output_pydantic, output_schema)
        kwargs["text"] = {
            "format": {
                "type": "json_schema",
                "name": schema_name,
                "schema": schema,
                "strict": True,
            }
        }

    if api_key:
        kwargs["api_key"] = api_key

    return litellm.responses(**kwargs)


def _parse_responses_api_result(
    response: Any,
) -> tuple[str, Optional[str]]:
    """Extract ``(content, thinking)`` from a Responses-API response object."""
    content_parts: List[str] = []
    thinking_parts: List[str] = []

    if hasattr(response, "output"):
        for item in response.output:
            item_type = getattr(item, "type", None)
            if item_type == "message":
                for block in getattr(item, "content", []):
                    if getattr(block, "type", "") == "output_text":
                        content_parts.append(getattr(block, "text", ""))
            elif item_type == "reasoning":
                for block in getattr(item, "summary", []):
                    thinking_parts.append(getattr(block, "text", ""))

    content = "".join(content_parts)
    thinking = "\n".join(thinking_parts) if thinking_parts else None
    return content, thinking


# ---------------------------------------------------------------------------
# Content Extraction
# ---------------------------------------------------------------------------


def _extract_content(response: Any) -> Optional[str]:
    try:
        return response.choices[0].message.content  # type: ignore[union-attr]
    except (AttributeError, IndexError):
        return None


# ---------------------------------------------------------------------------
# Content Processing
# ---------------------------------------------------------------------------


def _process_content(
    content: str,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    language: Optional[str],
    model_name: str,
    messages: List[Dict[str, Any]],
    row: pd.Series,
    project_root: Path,
) -> Any:
    """Parse, validate, and return the final result from raw LLM output."""
    if output_pydantic is None and output_schema is None:
        return content

    try:
        parsed = _parse_json_response(content, output_pydantic, output_schema)
    except ValueError as exc:
        raise SchemaValidationError(f"JSON parsing failed: {exc}")

    # Unescape code fields
    if isinstance(parsed, dict):
        for key, value in parsed.items():
            if isinstance(value, str) and not _is_prose_field(key):
                parsed[key] = _smart_unescape_code(value)

    # Validate embedded Python code
    if not _validate_code_in_result(parsed, language):
        if language is None or (isinstance(language, str) and language.lower() == "python"):
            raise SchemaValidationError("Invalid Python code in structured output")

    # Pydantic validation
    if output_pydantic is not None:
        try:
            if isinstance(parsed, dict):
                return output_pydantic.model_validate(parsed)
            return parsed
        except ValidationError as exc:
            raise SchemaValidationError(f"Pydantic validation failed: {exc}")

    return parsed


# ---------------------------------------------------------------------------
# Single-Model Invocation
# ---------------------------------------------------------------------------


def _invoke_with_model(
    row: pd.Series,
    all_messages: List[Any],
    temperature: float,
    time_val: float,
    verbose: bool,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    use_batch_mode: bool,
    language: Optional[str],
    project_root: Path,
    force_temperature: Optional[float] = None,
) -> Dict[str, Any]:
    """Invoke one model candidate and process the response.

    Raises :class:`SchemaValidationError` to trigger fallback to the next candidate.
    """
    global _LAST_CALLBACK_DATA
    _LAST_CALLBACK_DATA = {}

    model_name: str = str(row["model"])
    actual_temp = force_temperature if force_temperature is not None else temperature

    reasoning_params = _build_reasoning_params(row, time_val, model_name)

    # Anthropic with thinking → temperature must be 1
    if reasoning_params.get("thinking") and force_temperature is None:
        provider_lower = str(row.get("provider", "")).lower()
        if "claude" in model_name.lower() or "anthropic" in provider_lower:
            actual_temp = 1.0

    is_gpt5 = _is_gpt5_model(model_name)

    # Flatten for non-batch
    if not use_batch_mode:
        msgs: List[Dict[str, str]] = all_messages[0] if all_messages else [{"role": "user", "content": ""}]
        if isinstance(msgs, dict):
            msgs = [msgs]
    else:
        msgs = []  # unused for batch path

    # ── Responses API (gpt-5*) ───────────────────────────────────
    if is_gpt5 and not use_batch_mode:
        api_key_name = str(row.get("api_key", "")).strip()
        api_key = (
            os.getenv(api_key_name)
            if api_key_name and api_key_name != "EXISTING_KEY"
            else None
        )

        response = _invoke_responses_api(
            model=model_name,
            messages=msgs,
            reasoning_params=reasoning_params,
            output_pydantic=output_pydantic,
            output_schema=output_schema,
            api_key=api_key,
        )

        content, thinking = _parse_responses_api_result(response)

        result = _process_content(
            content,
            output_pydantic,
            output_schema,
            language,
            model_name,
            msgs,
            row,
            project_root,
        )

        cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
        if cost == 0:
            try:
                cost = litellm.completion_cost(completion_response=response)
            except Exception:
                pass

        return {
            "result": result,
            "cost": cost,
            "model_name": model_name,
            "thinking_output": thinking,
        }

    # ── Standard completion ────────────────────────────────────
    base_msgs = msgs if not use_batch_mode else (all_messages[0] if all_messages else [])
    if isinstance(base_msgs, dict):
        base_msgs = [base_msgs]

    response_format, extra_body, processed_msgs = _build_response_format(
        output_pydantic, output_schema, model_name, row, list(base_msgs)
    )

    kwargs: Dict[str, Any] = {
        "model": model_name,
        "temperature": actual_temp,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    for k, v in reasoning_params.items():
        if not k.startswith("_"):
            kwargs[k] = v

    if response_format:
        kwargs["response_format"] = response_format
    if extra_body:
        kwargs["extra_body"] = extra_body

    # Provider-specific params
    if _is_vertex_model(row):
        kwargs.update(_build_vertex_params(row))

    if _is_lm_studio_model(row):
        kwargs.update(_get_lm_studio_params())
    else:
        api_key_name = str(row.get("api_key", "")).strip()
        if api_key_name and api_key_name not in ("", "EXISTING_KEY"):
            key_val = os.getenv(api_key_name)
            if key_val:
                kwargs["api_key"] = key_val
        base_url = str(row.get("base_url", "")).strip()
        if base_url:
            kwargs["base_url"] = base_url

    # ── Batch mode ───────────────────────────────────────
    if use_batch_mode:
        batch_messages_list: List[List[Dict[str, Any]]] = []
        for msg_set in all_messages:
            if isinstance(msg_set, dict):
                msg_set = [msg_set]
            _, _, proc = _build_response_format(
                output_pydantic, output_schema, model_name, row, list(msg_set)
            )
            batch_messages_list.append(proc)

        kwargs["messages"] = batch_messages_list
        responses = litellm.batch_completion(**kwargs)

        results: List[Any] = []
        total_cost = 0.0
        thinking_outputs: List[Optional[str]] = []

        for resp in responses:
            c = _extract_content(resp)
            t = _extract_thinking(resp)
            thinking_outputs.append(t)

            if c is None:
                c = ""
            processed = _process_content(
                c, output_pydantic, output_schema, language, model_name, [], row, project_root
            )
            results.append(processed)

            try:
                total_cost += litellm.completion_cost(completion_response=resp)
            except Exception:
                pass

        if total_cost == 0:
            total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)

        return {
            "result": results,
            "cost": total_cost,
            "model_name": model_name,
            "thinking_output": thinking_outputs if any(thinking_outputs) else None,
        }

    # ── Single completion ──────────────────
    kwargs["messages"] = processed_msgs
    saved_cache = getattr(litellm, "cache", None)

    response = litellm.completion(**kwargs)
    content = _extract_content(response)
    thinking = _extract_thinking(response)

    # Handle None content → retry with cache bypass
    if content is None:
        logger.warning("None content from %s – retrying with cache bypass", model_name)
        bypass = copy.deepcopy(processed_msgs)
        if bypass:
            bypass[-1]["content"] = bypass[-1].get("content", "") + " "
        kwargs["messages"] = bypass
        if litellm.cache:
            kwargs["cache"] = {"no-cache": True}
        response = litellm.completion(**kwargs)
        content = _extract_content(response)
        thinking = thinking or _extract_thinking(response)
        # Restore cache state
        kwargs.pop("cache", None)

    if content is None:
        content = ""

    # Detect malformed JSON (excessive trailing newlines → possible truncation)
    if (output_pydantic or output_schema) and content.count("\n\n\n") > 2:
        logger.warning("Malformed JSON detected (excessive newlines) – retrying")
        bypass = copy.deepcopy(processed_msgs)
        if bypass:
            bypass[-1]["content"] = bypass[-1].get("content", "") + "  "
        kwargs["messages"] = bypass
        if litellm.cache:
            kwargs["cache"] = {"no-cache": True}
        response = litellm.completion(**kwargs)
        retry_content = _extract_content(response)
        if retry_content:
            content = retry_content
            thinking = thinking or _extract_thinking(response)
        kwargs.pop("cache", None)

    result = _process_content(
        content, output_pydantic, output_schema, language, model_name, processed_msgs, row, project_root
    )

    cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
    if cost == 0:
        try:
            cost = litellm.completion_cost(completion_response=response)
        except Exception:
            pass

    return {
        "result": result,
        "cost": cost,
        "model_name": model_name,
        "thinking_output": thinking,
    }


# ---------------------------------------------------------------------------
# Module Initialisation
# ---------------------------------------------------------------------------


def _ensure_initialized() -> Path:
    """Perform one-time setup; return the project root."""
    global _initialized, _project_root_cache
    if _initialized and _project_root_cache is not None:
        return _project_root_cache

    project_root = _load_env()
    _project_root_cache = project_root
    _configure_logging()
    _register_callback()

    drop = os.getenv("LITELLM_DROP_PARAMS", "true").lower()
    litellm.drop_params = drop in ("true", "1", "yes")

    _init_cache(project_root)
    _load_model_csv()
    _initialized = True
    return project_root


# ---------------------------------------------------------------------------
# Public API
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
    """Invoke an LLM with automatic model selection, structured output, and retry logic.

    Returns
    -------
    dict
        ``{"result": ..., "cost": float, "model_name": str, "thinking_output": Optional[str]}``
    """
    project_root = _ensure_initialized()

    if verbose:
        set_verbose_logging(True)

    # ── Cloud execution path (before local validation) ───────────
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
                return _llm_invoke_cloud(
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
            except InsufficientCreditsError:
                raise
            except CloudFallbackError as exc:
                console.print(
                    f"[yellow]Cloud execution failed, falling back to local: {exc}[/yellow]"
                )
                logger.warning("Cloud fallback: %s", exc)
            except CloudInvocationError as exc:
                console.print(
                    f"[yellow]Cloud error, falling back to local: {exc}[/yellow]"
                )
                logger.warning("Cloud invocation error: %s", exc)

    # ── Local execution ──────────────────────────────
    df = _load_model_csv()

    # List input → batch mode
    if isinstance(input_json, list) and not use_batch_mode:
        use_batch_mode = True

    # Build message sets
    if messages is not None:
        if (
            use_batch_mode
            and isinstance(messages, list)
            and messages
            and isinstance(messages[0], list)
        ):
            all_messages: List[Any] = list(messages)
        else:
            all_messages = [messages]
    else:
        if use_batch_mode and isinstance(input_json, list):
            all_messages = [_build_messages(prompt, ij) for ij in input_json]
        else:
            all_messages = [_build_messages(prompt, input_json)]

    candidates = _select_model_candidates(strength, df, project_root)
    if not candidates:
        raise RuntimeError("No model candidates available")

    last_error: Optional[Exception] = None

    for candidate in candidates:
        model_name = str(candidate["model"])
        logger.info("Trying model: %s", model_name)

        try:
            return _invoke_with_model(
                row=candidate,
                all_messages=all_messages,
                temperature=temperature,
                time_val=time,
                verbose=verbose,
                output_pydantic=output_pydantic,
                output_schema=output_schema,
                use_batch_mode=use_batch_mode,
                language=language,
                project_root=project_root,
            )

        except SchemaValidationError as exc:
            logger.warning("Schema validation failed for %s: %s", model_name, exc)
            last_error = exc
            continue

        except litellm.AuthenticationError as exc:
            key_name = str(candidate.get("api_key", "")).strip()
            if key_name in _NEWLY_ACQUIRED_KEYS:
                logger.warning(
                    "Auth error with newly acquired key %s – re-prompting", key_name
                )
                _NEWLY_ACQUIRED_KEYS.discard(key_name)
                os.environ.pop(key_name, None)
                if _check_and_acquire_api_key(key_name, project_root):
                    try:
                        return _invoke_with_model(
                            row=candidate,
                            all_messages=all_messages,
                            temperature=temperature,
                            time_val=time,
                            verbose=verbose,
                            output_pydantic=output_pydantic,
                            output_schema=output_schema,
                            use_batch_mode=use_batch_mode,
                            language=language,
                            project_root=project_root,
                        )
                    except Exception as retry_exc:
                        last_error = retry_exc
                        if _is_wsl():
                            console.print(
                                "[yellow]WSL detected: check for carriage returns in API keys[/yellow]"
                            )
                        continue

            if _is_wsl():
                console.print(
                    "[yellow]WSL detected: check for carriage returns in API keys[/yellow]"
                )
            last_error = exc
            continue

        except Exception as exc:
            err_str = str(exc).lower()
            # Anthropic temperature + thinking auto-adjustment
            if "temperature" in err_str and "thinking" in err_str:
                logger.info(
                    "Retrying %s with temperature=1 (thinking requirement)", model_name
                )
                try:
                    return _invoke_with_model(
                        row=candidate,
                        all_messages=all_messages,
                        temperature=temperature,
                        time_val=time,
                        verbose=verbose,
                        output_pydantic=output_pydantic,
                        output_schema=output_schema,
                        use_batch_mode=use_batch_mode,
                        language=language,
                        project_root=project_root,
                        force_temperature=1.0,
                    )
                except Exception as retry_exc:
                    last_error = retry_exc
                    continue

            logger.warning("Error with model %s: %s", model_name, exc)
            last_error = exc
            continue

    raise RuntimeError(f"All model candidates exhausted. Last error: {last_error}")