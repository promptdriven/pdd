from __future__ import annotations

import ast
import json
import logging
import os
import re
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union

import litellm
import pandas as pd
from pydantic import BaseModel
from rich.console import Console

from .path_resolution import get_default_resolver

# ─── Module-Level State ───────────────────────────────────────────────────────

LLM_CALL_TIMEOUT: int = 120
CLOUD_CALL_TIMEOUT: int = 300

console: Console = Console()

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_NEWLY_ACQUIRED_KEYS: set[str] = set()

_PROSE_FIELD_NAMES: frozenset[str] = frozenset({
    "reasoning", "explanation", "analysis", "description", "summary",
    "rationale", "thought", "thinking", "justification", "notes",
    "comment", "comments", "review", "feedback", "observation",
    "observations", "insight", "insights",
})

# ─── Logging ──────────────────────────────────────────────────────────────────

logger: logging.Logger = logging.getLogger("pdd.llm_invoke")
litellm_logger: logging.Logger = logging.getLogger("litellm")


def _configure_logging() -> None:
    """Configure logging from environment variables."""
    env = os.getenv("PDD_ENVIRONMENT", "").lower()
    verbose = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"

    pdd_level_str = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    litellm_level_str = os.getenv(
        "LITELLM_LOG_LEVEL",
        "WARNING" if env == "production" else "WARNING",
    ).upper()

    if verbose:
        pdd_level_str = "DEBUG"
        litellm_level_str = "DEBUG"
    elif env == "production" and pdd_level_str == "INFO":
        pdd_level_str = "WARNING"

    logger.setLevel(getattr(logging, pdd_level_str, logging.INFO))
    litellm_logger.setLevel(getattr(logging, litellm_level_str, logging.WARNING))

    if not logger.handlers:
        handler = logging.StreamHandler()
        handler.setFormatter(logging.Formatter("%(name)s - %(levelname)s - %(message)s"))
        logger.addHandler(handler)


def setup_file_logging(log_dir: Optional[Path] = None) -> None:
    """Set up rotating file handlers (10 MB, 5 backups)."""
    if log_dir is None:
        log_dir = Path.cwd() / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "pdd_llm_invoke.log",
        maxBytes=10 * 1024 * 1024,
        backupCount=5,
    )
    handler.setFormatter(
        logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s"),
    )
    logger.addHandler(handler)


def set_verbose_logging(enabled: bool = True) -> None:
    """Toggle DEBUG level on both loggers."""
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    litellm_logger.setLevel(level)


# ─── Exceptions ───────────────────────────────────────────────────────────────


class SchemaValidationError(Exception):
    """Structured output failed schema validation; triggers model fallback."""


class CloudFallbackError(Exception):
    """Recoverable cloud error; triggers fallback to local execution."""


class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""


class InsufficientCreditsError(Exception):
    """402 Payment Required – does NOT fall back to local."""


# ─── Startup Helpers ──────────────────────────────────────────────────────────


def _resolve_project_root() -> Path:
    try:
        resolver = get_default_resolver()
        return Path(resolver.resolve_project_root())
    except Exception:
        return Path.cwd()


def _load_env(project_root: Path) -> None:
    env_file = project_root / ".env"
    if env_file.exists():
        from dotenv import load_dotenv

        load_dotenv(env_file, override=False)


def _resolve_model_csv(project_root: Path) -> Path:
    """Resolve llm_model.csv in priority order."""
    # (a) ~/.pdd/llm_model.csv
    home_csv = Path.home() / ".pdd" / "llm_model.csv"
    if home_csv.exists():
        return home_csv

    # (b) <PROJECT_ROOT>/.pdd/llm_model.csv when PDD_PATH is a real project
    pdd_path = os.getenv("PDD_PATH")
    if pdd_path:
        candidate = Path(pdd_path) / ".pdd" / "llm_model.csv"
        if candidate.exists():
            try:
                import pdd as _pdd_pkg

                pkg_dir = Path(_pdd_pkg.__file__).parent
                if not str(candidate).startswith(str(pkg_dir)):
                    return candidate
            except Exception:
                return candidate

    # (c) <cwd>/.pdd/llm_model.csv
    cwd_csv = Path.cwd() / ".pdd" / "llm_model.csv"
    if cwd_csv.exists():
        return cwd_csv

    # (d) packaged pdd/data/llm_model.csv
    try:
        resolver = get_default_resolver()
        data_csv = Path(resolver.resolve_data_file("data/llm_model.csv"))
        if data_csv.exists():
            return data_csv
    except Exception:
        pass

    try:
        import pdd as _pdd_pkg

        pkg_csv = Path(_pdd_pkg.__file__).parent / "data" / "llm_model.csv"
        if pkg_csv.exists():
            return pkg_csv
    except Exception:
        pass

    raise FileNotFoundError("Cannot find llm_model.csv in any expected location")


# ─── CSV / Rate Map ──────────────────────────────────────────────────────────


def _load_model_csv(csv_path: Path) -> pd.DataFrame:
    df = pd.read_csv(csv_path)

    required = {"model", "provider", "input", "output", "api_key"}
    missing = required - set(df.columns)
    if missing:
        raise ValueError(f"Model CSV missing columns: {missing}")

    defaults: Dict[str, Any] = {
        "coding_arena_elo": 0,
        "structured_output": False,
        "reasoning_type": "none",
        "max_reasoning_tokens": 0,
        "location": "",
        "base_url": "",
    }
    for col, default in defaults.items():
        if col not in df.columns:
            df[col] = default

    df["coding_arena_elo"] = pd.to_numeric(df["coding_arena_elo"], errors="coerce").fillna(0)
    df["input"] = pd.to_numeric(df["input"], errors="coerce").fillna(0)
    df["output"] = pd.to_numeric(df["output"], errors="coerce").fillna(0)
    df["max_reasoning_tokens"] = (
        pd.to_numeric(df["max_reasoning_tokens"], errors="coerce").fillna(0).astype(int)
    )
    df["structured_output"] = df["structured_output"].astype(str).str.lower().isin(
        ["true", "1", "yes"],
    )
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
    df["location"] = df["location"].fillna("").astype(str)
    df["base_url"] = df["base_url"].fillna("").astype(str)
    df["api_key"] = df["api_key"].fillna("").astype(str)
    return df


def _build_rate_map(df: pd.DataFrame) -> Dict[str, Dict[str, float]]:
    return {
        str(row["model"]): {"input": float(row["input"]), "output": float(row["output"])}
        for _, row in df.iterrows()
    }


# ─── WSL Diagnostics ─────────────────────────────────────────────────────────


def _is_wsl() -> bool:
    if os.getenv("WSL_DISTRO_NAME"):
        return True
    try:
        with open("/proc/version") as fh:
            txt = fh.read().lower()
            return "microsoft" in txt or "wsl" in txt
    except (OSError, FileNotFoundError):
        return False


def _sanitize_api_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "").replace("\t", "")


# ─── API Key Management ──────────────────────────────────────────────────────


def _save_key_to_env(env_file: Path, key_name: str, key_value: str) -> None:
    lines: List[str] = []
    if env_file.exists():
        with open(env_file) as fh:
            lines = fh.readlines()

    pattern = re.compile(rf"^#?\s*{re.escape(key_name)}\s*=")
    new_lines = [ln for ln in lines if not pattern.match(ln)]
    new_lines.append(f"{key_name}={key_value}\n")

    with open(env_file, "w") as fh:
        fh.writelines(new_lines)


def _check_api_key(key_name: str, project_root: Path) -> bool:
    """Return True if API key is available; prompt interactively when possible."""
    if not key_name or key_name == "EXISTING_KEY":
        return True

    existing = os.getenv(key_name)
    if existing and existing.strip():
        return True

    if os.getenv("PDD_FORCE"):
        logger.debug("Skipping model requiring %s (PDD_FORCE set)", key_name)
        return False

    console.print(f"\n[yellow]API key '{key_name}' not found in environment.[/yellow]")
    try:
        raw = input(f"Enter value for {key_name} (or press Enter to skip): ")
    except (EOFError, KeyboardInterrupt):
        return False
    if not raw.strip():
        return False

    value = _sanitize_api_key(raw)
    os.environ[key_name] = value

    env_file = project_root / ".env"
    _save_key_to_env(env_file, key_name, value)
    console.print(f"[yellow]⚠ Security warning: {key_name} saved to {env_file}[/yellow]")
    logger.warning("API key %s saved to .env file at %s", key_name, env_file)
    _NEWLY_ACQUIRED_KEYS.add(key_name)
    return True


# ─── Model Selection ─────────────────────────────────────────────────────────


def _filter_available_models(df: pd.DataFrame, project_root: Path) -> pd.DataFrame:
    keep: List[int] = []
    for idx, row in df.iterrows():
        kn = row["api_key"]
        if not kn or kn == "EXISTING_KEY" or os.getenv(kn) or _check_api_key(kn, project_root):
            keep.append(int(idx))
    return df.loc[keep].reset_index(drop=True)


def _select_model(
    df: pd.DataFrame,
    strength: float,
    base_model_name: Optional[str] = None,
) -> pd.DataFrame:
    """Return candidate models ordered by preference for *strength*."""
    if df.empty:
        raise RuntimeError("No models available with valid API keys")

    base_idx: int = 0
    if base_model_name:
        matches = df.index[df["model"] == base_model_name].tolist()
        if matches:
            base_idx = matches[0]

    if abs(strength - 0.5) < 1e-9:
        order = [base_idx] + [
            i
            for i in df.sort_values("coding_arena_elo", ascending=False).index
            if i != base_idx
        ]
        return df.loc[order].reset_index(drop=True)

    if strength < 0.5:
        base_cost = float(df.loc[base_idx, "input"]) + float(df.loc[base_idx, "output"])
        df2 = df.copy()
        df2["_tc"] = df2["input"].astype(float) + df2["output"].astype(float)
        cheapest = float(df2["_tc"].min())
        t = strength / 0.5
        target = cheapest + t * (base_cost - cheapest)
        df2["_dist"] = (df2["_tc"] - target).abs()
        return df2.sort_values("_dist").drop(columns=["_tc", "_dist"]).reset_index(drop=True)

    # strength > 0.5
    base_elo = float(df.loc[base_idx, "coding_arena_elo"])
    max_elo = float(df["coding_arena_elo"].max())
    t = (strength - 0.5) / 0.5
    target = base_elo + t * (max_elo - base_elo)
    df2 = df.copy()
    df2["_dist"] = (df2["coding_arena_elo"].astype(float) - target).abs()
    return df2.sort_values("_dist").drop(columns=["_dist"]).reset_index(drop=True)


# ─── Vertex AI ────────────────────────────────────────────────────────────────


def _is_vertex_model(row: pd.Series) -> bool:
    m = str(row.get("model", ""))
    p = str(row.get("provider", "")).lower()
    return m.startswith("vertex_ai/") or p in ("google", "vertex_ai")


def _get_vertex_credentials() -> Optional[str]:
    cred_path = os.getenv("VERTEX_CREDENTIALS")
    if not cred_path:
        return None
    p = Path(cred_path)
    if p.exists() and p.suffix == ".json":
        return p.read_text()
    return cred_path


def _build_vertex_params(row: pd.Series) -> Dict[str, Any]:
    params: Dict[str, Any] = {}
    creds = _get_vertex_credentials()
    if creds:
        params["vertex_credentials"] = creds
    proj = os.getenv("VERTEX_PROJECT")
    if proj:
        params["vertex_project"] = proj
    loc = str(row.get("location", "")).strip() or os.getenv("VERTEX_LOCATION", "us-central1")
    params["vertex_location"] = loc
    return params


# ─── LiteLLM Caching ─────────────────────────────────────────────────────────


_cache_initialized: bool = False


def _setup_cache(project_root: Path) -> None:
    global _cache_initialized
    if _cache_initialized:
        return
    _cache_initialized = True

    if os.getenv("LITELLM_CACHE_DISABLE", "0") == "1":
        logger.debug("LiteLLM caching disabled")
        return

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
            logger.debug("LiteLLM cache: GCS S3-compatible backend")
            return
        except Exception as exc:
            logger.warning("GCS cache setup failed, falling back to disk: %s", exc)

    try:
        litellm.cache = litellm.Cache(
            type="disk",
            disk_cache_dir=str(project_root),
        )
        logger.debug("LiteLLM cache: disk backend at %s", project_root)
    except Exception as exc:
        logger.warning("Disk cache setup failed: %s", exc)


# ─── LiteLLM Callback ────────────────────────────────────────────────────────


def _litellm_success_callback(
    kwargs: Dict[str, Any],
    completion_response: Any,
    start_time: Any,
    end_time: Any,
) -> None:
    global _LAST_CALLBACK_DATA
    usage: Dict[str, int] = {}
    finish_reason: Optional[str] = None

    try:
        if hasattr(completion_response, "usage") and completion_response.usage:
            u = completion_response.usage
            usage = {
                "prompt_tokens": getattr(u, "prompt_tokens", 0) or 0,
                "completion_tokens": getattr(u, "completion_tokens", 0) or 0,
                "total_tokens": getattr(u, "total_tokens", 0) or 0,
            }
        if hasattr(completion_response, "choices") and completion_response.choices:
            finish_reason = getattr(completion_response.choices[0], "finish_reason", None)

        cost = 0.0
        try:
            cost = litellm.completion_cost(completion_response=completion_response)
        except Exception:
            model = kwargs.get("model", "")
            if model in _MODEL_RATE_MAP:
                r = _MODEL_RATE_MAP[model]
                cost = (
                    usage.get("prompt_tokens", 0) * r["input"] / 1_000_000
                    + usage.get("completion_tokens", 0) * r["output"] / 1_000_000
                )
        _LAST_CALLBACK_DATA = {"usage": usage, "finish_reason": finish_reason, "cost": cost}
    except Exception as exc:
        logger.debug("Callback error: %s", exc)
        _LAST_CALLBACK_DATA = {"usage": usage, "finish_reason": finish_reason, "cost": 0.0}


def _register_callback() -> None:
    if _litellm_success_callback not in litellm.success_callback:
        litellm.success_callback.append(_litellm_success_callback)


# ─── Structured-Output Helpers ────────────────────────────────────────────────


def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively mark every property as required."""
    if not isinstance(schema, dict):
        return schema
    schema = dict(schema)

    if "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        schema["properties"] = {
            k: _ensure_all_properties_required(v) for k, v in schema["properties"].items()
        }

    if "items" in schema and isinstance(schema["items"], dict):
        schema["items"] = _ensure_all_properties_required(schema["items"])

    for kw in ("anyOf", "oneOf", "allOf"):
        if kw in schema and isinstance(schema[kw], list):
            schema[kw] = [_ensure_all_properties_required(s) for s in schema[kw]]

    for defs_key in ("$defs", "definitions"):
        if defs_key in schema and isinstance(schema[defs_key], dict):
            schema[defs_key] = {
                k: _ensure_all_properties_required(v)
                for k, v in schema[defs_key].items()
            }
    return schema


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively add ``additionalProperties: false`` on all object schemas."""
    if not isinstance(schema, dict):
        return schema
    schema = dict(schema)

    if schema.get("type") == "object" or "properties" in schema:
        schema["additionalProperties"] = False

    if "properties" in schema:
        schema["properties"] = {
            k: _add_additional_properties_false(v) for k, v in schema["properties"].items()
        }
    if "items" in schema and isinstance(schema["items"], dict):
        schema["items"] = _add_additional_properties_false(schema["items"])

    for kw in ("anyOf", "oneOf", "allOf"):
        if kw in schema and isinstance(schema[kw], list):
            schema[kw] = [_add_additional_properties_false(s) for s in schema[kw]]

    for defs_key in ("$defs", "definitions"):
        if defs_key in schema and isinstance(schema[defs_key], dict):
            schema[defs_key] = {
                k: _add_additional_properties_false(v)
                for k, v in schema[defs_key].items()
            }
    return schema


def _prepare_json_schema(
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
) -> tuple[str, Dict[str, Any]]:
    """Return (schema_name, strict-ready schema dict)."""
    if output_pydantic is not None:
        raw = output_pydantic.model_json_schema()
    else:
        raw = dict(output_schema)  # type: ignore[arg-type]
    raw = _ensure_all_properties_required(raw)
    raw = _add_additional_properties_false(raw)
    name = raw.pop("title", "response_schema")
    return name, raw


def _build_response_format(
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    model_row: pd.Series,
) -> Optional[Dict[str, Any]]:
    if output_pydantic is None and output_schema is None:
        return None
    if not bool(model_row.get("structured_output", False)):
        return None

    name, schema = _prepare_json_schema(output_pydantic, output_schema)
    model_name = str(model_row.get("model", ""))
    provider = str(model_row.get("provider", "")).lower()

    if "groq" in model_name.lower() or provider == "groq":
        return {"type": "json_object"}

    return {
        "type": "json_schema",
        "json_schema": {"name": name, "schema": schema, "strict": True},
    }


# ─── Reasoning Parameters ────────────────────────────────────────────────────


def _build_reasoning_params(model_row: pd.Series, time_param: float) -> Dict[str, Any]:
    rtype = str(model_row.get("reasoning_type", "none")).lower()
    max_tok = int(model_row.get("max_reasoning_tokens", 0))
    model_name = str(model_row.get("model", ""))
    params: Dict[str, Any] = {}

    if rtype == "budget" and max_tok > 0:
        budget = int(time_param * max_tok)
        if budget > 0:
            if "claude" in model_name.lower() or "anthropic" in model_name.lower():
                params["thinking"] = {"type": "enabled", "budget_tokens": budget}
            else:
                params["budget_tokens"] = budget

    elif rtype == "effort":
        if time_param <= 0.33:
            effort = "low"
        elif time_param <= 0.66:
            effort = "medium"
        else:
            effort = "high"

        if model_name.startswith("gpt-5") or model_name.startswith("openai/gpt-5"):
            params["reasoning"] = {"effort": effort, "summary": "auto"}
        else:
            params["reasoning_effort"] = effort

    return params


# ─── Response Processing ─────────────────────────────────────────────────────


def _extract_json_from_response(text: str) -> Optional[str]:
    """Extract JSON: fenced blocks → balanced extraction → fence cleaning."""
    if not text:
        return None
    text = text.strip()

    # Fenced ```json blocks
    m = re.search(r"```(?:json)?\s*\n?(.*?)\n?\s*```", text, re.DOTALL)
    if m:
        return m.group(1).strip()

    # Balanced extraction
    for sc, ec in (("{", "}"), ("[", "]")):
        si = text.find(sc)
        if si == -1:
            continue
        depth = 0
        in_str = False
        esc = False
        for i in range(si, len(text)):
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
            if in_str:
                continue
            if c == sc:
                depth += 1
            elif c == ec:
                depth -= 1
                if depth == 0:
                    return text[si : i + 1]

    # Fence cleaning
    cleaned = text.strip("`").strip()
    if cleaned.startswith("json"):
        cleaned = cleaned[4:].strip()
    return cleaned


def _repair_truncated_json(text: str) -> Optional[str]:
    for suffix in ('}"', "}", '"}', '"}]', '"}}', '"}}}', "]", "]}", '"]}', '"}]}'):
        candidate = text + suffix
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            continue
    return None


def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines while preserving ``\\n`` inside string literals."""
    result: List[str] = []
    i = 0
    in_sq = False
    in_dq = False
    in_tsq = False
    in_tdq = False
    length = len(text)

    while i < length:
        # Triple-quote detection
        if i + 2 < length:
            tri = text[i : i + 3]
            if tri == '"""' and not in_sq and not in_tsq:
                in_tdq = not in_tdq
                result.append(tri)
                i += 3
                continue
            if tri == "'''" and not in_dq and not in_tdq:
                in_tsq = not in_tsq
                result.append(tri)
                i += 3
                continue

        in_string = in_sq or in_dq or in_tsq or in_tdq
        c = text[i]

        if not in_string:
            if c == '"':
                in_dq = True
                result.append(c)
                i += 1
            elif c == "'":
                in_sq = True
                result.append(c)
                i += 1
            elif c == "\\" and i + 1 < length and text[i + 1] == "n":
                result.append("\n")
                i += 2
            else:
                result.append(c)
                i += 1
        else:
            if c == "\\":
                result.append(c)
                i += 1
                if i < length:
                    result.append(text[i])
                    i += 1
            elif c == '"' and in_dq and not in_tdq:
                in_dq = False
                result.append(c)
                i += 1
            elif c == "'" and in_sq and not in_tsq:
                in_sq = False
                result.append(c)
                i += 1
            else:
                result.append(c)
                i += 1

    return "".join(result)


def _repair_python_syntax(code: str) -> str:
    lines = code.rstrip().split("\n")
    while lines and lines[-1].strip() in ("'", '"', "'''", '"""'):
        lines.pop()
    return "\n".join(lines)


def _is_valid_python(code: str) -> bool:
    try:
        ast.parse(code)
        return True
    except SyntaxError:
        return False


def _extract_thinking_output(response: Any) -> Optional[str]:
    try:
        hidden = getattr(response, "_hidden_params", None)
        if hidden and isinstance(hidden, dict) and "thinking" in hidden:
            return hidden["thinking"]
    except Exception:
        pass
    try:
        if hasattr(response, "choices") and response.choices:
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
    model_row: pd.Series,
    language: Optional[str],
) -> Dict[str, Any]:
    content: Optional[str] = None
    if hasattr(response, "choices") and response.choices:
        content = response.choices[0].message.content
    thinking = _extract_thinking_output(response)

    if content is None:
        raise ValueError("Response content is None")

    result: Any = content

    if output_pydantic is not None or output_schema is not None:
        json_str = _extract_json_from_response(content)
        if json_str is None:
            raise SchemaValidationError(
                f"Could not extract JSON from response: {content[:200]}",
            )
        try:
            parsed = json.loads(json_str)
        except json.JSONDecodeError:
            repaired = _repair_truncated_json(json_str)
            if repaired:
                try:
                    parsed = json.loads(repaired)
                except json.JSONDecodeError:
                    raise SchemaValidationError(
                        f"Could not parse JSON: {json_str[:200]}",
                    )
            else:
                raise SchemaValidationError(f"Could not parse JSON: {json_str[:200]}")

        if output_pydantic is not None:
            try:
                result = output_pydantic.model_validate(parsed)
            except Exception as exc:
                raise SchemaValidationError(f"Pydantic validation failed: {exc}")
        else:
            result = parsed
    else:
        if "\\n" in result:
            result = _smart_unescape_code(result)

        if language in ("python", None):
            stripped = result.strip()
            is_prose = any(stripped.lower().startswith(p) for p in _PROSE_FIELD_NAMES)
            code_like = "def " in stripped or "class " in stripped or "import " in stripped
            if code_like and not is_prose and not _is_valid_python(stripped):
                repaired = _repair_python_syntax(stripped)
                if _is_valid_python(repaired):
                    result = repaired

    return {"result": result, "thinking_output": thinking}


def _process_responses_api_response(
    response: Any,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
) -> Dict[str, Any]:
    content: Optional[str] = None
    thinking: Optional[str] = None

    if hasattr(response, "output"):
        for item in response.output:
            item_type = getattr(item, "type", None)
            if item_type == "message":
                for part in getattr(item, "content", []):
                    if hasattr(part, "text"):
                        content = part.text
            elif item_type == "reasoning":
                parts: List[str] = []
                for part in getattr(item, "summary", []):
                    if hasattr(part, "text"):
                        parts.append(part.text)
                if parts:
                    thinking = "\n".join(parts)

    if content is None and hasattr(response, "output_text"):
        content = response.output_text

    if content is None:
        raise ValueError("Could not extract content from Responses API response")

    result: Any = content
    if output_pydantic is not None or output_schema is not None:
        json_str = _extract_json_from_response(content)
        if json_str is None:
            raise SchemaValidationError("Could not extract JSON from Responses API response")
        try:
            parsed = json.loads(json_str)
        except json.JSONDecodeError:
            repaired = _repair_truncated_json(json_str)
            if repaired:
                parsed = json.loads(repaired)
            else:
                raise SchemaValidationError("Could not parse JSON from Responses API response")
        if output_pydantic is not None:
            try:
                result = output_pydantic.model_validate(parsed)
            except Exception as exc:
                raise SchemaValidationError(f"Pydantic validation failed: {exc}")
        else:
            result = parsed

    return {"result": result, "thinking_output": thinking}


# ─── Cloud Execution ──────────────────────────────────────────────────────────


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    schema = _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> Any:
    if isinstance(result, str):
        try:
            result = json.loads(result)
        except json.JSONDecodeError:
            js = _extract_json_from_response(result)
            if js:
                result = json.loads(js)
            else:
                raise SchemaValidationError("Could not parse cloud result as JSON")
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    return result


def _llm_invoke_cloud(
    *,
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]],
    strength: float,
    temperature: float,
    time_param: float,
    verbose: bool,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    try:
        from .cloud_config import CloudConfig
    except ImportError:
        raise CloudFallbackError("Cloud config module not available")

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
    if language is not None:
        payload["language"] = language

    if output_pydantic is not None:
        payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema is not None:
        payload["outputSchema"] = output_schema

    try:
        cloud_resp = CloudConfig.call_function("llmInvoke", payload, timeout=CLOUD_CALL_TIMEOUT)
    except Exception as exc:
        err = str(exc).lower()
        if "402" in err or "payment required" in err or "insufficient credits" in str(exc):
            raise InsufficientCreditsError(str(exc))
        recoverable = ("timeout", "network", "connection", "500", "502", "503", "504",
                       "401", "403", "unauthorized", "forbidden")
        if any(ind in err for ind in recoverable):
            if any(a in err for a in ("401", "403", "unauthorized", "forbidden")):
                try:
                    CloudConfig.clear_jwt_cache()
                except Exception:
                    pass
            raise CloudFallbackError(str(exc))
        raise CloudInvocationError(str(exc))

    data = cloud_resp if isinstance(cloud_resp, dict) else {}
    return {
        "result": data.get("result"),
        "cost": data.get("totalCost", 0.0),
        "model_name": data.get("modelName", "cloud"),
        "thinking_output": data.get("thinkingOutput"),
    }


# ─── Message Building ────────────────────────────────────────────────────────


def _build_messages(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
) -> List[Dict[str, str]]:
    if prompt is None:
        return [{"role": "user", "content": ""}]

    content = prompt
    if input_json is not None and isinstance(input_json, dict):
        try:
            content = prompt.format(**input_json)
        except (KeyError, IndexError, ValueError) as exc:
            logger.warning("Prompt formatting failed: %s", exc)
            content = f"{prompt}\n\nInput:\n{json.dumps(input_json, indent=2)}"

    return [{"role": "user", "content": content}]


def _is_lm_studio(model_name: str, provider: str) -> bool:
    return (
        "lm_studio" in model_name.lower()
        or "lm-studio" in model_name.lower()
        or provider.lower() == "lm studio"
    )


def _bypass_cache(
    msgs: Union[List[Dict[str, str]], List[List[Dict[str, str]]]],
) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    """Return a shallow copy with a trailing space appended to the last user message."""
    if not msgs:
        return msgs
    if isinstance(msgs[0], dict):
        out = list(msgs)
        last = dict(out[-1])
        last["content"] = last.get("content", "") + " "
        out[-1] = last
        return out
    # Batch: modify the first sub-list
    out = list(msgs)
    first = list(out[0])
    last = dict(first[-1])
    last["content"] = last.get("content", "") + " "
    first[-1] = last
    out[0] = first
    return out


# ─── Cost Helper for Responses API ───────────────────────────────────────────


def _compute_cost_responses(response: Any, model_name: str) -> float:
    try:
        return litellm.completion_cost(completion_response=response)
    except Exception:
        pass
    if model_name in _MODEL_RATE_MAP:
        rates = _MODEL_RATE_MAP[model_name]
        usage = getattr(response, "usage", None)
        if usage:
            pt = getattr(usage, "input_tokens", 0) or getattr(usage, "prompt_tokens", 0) or 0
            ct = getattr(usage, "output_tokens", 0) or getattr(usage, "completion_tokens", 0) or 0
            return pt * rates["input"] / 1_000_000 + ct * rates["output"] / 1_000_000
    return 0.0


# ─── Main ─────────────────────────────────────────────────────────────────────


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
    """Invoke an LLM with the given prompt and parameters.

    Returns
    -------
    Dict with keys ``result``, ``cost``, ``model_name``, ``thinking_output``.
    """
    global _LAST_CALLBACK_DATA, _MODEL_RATE_MAP

    # ── Initialisation ────────────────────────────────────────────────────
    _configure_logging()
    if verbose:
        set_verbose_logging(True)

    project_root = _resolve_project_root()
    _load_env(project_root)

    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() in (
        "true", "1", "yes",
    )
    _register_callback()
    _setup_cache(project_root)

    # ── Cloud path ────────────────────────────────────────────────────────
    if use_cloud is not False:
        should_cloud = False
        if use_cloud is True:
            should_cloud = True
        elif use_cloud is None:
            if os.getenv("PDD_FORCE_LOCAL", "0") != "1":
                try:
                    from .cloud_config import CloudConfig

                    should_cloud = CloudConfig.is_cloud_enabled()
                except Exception:
                    pass

        if should_cloud:
            try:
                cloud_result = _llm_invoke_cloud(
                    prompt=prompt,
                    input_json=input_json,
                    messages=messages,
                    strength=strength,
                    temperature=temperature,
                    time_param=time,
                    verbose=verbose,
                    output_pydantic=output_pydantic,
                    output_schema=output_schema,
                    use_batch_mode=use_batch_mode,
                    language=language,
                )
                if output_pydantic is not None and cloud_result.get("result") is not None:
                    cloud_result["result"] = _validate_with_pydantic(
                        cloud_result["result"], output_pydantic,
                    )
                return cloud_result
            except InsufficientCreditsError:
                raise
            except CloudFallbackError as exc:
                console.print(
                    f"[yellow]Cloud execution failed, falling back to local: {exc}[/yellow]",
                )
                logger.warning("Cloud fallback: %s", exc)
            except CloudInvocationError as exc:
                console.print(
                    f"[yellow]Cloud invocation error, falling back to local: {exc}[/yellow]",
                )
                logger.warning("Cloud invocation error: %s", exc)

    # ── Load models ───────────────────────────────────────────────────────
    try:
        csv_path = _resolve_model_csv(project_root)
        df = _load_model_csv(csv_path)
    except FileNotFoundError as exc:
        raise RuntimeError(f"Cannot find model CSV: {exc}") from exc

    _MODEL_RATE_MAP = _build_rate_map(df)
    available = _filter_available_models(df, project_root)
    if available.empty:
        raise RuntimeError("No models available with valid API keys")

    base_model = os.getenv("PDD_MODEL_DEFAULT")
    candidates = _select_model(available, strength, base_model)

    # ── Build messages ────────────────────────────────────────────────────
    is_batch = use_batch_mode or (isinstance(input_json, list) and messages is None)
    if messages is not None:
        all_messages: Any = messages
    elif is_batch and isinstance(input_json, list):
        all_messages = [_build_messages(prompt, item) for item in input_json]
    else:
        all_messages = _build_messages(prompt, input_json)

    # Keep a pristine copy for cache-bypass restores
    original_messages = all_messages

    # ── Iterate candidates ────────────────────────────────────────────────
    last_error: Optional[Exception] = None

    for ci in range(len(candidates)):
        model_row = candidates.iloc[ci]
        model_name = str(model_row["model"])
        provider = str(model_row.get("provider", ""))
        api_key_name = str(model_row.get("api_key", "")).strip()

        logger.info("Attempting model: %s", model_name)

        # -- base call params --
        reasoning_params = _build_reasoning_params(model_row, time)
        is_anthropic_thinking = "thinking" in reasoning_params
        is_responses = model_name.startswith("gpt-5") or model_name.startswith("openai/gpt-5")

        call_params: Dict[str, Any] = {
            "model": model_name,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        if is_anthropic_thinking:
            call_params["temperature"] = 1
        elif not is_responses:
            call_params["temperature"] = temperature

        call_params.update(reasoning_params)

        # Vertex AI
        if _is_vertex_model(model_row):
            call_params.update(_build_vertex_params(model_row))

        # LM Studio
        if _is_lm_studio(model_name, provider):
            call_params["base_url"] = os.getenv(
                "LM_STUDIO_API_BASE", "http://localhost:1234/v1",
            )
            call_params["api_key"] = "lm-studio"

        # CSV base_url
        csv_base = str(model_row.get("base_url", "")).strip()
        if csv_base and "base_url" not in call_params:
            call_params["base_url"] = csv_base

        # API key
        if (
            api_key_name
            and api_key_name != "EXISTING_KEY"
            and "api_key" not in call_params
            and not _is_vertex_model(model_row)
        ):
            env_key = os.getenv(api_key_name)
            if env_key:
                call_params["api_key"] = env_key

        # -- structured output --
        resp_fmt = _build_response_format(output_pydantic, output_schema, model_row)
        needs_manual_parse = (
            (output_pydantic is not None or output_schema is not None)
            and resp_fmt is None
        )

        # Groq: inject schema into system prompt
        working_msgs: Any = all_messages
        if resp_fmt and resp_fmt.get("type") == "json_object" and (
            output_pydantic or output_schema
        ):
            raw_schema = (
                output_pydantic.model_json_schema() if output_pydantic else output_schema
            )
            instr = f"\nRespond with valid JSON matching this schema:\n{json.dumps(raw_schema, indent=2)}"
            if isinstance(working_msgs, list) and working_msgs and isinstance(working_msgs[0], dict):
                working_msgs = list(working_msgs)
                if working_msgs[0].get("role") == "system":
                    working_msgs[0] = dict(working_msgs[0])
                    working_msgs[0]["content"] += instr
                else:
                    working_msgs = [{"role": "system", "content": instr.strip()}] + working_msgs

        # Manual-parse models: add schema instruction to user prompt
        if needs_manual_parse:
            raw_schema = (
                output_pydantic.model_json_schema() if output_pydantic else output_schema
            )
            instr = (
                "\n\nYou MUST respond with valid JSON only, matching this schema:\n"
                f"{json.dumps(raw_schema, indent=2)}"
            )
            if isinstance(working_msgs, list) and working_msgs and isinstance(working_msgs[0], dict):
                working_msgs = list(working_msgs)
                last = dict(working_msgs[-1])
                last["content"] = last.get("content", "") + instr
                working_msgs[-1] = last

        if resp_fmt is not None:
            if _is_lm_studio(model_name, provider):
                call_params["extra_body"] = {"response_format": resp_fmt}
            else:
                call_params["response_format"] = resp_fmt

        _LAST_CALLBACK_DATA = {}
        max_retries = 2

        for retry in range(max_retries + 1):
            try:
                # ── Responses API ──
                if is_responses:
                    resp_params: Dict[str, Any] = {
                        "model": model_name,
                        "input": working_msgs,
                    }
                    if "reasoning" in call_params:
                        resp_params["reasoning"] = call_params["reasoning"]

                    if resp_fmt and resp_fmt.get("type") == "json_schema":
                        resp_params["text"] = {"format": resp_fmt}
                    else:
                        resp_params["text"] = {"format": {"type": "text"}}

                    for passthrough in ("api_key", "base_url"):
                        if passthrough in call_params:
                            resp_params[passthrough] = call_params[passthrough]

                    response = litellm.responses(
                        **resp_params, timeout=LLM_CALL_TIMEOUT, num_retries=2,
                    )
                    processed = _process_responses_api_response(
                        response, output_pydantic, output_schema,
                    )
                    cost = _compute_cost_responses(response, model_name)

                # ── Batch completion ──
                elif is_batch and isinstance(working_msgs, list) and working_msgs and isinstance(working_msgs[0], list):
                    call_params["messages"] = working_msgs
                    response = litellm.batch_completion(**call_params)
                    batch_results: List[Any] = []
                    for sub_resp in response:
                        try:
                            proc = _process_response(
                                sub_resp, output_pydantic, output_schema, model_row, language,
                            )
                            batch_results.append(proc["result"])
                        except Exception as sub_exc:
                            batch_results.append(f"Error: {sub_exc}")
                    processed = {"result": batch_results, "thinking_output": None}
                    cost = _LAST_CALLBACK_DATA.get("cost", 0.0)

                # ── Standard completion ──
                else:
                    call_params["messages"] = working_msgs
                    response = litellm.completion(**call_params)
                    processed = _process_response(
                        response, output_pydantic, output_schema, model_row, language,
                    )
                    cost = _LAST_CALLBACK_DATA.get("cost", 0.0)

                # ── Post-processing checks ──
                if processed["result"] is None:
                    if retry < max_retries:
                        logger.warning("Response content is None, retrying with cache bypass")
                        working_msgs = _bypass_cache(working_msgs)
                        continue
                    raise ValueError("Response content is None after retries")

                # Malformed JSON with excessive trailing newlines
                if (
                    isinstance(processed["result"], str)
                    and (output_pydantic or output_schema)
                    and processed["result"].endswith("\n\n\n")
                ):
                    if retry < max_retries:
                        logger.warning("Malformed JSON (trailing newlines), retrying")
                        working_msgs = _bypass_cache(working_msgs)
                        continue

                # Invalid Python code → retry
                if (
                    language in ("python", None)
                    and isinstance(processed["result"], str)
                    and output_pydantic is None
                    and output_schema is None
                ):
                    code = processed["result"].strip()
                    code_like = "def " in code or "class " in code or "import " in code
                    is_prose = any(code.lower().startswith(p) for p in _PROSE_FIELD_NAMES)
                    if code_like and not is_prose and not _is_valid_python(code):
                        repaired = _repair_python_syntax(code)
                        if _is_valid_python(repaired):
                            processed["result"] = repaired
                        elif retry < max_retries:
                            logger.warning("Invalid Python syntax, retrying")
                            working_msgs = _bypass_cache(working_msgs)
                            continue

                # ── Success ──
                return {
                    "result": processed["result"],
                    "cost": cost,
                    "model_name": model_name,
                    "thinking_output": processed.get("thinking_output"),
                }

            except SchemaValidationError as exc:
                logger.warning("Schema validation failed for %s: %s", model_name, exc)
                last_error = exc
                break  # next candidate

            except Exception as exc:
                err_s = str(exc).lower()

                # Auth error with newly acquired key → re-prompt
                if api_key_name in _NEWLY_ACQUIRED_KEYS and any(
                    kw in err_s for kw in ("auth", "401", "403", "invalid api key")
                ):
                    if _is_wsl():
                        console.print(
                            "[yellow]⚠ WSL detected: API key may contain "
                            "carriage returns. Check for \\r characters.[/yellow]",
                        )
                    console.print(
                        f"[red]Authentication failed for {api_key_name}. Please re-enter.[/red]",
                    )
                    try:
                        raw = input(f"Enter value for {api_key_name} (or press Enter to skip): ")
                    except (EOFError, KeyboardInterrupt):
                        last_error = exc
                        break
                    if raw.strip():
                        val = _sanitize_api_key(raw)
                        os.environ[api_key_name] = val
                        call_params["api_key"] = val
                        _save_key_to_env(project_root / ".env", api_key_name, val)
                        continue
                    last_error = exc
                    break

                # Anthropic temperature + thinking conflict
                if is_anthropic_thinking and "temperature" in err_s:
                    call_params["temperature"] = 1
                    logger.debug("Adjusting temperature to 1 for Anthropic thinking")
                    continue

                if retry < max_retries:
                    logger.warning(
                        "Retry %d/%d for %s: %s", retry + 1, max_retries, model_name, exc,
                    )
                    working_msgs = _bypass_cache(working_msgs)
                    continue

                logger.warning("Model %s failed after retries: %s", model_name, exc)
                last_error = exc
                break

        # Restore messages for next candidate
        all_messages = original_messages

    raise RuntimeError(f"All model candidates exhausted. Last error: {last_error}")