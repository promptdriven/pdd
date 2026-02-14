from __future__ import annotations

import os
import re
import json
import logging
import warnings
import time as time_module
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console
from litellm.caching.caching import Cache

# Internal module imports
from .path_resolution import get_default_resolver

# Logging Configuration
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")
console = Console()

PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"

if PRODUCTION_MODE:
    logger.setLevel(logging.WARNING)
    litellm_logger.setLevel(logging.WARNING)
else:
    logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))
    litellm_logger.setLevel(getattr(logging, os.getenv("LITELLM_LOG_LEVEL", "WARNING"), logging.WARNING))

litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() in ("true", "1", "yes")

def setup_file_logging(log_file_path: str | None = None) -> None:
    """Configure rotating file handler for logging."""
    if not log_file_path:
        return
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler(log_file_path, maxBytes=10 * 1024 * 1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    litellm_logger.addHandler(handler)

def set_verbose_logging(verbose: bool = False) -> None:
    """Toggle DEBUG level logging."""
    level = logging.DEBUG if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1" else logging.INFO
    logger.setLevel(level)
    if verbose:
        litellm.set_verbose = True

# --- Path and Environment Setup ---
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
ENV_PATH = PROJECT_ROOT / ".env"
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

def _get_model_csv_path() -> Path:
    candidates = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    for c in candidates:
        if c.is_file():
            return c
    # Fallback to packaged data
    return Path(str(importlib.resources.files("pdd").joinpath("data/llm_model.csv")))

LLM_MODEL_CSV_PATH = _get_model_csv_path()
DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT")
LLM_CALL_TIMEOUT = 120

# --- Caching ---
configured_cache = None
if os.getenv("LITELLM_CACHE_DISABLE") != "1":
    gcs_bucket = os.getenv("GCS_BUCKET_NAME")
    if gcs_bucket and os.getenv("GCS_HMAC_ACCESS_KEY_ID"):
        os.environ["AWS_ACCESS_KEY_ID"] = os.getenv("GCS_HMAC_ACCESS_KEY_ID", "").strip()
        os.environ["AWS_SECRET_ACCESS_KEY"] = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY", "").strip()
        configured_cache = Cache(type="s3", s3_bucket_name=gcs_bucket, s3_endpoint_url="https://storage.googleapis.com")
    else:
        sqlite_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_path))
    litellm.cache = configured_cache

# --- Callback and Cost fallback ---
_LAST_CALLBACK_DATA: Dict[str, Any] = {"cost": 0.0}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        cost = litellm.completion_cost(completion_response=completion_response)
    except Exception:
        model = kwargs.get("model", "")
        rates = _MODEL_RATE_MAP.get(model, (0.0, 0.0))
        usage = completion_response.usage
        cost = (usage.prompt_tokens * rates[0] + usage.completion_tokens * rates[1]) / 1_000_000
    _LAST_CALLBACK_DATA["cost"] = cost or 0.0

litellm.success_callback = [_litellm_success_callback]

# --- Custom Exceptions ---
class SchemaValidationError(Exception):
    pass

class CloudFallbackError(Exception):
    pass

class CloudInvocationError(Exception):
    pass

class InsufficientCreditsError(Exception):
    pass

# --- Helper Functions ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            _ensure_all_properties_required(prop)
    if "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _ensure_all_properties_required(d)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values():
                _add_additional_properties_false(prop)
    if "items" in schema:
        _add_additional_properties_false(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _add_additional_properties_false(d)

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    return pydantic_class.model_validate_json(result)

def _sanitize_api_key(key: str) -> str:
    return re.sub(r"[\s\r\n\t]+", "", key)

def _save_key_to_env_file(key_name: str, value: str) -> None:
    lines = []
    if ENV_PATH.exists():
        with open(ENV_PATH, "r") as f:
            lines = f.readlines()
    
    new_lines = [l for l in lines if not (l.strip().startswith(f"{key_name}=") or l.strip().startswith(f"# {key_name}="))]
    new_lines.append(f'{key_name}="{value}"\n')
    
    with open(ENV_PATH, "w") as f:
        f.writelines(new_lines)
    logger.warning(f"Security: API Key {key_name} saved to {ENV_PATH}")

def _repair_python_syntax(code: str) -> str:
    import ast
    code = code.strip()
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        # Simple repair for common LLM quoting artifacts
        for quote in ('"', "'", "```"):
            if code.endswith(quote):
                try:
                    candidate = code[:-len(quote)].strip()
                    ast.parse(candidate)
                    return candidate
                except SyntaxError:
                    continue
    return code

def _unescape_code_newlines(obj: Any) -> None:
    """Recursively unescape newline characters in string values of a dict or list."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str):
                obj[k] = v.replace("\\n", "\n")
            else:
                _unescape_code_newlines(v)
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            if isinstance(v, str):
                obj[i] = v.replace("\\n", "\n")
            else:
                _unescape_code_newlines(v)

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    from .auth_service import get_jwt_token, clear_jwt_cache
    token = get_jwt_token()
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    try:
        resp = requests.post(url, json=payload, headers={"Authorization": f"Bearer {token}"}, timeout=300)
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in (401, 403):
            clear_jwt_cache()
            raise CloudFallbackError("Cloud auth failed.")
        resp.raise_for_status()
        data = resp.json()
        return {
            "result": data["result"],
            "cost": data["totalCost"],
            "model_name": data["modelName"],
            "thinking_output": data.get("thinkingOutput")
        }
    except Exception as e:
        if isinstance(e, InsufficientCreditsError): raise
        raise CloudFallbackError(str(e))

def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict, List[Dict]]] = None,
    strength: float = 0.5,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict] = None,
    time: float = 0.25,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict], List[List[Dict]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    set_verbose_logging(verbose)

    # Cloud Check
    if use_cloud is not False and os.getenv("PDD_FORCE_LOCAL") != "1":
        try:
            payload = {
                "prompt": prompt, "inputJson": input_json, "messages": messages,
                "strength": strength, "temperature": temperature, "time": time,
                "verbose": verbose, "useBatchMode": use_batch_mode, "language": language
            }
            if output_pydantic: payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
            elif output_schema: payload["outputSchema"] = output_schema
            
            res = _llm_invoke_cloud(payload)
            if output_pydantic:
                res["result"] = _validate_with_pydantic(res["result"], output_pydantic)
            return res
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed: {e}. Falling back to local.[/yellow]")
        except InsufficientCreditsError:
            raise

    # Local Model Selection
    df = pd.read_csv(LLM_MODEL_CSV_PATH)
    for col in ["input", "output", "coding_arena_elo", "max_reasoning_tokens"]:
        df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)
    df["avg_cost"] = (df["input"] + df["output"]) / 2
    
    global _MODEL_RATE_MAP
    _MODEL_RATE_MAP = {r["model"]: (r["input"], r["output"]) for _, r in df.iterrows()}

    base_model = df[df["model"] == DEFAULT_BASE_MODEL]
    if base_model.empty:
        base_model = df.iloc[[0]]
    
    base_row = base_model.iloc[0]
    if strength < 0.5:
        cheapest = df.iloc[[df["avg_cost"].idxmin()]].iloc[0]
        target_cost = cheapest["avg_cost"] + (strength / 0.5) * (base_row["avg_cost"] - cheapest["avg_cost"])
        df["dist"] = (df["avg_cost"] - target_cost).abs()
    else:
        highest = df.iloc[[df["coding_arena_elo"].idxmax()]].iloc[0]
        target_elo = base_row["coding_arena_elo"] + ((strength - 0.5) / 0.5) * (highest["coding_arena_elo"] - base_row["coding_arena_elo"])
        df["dist"] = (df["coding_arena_elo"] - target_elo).abs()

    candidates = df.sort_values("dist")

    last_error = ""
    for _, m_row in candidates.iterrows():
        model_name = m_row["model"]
        key_name = m_row["api_key"]
        
        # API Key management
        if key_name and key_name != "EXISTING_KEY":
            api_key = os.getenv(key_name)
            if not api_key:
                if os.getenv("PDD_FORCE"): continue
                api_key = _sanitize_api_key(console.input(f"Enter API Key for {key_name}: "))
                if not api_key: continue
                os.environ[key_name] = api_key
                _save_key_to_env_file(key_name, api_key)

        # Build Arguments
        msgs = messages
        if not msgs:
            if isinstance(input_json, list):
                msgs = [[{"role": "user", "content": prompt.format(**ij)}] for ij in input_json]
                use_batch_mode = True
            else:
                msgs = [{"role": "user", "content": prompt.format(**input_json)}]

        call_kwargs: Dict[str, Any] = {
            "model": model_name, "messages": msgs, "temperature": temperature,
            "num_retries": 2, "timeout": LLM_CALL_TIMEOUT
        }

        # Vertex AI logic
        if m_row["provider"].lower() == "google" or "vertex_ai" in model_name:
            loc = m_row.get("location") or os.getenv("VERTEX_LOCATION", "us-central1")
            call_kwargs.update({
                "vertex_project": os.getenv("VERTEX_PROJECT"),
                "vertex_location": loc,
                "vertex_credentials": os.getenv("VERTEX_CREDENTIALS")
            })

        # LM Studio
        if "lm_studio" in model_name.lower():
            call_kwargs["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
            call_kwargs["api_key"] = "lm-studio"

        # Reasoning Params
        rtype = m_row["reasoning_type"]
        if rtype == "budget":
            budget = int(time * m_row["max_reasoning_tokens"])
            call_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
            call_kwargs["temperature"] = 1.0 # Required for Anthropic thinking
        elif rtype == "effort":
            effort = "low" if time < 0.3 else "medium" if time < 0.7 else "high"
            if "gpt-5" in model_name:
                call_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                call_kwargs["reasoning_effort"] = effort

        # Structured Output
        if output_pydantic or output_schema:
            if m_row["structured_output"]:
                schema = output_pydantic.model_json_schema() if output_pydantic else output_schema
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)
                call_kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "output", "schema": schema, "strict": True}
                }
            elif "groq" in model_name.lower():
                call_kwargs["response_format"] = {"type": "json_object"}

        # Invoke
        try:
            if "gpt-5" in model_name and not use_batch_mode:
                completion = litellm.responses(**call_kwargs)
            elif use_batch_mode:
                completion = litellm.batch_completion(**call_kwargs)
            else:
                completion = litellm.completion(**call_kwargs)
            
            # Post-process
            def process_item(c):
                content = c.choices[0].message.content
                if content is None: raise ValueError("None content")
                
                # Extract JSON if needed
                if output_pydantic or output_schema:
                    try:
                        content = json.loads(content)
                    except Exception:
                        match = re.search(r"\{.*\}", content, re.DOTALL)
                        if match: content = json.loads(match.group())
                    
                    if output_pydantic:
                        _unescape_code_newlines(content)
                        content = output_pydantic.model_validate(content)
                        if language in ("python", None) and _has_invalid_python_code(content):
                            raise SchemaValidationError("Invalid Python code")
                return content

            if use_batch_mode:
                result = [process_item(it) for it in completion]
            else:
                result = process_item(completion)
            
            thinking = completion[0]._hidden_params.get("thinking") if use_batch_mode else completion._hidden_params.get("thinking")
            if not thinking and not use_batch_mode:
                thinking = getattr(completion.choices[0].message, "reasoning_content", None)

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA["cost"],
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            last_error = str(e)
            logger.warning(f"Model {model_name} failed: {e}")
            continue

    raise RuntimeError(f"All candidate models failed. Last error: {last_error}")

def _has_invalid_python_code(obj: Any) -> bool:
    import ast
    prose_keys = {"reasoning", "explanation", "analysis", "thought"}
    if isinstance(obj, str):
        if len(obj) < 10: return False
        try:
            ast.parse(obj)
            return False
        except SyntaxError:
            return True
    if isinstance(obj, BaseModel):
        for k, v in obj.model_dump().items():
            if k not in prose_keys and _has_invalid_python_code(v): return True
    return False