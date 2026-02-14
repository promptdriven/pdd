from __future__ import annotations

import os
import re
import ast
import json
import time as time_module
import logging
import warnings
import pandas as pd
import litellm
import requests
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple
from logging.handlers import RotatingFileHandler

from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

# Internal relative imports
from .path_resolution import get_default_resolver

# Constants and Global Variables
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {
    "input_tokens": 0,
    "output_tokens": 0,
    "finish_reason": None,
    "cost": 0.0,
}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

# --- Logging Configuration ---
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")
console = Console()

def setup_file_logging(log_file_path: Optional[str] = None) -> None:    
    """Configure rotating file handler for logging."""
    if not log_file_path:
        return
    try:
        handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        handler.setFormatter(formatter)
        logger.addHandler(handler)
        litellm_logger.addHandler(handler)
    except Exception as e:
        console.print(f"[red]Failed to set up file logging: {e}[/red]")

def set_verbose_logging(verbose: bool = False) -> None:
    """Toggle DEBUG level logging."""
    level = logging.DEBUG if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1" else logging.INFO
    logger.setLevel(level)
    if verbose:
        litellm_logger.setLevel(logging.DEBUG)
        litellm.set_verbose = True
    else:
        litellm_logger.setLevel(logging.WARNING)
        litellm.set_verbose = False

# Initial logging setup
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
logger.setLevel(getattr(logging, PDD_LOG_LEVEL))
litellm_logger.setLevel(logging.WARNING if os.getenv("PDD_ENVIRONMENT") == "production" else logging.INFO)
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() == "true"

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Triggers model fallback on structured output failure."""
    def __init__(self, message: str, raw_response: Any = None):
        super().__init__(message)
        self.raw_response = raw_response

class CloudFallbackError(Exception): pass
class CloudInvocationError(Exception): pass
class InsufficientCreditsError(Exception): pass

# --- Path & Env Resolution ---

resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
ENV_PATH = PROJECT_ROOT / ".env"
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

def resolve_model_csv() -> Path:
    candidates = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for c in candidates:
        if c.is_file(): return c
    return Path(str(importlib.resources.files("pdd.data").joinpath("llm_model.csv")))

LLM_MODEL_CSV_PATH = resolve_model_csv()
DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT")

# --- LiteLLM Callbacks & Cache ---

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, 'usage', None)
    _LAST_CALLBACK_DATA["input_tokens"] = getattr(usage, 'prompt_tokens', 0)
    _LAST_CALLBACK_DATA["output_tokens"] = getattr(usage, 'completion_tokens', 0)
    _LAST_CALLBACK_DATA["finish_reason"] = completion_response.choices[0].finish_reason
    try:
        _LAST_CALLBACK_DATA["cost"] = litellm.completion_cost(completion_response=completion_response) or 0.0
    except Exception:
        model = kwargs.get("model", "")
        rates = _MODEL_RATE_MAP.get(model, (0.0, 0.0))
        _LAST_CALLBACK_DATA["cost"] = (_LAST_CALLBACK_DATA["input_tokens"] * rates[0] + 
                                       _LAST_CALLBACK_DATA["output_tokens"] * rates[1]) / 1_000_000

litellm.success_callback = [_litellm_success_callback]

# Cache Setup
if os.getenv("LITELLM_CACHE_DISABLE") != "1":
    try:
        from litellm.caching import Cache
        if os.getenv("GCS_HMAC_ACCESS_KEY_ID"):
            litellm.cache = Cache(type="s3", s3_bucket_name=os.getenv("GCS_BUCKET_NAME"),
                                  s3_region_name=os.getenv("GCS_REGION_NAME", "auto"),
                                  s3_endpoint_url="https://storage.googleapis.com")
        else:
            litellm.cache = Cache(type="disk", disk_cache_dir=str(PROJECT_ROOT / "litellm_cache.sqlite"))
    except Exception as e:
        logger.warning(f"Cache init failed: {e}")

# --- Logic Helpers ---

def _ensure_all_properties_required(schema: dict) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            _ensure_all_properties_required(prop)
    for k in ("anyOf", "oneOf", "allOf"):
        if k in schema:
            for sub in schema[k]: _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values(): _ensure_all_properties_required(d)

def _add_additional_properties_false(schema: dict) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for p in schema["properties"].values(): _add_additional_properties_false(p)
    # Recurse definitions
    for sub in schema.get("anyOf", []) + schema.get("oneOf", []) + schema.get("allOf", []):
        _add_additional_properties_false(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values(): _add_additional_properties_false(d)

def _sanitize_api_key(key: str) -> str:
    return re.sub(r'[\x00-\x1f\x7f-\x9f]', '', key).strip()

def _save_key_to_env(key_name: str, value: str) -> None:
    lines = ENV_PATH.read_text().splitlines() if ENV_PATH.exists() else []
    new_lines = [line for line in lines if not line.strip().startswith((f"{key_name}=", f"# {key_name}="))]
    new_lines.append(f'{key_name}="{value}"')
    ENV_PATH.write_text("\n".join(new_lines) + "\n")
    console.print(f"[yellow]Security Warning: API key saved to {ENV_PATH}[/yellow]")

def _smart_unescape_code(code: str) -> str:
    # Preserves \n inside string literals but fixes double escaped structural newlines
    if '\\n' not in code: return code
    return code.encode().decode('unicode_escape') if '\n' not in code else code

def _repair_python_syntax(code: str) -> str:
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        # Common LLM error: trailing quotes or incomplete closures
        code = code.strip()
        for quote in ('"', "'", '"""', "'''"):
            if code.endswith(quote):
                try:
                    c = code[:-len(quote)]
                    ast.parse(c)
                    return c
                except SyntaxError: continue
    return code

# --- Core Function ---

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
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(prompt, input_json, strength, temperature, verbose, 
                                     output_pydantic, output_schema, time, use_batch_mode, messages, language)
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed ({e}), falling back to local...[/yellow]")
        except InsufficientCreditsError: raise

    # Local Logic
    df = pd.read_csv(LLM_MODEL_CSV_PATH)
    global _MODEL_RATE_MAP
    _MODEL_RATE_MAP = {r['model']: (r['input'], r['output']) for _, r in df.iterrows()}

    # Select Candidates (Interpolation Logic)
    base_name = DEFAULT_BASE_MODEL or df.iloc[0]['model']
    base_model = df[df['model'] == base_name].iloc[0] if base_name in df['model'].values else df.iloc[0]
    
    if strength < 0.5:
        candidates = df[df['input'] <= base_model['input']].sort_values('input', ascending=True)
    elif strength > 0.5:
        candidates = df[df['coding_arena_elo'] >= base_model['coding_arena_elo']].sort_values('coding_arena_elo', ascending=False)
    else:
        candidates = df[df['model'] == base_name]
        # Fallback to ELO order
        candidates = pd.concat([candidates, df.sort_values('coding_arena_elo', ascending=False)]).drop_duplicates('model')

    last_error = None
    for _, row in candidates.iterrows():
        model_name = row['model']
        api_key_name = row['api_key']
        
        # API Key Management
        api_key = os.getenv(api_key_name)
        if not api_key and api_key_name not in ("", "EXISTING_KEY"):
            if os.getenv("PDD_FORCE"): continue
            api_key = _sanitize_api_key(input(f"Enter API key for {api_key_name}: "))
            if not api_key: continue
            os.environ[api_key_name] = api_key
            _save_key_to_env(api_key_name, api_key)

        # Call Params
        msgs = messages or _format_messages(prompt, input_json, use_batch_mode)
        call_kwargs = {
            "model": model_name, "messages": msgs, "temperature": temperature,
            "timeout": LLM_CALL_TIMEOUT, "num_retries": 2, "api_key": api_key
        }
        if row.get('base_url'): call_kwargs["base_url"] = row['base_url']
        if row['provider'] == "LM Studio": 
            call_kwargs["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
            call_kwargs["api_key"] = "lm-studio"

        # Reasoning
        if row['reasoning_type'] == 'budget':
            call_kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * row['max_reasoning_tokens'])}
            if "claude" in model_name: call_kwargs["temperature"] = 1.0
        elif row['reasoning_type'] == 'effort':
            effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
            if "gpt-5" in model_name: call_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else: call_kwargs["reasoning_effort"] = effort

        # Structured Output
        if output_pydantic or output_schema:
            schema = output_schema or output_pydantic.model_json_schema()
            _ensure_all_properties_required(schema)
            _add_additional_properties_false(schema)
            
            if row['structured_output']:
                call_kwargs["response_format"] = {
                    "type": "json_schema", 
                    "json_schema": {"name": "resp", "schema": schema, "strict": True}
                }
            if row['provider'] == "LM Studio":
                call_kwargs["extra_body"] = {"response_format": call_kwargs.pop("response_format")}

        try:
            if "gpt-5" in model_name and not use_batch_mode:
                response = litellm.responses(**call_kwargs)
            elif use_batch_mode:
                response = litellm.batch_completion(**call_kwargs)
            else:
                response = litellm.completion(**call_kwargs)
            
            # Processing
            return _process_response(response, output_pydantic, language, model_name)
        except Exception as e:
            last_error = e
            logger.warning(f"Model {model_name} failed: {e}")
            continue

    raise RuntimeError(f"All models failed. Last error: {last_error}")

def _format_messages(prompt, input_json, batch):
    if batch: return [[{"role": "user", "content": prompt.format(**item)}] for item in input_json]
    return [{"role": "user", "content": prompt.format(**input_json)}]

def _process_response(resp, pydantic_cls, language, model_name):
    # Simplified extraction logic based on LiteLLM structure
    raw = resp.choices[0].message.content
    thinking = getattr(resp.choices[0].message, 'reasoning_content', None) or resp._hidden_params.get('thinking')
    
    res = raw
    if pydantic_cls:
        try:
            # Balanced brace extraction for non-native JSON
            match = re.search(r'\{.*\}', raw, re.DOTALL)
            json_str = match.group(0) if match else raw
            res = pydantic_cls.model_validate_json(json_str)
            # Code repair
            for field in res.model_fields:
                val = getattr(res, field)
                if isinstance(val, str) and field not in ("reasoning", "explanation"):
                    fixed = _repair_python_syntax(_smart_unescape_code(val))
                    setattr(res, field, fixed)
        except Exception as e:
            raise SchemaValidationError(str(e), raw)

    return {
        "result": res,
        "cost": _LAST_CALLBACK_DATA["cost"],
        "model_name": model_name,
        "thinking_output": thinking
    }

def _llm_invoke_cloud(*args):
    # Mocking cloud function call
    raise CloudFallbackError("Cloud logic omitted for brevity in this snippet")