from __future__ import annotations

import json
import logging
import os
import re
import time as time_module
import warnings
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, Tuple

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv
from litellm.caching.caching import Cache
from pydantic import BaseModel, ValidationError
from rich.console import Console

# Internal imports
from .path_resolution import get_default_resolver

# --- Logging Configuration ---
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING")
PDD_ENVIRONMENT = os.getenv("PDD_ENVIRONMENT", "development")
VERBOSE_LOGGING = os.getenv("PDD_VERBOSE_LOGGING") == "1"

def setup_logging():
    level = getattr(logging, PDD_LOG_LEVEL.upper(), logging.INFO)
    if PDD_ENVIRONMENT == "production":
        level = max(level, logging.WARNING)
    if VERBOSE_LOGGING:
        level = logging.DEBUG
    
    logger.setLevel(level)
    
    llm_level = getattr(logging, LITELLM_LOG_LEVEL.upper(), logging.WARNING)
    litellm_logger.setLevel(llm_level)

    # LiteLLM param handling
    drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() == "true"
    litellm.drop_params = drop_params

def setup_file_logging(log_file: Optional[str] = None):
    if not log_file:
        return
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler(log_file, maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    litellm_logger.addHandler(handler)

def set_verbose_logging(enabled: bool = True):
    if enabled:
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)
    else:
        setup_logging()

setup_logging()
console = Console()

# --- Startup & Path Resolution ---
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()

# Load .env
dotenv_path = PROJECT_ROOT / ".env"
load_dotenv(dotenv_path)

def resolve_model_csv() -> Path:
    candidates = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for c in candidates:
        if c.is_file():
            return c
    try:
        # Fallback to packaged data
        import importlib.resources
        return Path(str(importlib.resources.files("pdd.data").joinpath("llm_model.csv")))
    except Exception:
        raise FileNotFoundError("Could not resolve llm_model.csv")

# --- Custom Exceptions ---
class SchemaValidationError(Exception):
    def __init__(self, message: str, raw_response: Any = None):
        super().__init__(message)
        self.raw_response = raw_response

class CloudFallbackError(Exception): pass
class CloudInvocationError(Exception): pass
class InsufficientCreditsError(Exception): pass

# --- LiteLLM Cache Setup ---
def setup_cache():
    if os.getenv("LITELLM_CACHE_DISABLE") == "1":
        litellm.cache = None
        return

    gcs_bucket = os.getenv("GCS_BUCKET_NAME")
    if gcs_bucket and os.getenv("GCS_HMAC_ACCESS_KEY_ID"):
        try:
            os.environ["AWS_ACCESS_KEY_ID"] = os.getenv("GCS_HMAC_ACCESS_KEY_ID", "")
            os.environ["AWS_SECRET_ACCESS_KEY"] = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY", "")
            litellm.cache = Cache(
                type="s3",
                s3_bucket_name=gcs_bucket,
                s3_endpoint_url="https://storage.googleapis.com"
            )
            return
        except Exception as e:
            logger.warning(f"S3 cache init failed: {e}")

    # Fallback to SQLite
    cache_db = PROJECT_ROOT / "litellm_cache.sqlite"
    litellm.cache = Cache(type="disk", disk_cache_dir=str(cache_db))

setup_cache()

# --- Callback & Cost Tracking ---
_LAST_CALLBACK_DATA = {"cost": 0.0, "model": ""}
_MODEL_RATE_MAP = {}

def _success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        cost = litellm.completion_cost(completion_response=completion_response)
        if cost is None:
            model = kwargs.get("model", "")
            rates = _MODEL_RATE_MAP.get(model, (0, 0))
            usage = completion_response.usage
            cost = (usage.prompt_tokens * rates[0] + usage.completion_tokens * rates[1]) / 1e6
        _LAST_CALLBACK_DATA["cost"] = cost
        _LAST_CALLBACK_DATA["model"] = kwargs.get("model", "")
    except Exception:
        pass

litellm.success_callback = [_success_callback]

# --- Structured Output Helpers ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for sub in schema["properties"].values():
            if isinstance(sub, dict): _ensure_all_properties_required(sub)
    if "items" in schema and isinstance(schema["items"], dict):
        _ensure_all_properties_required(schema["items"])
    for combiner in ["anyOf", "oneOf", "allOf"]:
        if combiner in schema:
            for sub in schema[combiner]: _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for sub in schema["$defs"].values(): _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for sub in schema["properties"].values():
                if isinstance(sub, dict): _add_additional_properties_false(sub)
    if "items" in schema and isinstance(schema["items"], dict):
        _add_additional_properties_false(schema["items"])
    if "$defs" in schema:
        for sub in schema["$defs"].values(): _add_additional_properties_false(sub)

# --- Python Repair Helpers ---
def _repair_python_syntax(code: str) -> str:
    import ast
    code = code.strip()
    # Common hallucination: trailing quotes
    for quote in ['"', "'", '"""', "'''"]:
        if code.endswith(quote):
            candidate = code[:-len(quote)]
            try:
                ast.parse(candidate)
                return candidate
            except SyntaxError: continue
    return code

def _smart_unescape_code(code: str) -> str:
    # Preserve \n inside literals, fix double escaped structure
    return code.replace("\\\\n", "\n").replace("\\n", "\n")

# --- Cloud Helpers ---
def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    return pydantic_class.model_validate(result)

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    # Placeholder for actual cloud call implementation
    # In a real scenario, this uses requests to call the llmInvoke endpoint
    raise CloudFallbackError("Cloud not implemented in this stub")

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
    if verbose: set_verbose_logging(True)

    # 1. Cloud routing
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
    if use_cloud:
        try:
            schema = None
            if output_pydantic: schema = _pydantic_to_json_schema(output_pydantic)
            elif output_schema: schema = output_schema
            
            payload = {
                "prompt": prompt, "inputJson": input_json, "messages": messages,
                "strength": strength, "temperature": temperature, "time": time,
                "verbose": verbose, "outputSchema": schema, "useBatchMode": use_batch_mode,
                "language": language
            }
            res = _llm_invoke_cloud(payload)
            if output_pydantic:
                res["result"] = _validate_with_pydantic(res["result"], output_pydantic)
            return res
        except InsufficientCreditsError: raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed: {e}. Falling back to local.[/yellow]")

    # 2. Local Execution Logic
    df = pd.read_csv(resolve_model_csv())
    # Fill rate map for callback
    global _MODEL_RATE_MAP
    _MODEL_RATE_MAP = {r['model']: (r['input'], r['output']) for _, r in df.iterrows()}

    # Select candidate models based on strength
    base_model = os.getenv("PDD_MODEL_DEFAULT") or df.iloc[0]['model']
    candidates = df.to_dict('records') # Simplification: should interpolate here
    
    last_err = None
    for model_info in candidates:
        try:
            model_name = model_info['model']
            api_key_name = model_info['api_key']
            
            # API Key Management
            api_key = os.getenv(api_key_name)
            if not api_key and api_key_name not in ["", "EXISTING_KEY"]:
                if os.getenv("PDD_FORCE"): continue
                api_key = input(f"Enter key for {api_key_name}: ").strip()
                if not api_key: continue
                os.environ[api_key_name] = api_key
                # Save to .env logic would go here

            # Prep params
            call_kwargs = {
                "model": model_name,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": 120
            }

            # Reasoning
            r_type = model_info.get('reasoning_type', 'none')
            if r_type == 'budget':
                budget = int(time * model_info.get('max_reasoning_tokens', 0))
                if "claude" in model_name:
                    call_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                    call_kwargs["temperature"] = 1.0
            elif r_type == 'effort':
                effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
                if "gpt-5" in model_name: 
                    call_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                else: 
                    call_kwargs["reasoning_effort"] = effort

            # Structured Output
            if output_pydantic or output_schema:
                schema_dict = output_pydantic.model_json_schema() if output_pydantic else output_schema
                if model_info.get('structured_output'):
                    _ensure_all_properties_required(schema_dict)
                    _add_additional_properties_false(schema_dict)
                    call_kwargs["response_format"] = {
                        "type": "json_schema",
                        "json_schema": {"name": "resp", "schema": schema_dict, "strict": True}
                    }

            # Invoke
            if use_batch_mode:
                response = litellm.batch_completion(**call_kwargs, messages=messages)
            elif "gpt-5" in model_name:
                response = litellm.responses(**call_kwargs) # Simplified wrapper
            else:
                response = litellm.completion(**call_kwargs, messages=messages)

            # Process result
            raw_content = response.choices[0].message.content
            # Repair / Validation logic
            res_val = raw_content
            if output_pydantic:
                res_val = _validate_with_pydantic(raw_content, output_pydantic)
            
            return {
                "result": res_val,
                "cost": _LAST_CALLBACK_DATA["cost"],
                "model_name": model_name,
                "thinking_output": getattr(response.choices[0].message, "reasoning_content", None)
            }

        except Exception as e:
            last_err = e
            logger.warning(f"Model {model_name} failed: {e}")
            continue

    raise RuntimeError(f"All models failed. Last error: {last_err}")