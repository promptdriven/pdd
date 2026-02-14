from __future__ import annotations

import os
import re
import json
import logging
import warnings
import time as time_module
import io
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

# Internal relative imports
try:
    from .path_resolution import get_default_resolver
except ImportError:
    # Fallback for standalone execution
    def get_default_resolver():
        class Resolver:
            def resolve_project_root(self):
                return Path.cwd()
        return Resolver()

# --- Logging Configuration ---
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

def setup_file_logging(log_file_path: str | None = None) -> None: 
    """Sets up rotating file handlers for logging."""
    if not log_file_path:
        return
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    litellm_logger.addHandler(handler)

def set_verbose_logging(verbose: bool = False) -> None:
    """Configures verbosity for both internal and litellm loggers."""
    level = logging.DEBUG if (verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1") else logging.INFO
    logger.setLevel(level)
    if hasattr(litellm, "set_verbose"):
        litellm.set_verbose = (level == logging.DEBUG)

# --- LiteLLM Global Config ---
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() in ("true", "1")
LLM_CALL_TIMEOUT = 120

# --- Path and Env Resolution ---
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
ENV_PATH = PROJECT_ROOT / ".env"
if ENV_PATH.exists():
    load_dotenv(ENV_PATH)

def _resolve_model_csv() -> Path | None:
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for p in paths:
        if p.is_file():
            return p
    return None

LLM_MODEL_CSV_PATH = _resolve_model_csv()

# --- Custom Exceptions ---
class SchemaValidationError(Exception):
    def __init__(self, message: str, raw_response: Any = None):
        super().__init__(message)
        self.raw_response = raw_response

class CloudFallbackError(Exception): pass
class CloudInvocationError(Exception): pass
class InsufficientCreditsError(Exception): pass

# --- State ---
_LAST_CALLBACK_DATA: Dict[str, Any] = {"cost": 0.0, "input_tokens": 0, "output_tokens": 0}

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        cost = litellm.completion_cost(completion_response=completion_response) or 0.0
        usage = getattr(completion_response, 'usage', None)
        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "input_tokens": getattr(usage, 'prompt_tokens', 0),
            "output_tokens": getattr(usage, 'completion_tokens', 0)
        }
    except Exception:
        pass

litellm.success_callback = [_litellm_success_callback]

# --- Helpers ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            _ensure_all_properties_required(prop)
    if "items" in schema: _ensure_all_properties_required(schema["items"])
    for complex_key in ("anyOf", "oneOf", "allOf"):
        if complex_key in schema:
            for sub in schema[complex_key]: _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values(): _ensure_all_properties_required(d)

def _unescape_code_newlines(obj: Any) -> None:
    """Recursively unescape string fields in a Pydantic model or dict."""
    if isinstance(obj, BaseModel):
        for field in obj.model_fields:
            val = getattr(obj, field)
            if isinstance(val, str):
                setattr(obj, field, _smart_unescape_code(val))
            elif isinstance(val, (list, dict, BaseModel)):
                _unescape_code_newlines(val)
    elif isinstance(obj, list):
        for item in obj: _unescape_code_newlines(item)
    elif isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str): obj[k] = _smart_unescape_code(v)
            else: _unescape_code_newlines(v)

def _smart_unescape_code(code: str) -> str:
    if r"\n" not in code or "\n" in code: return code
    try:
        return code.encode().decode('unicode_escape')
    except Exception:
        return code

def _sanitize_api_key(key: str) -> str:
    return re.sub(r'[\s\r\n]+', '', key)

def _save_key_to_env_file(key_name: str, value: str):
    lines = []
    if ENV_PATH.exists():
        lines = ENV_PATH.read_text().splitlines()
    new_lines = [l for l in lines if not l.split('=')[0].strip().endswith(key_name)]
    new_lines.append(f'{key_name}="{value}"')
    ENV_PATH.write_text("\n".join(new_lines) + "\n")

# --- Cloud Execution ---
def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, str): return pydantic_class.model_validate_json(result)
    return pydantic_class.model_validate(result)

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    from pdd.core.cloud import CloudConfig
    token = CloudConfig.get_jwt_token()
    url = CloudConfig.get_endpoint_url("llmInvoke")
    resp = requests.post(url, json=payload, headers={"Authorization": f"Bearer {token}"}, timeout=300)
    if resp.status_code == 200: return resp.json()
    if resp.status_code == 402: raise InsufficientCreditsError("Insufficient credits")
    if resp.status_code in (401, 403):
        from pdd.auth_service import clear_jwt_cache
        clear_jwt_cache()
        raise CloudFallbackError("Cloud auth failed")
    raise CloudInvocationError(f"Cloud error: {resp.status_code}")

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
    """Invokes an LLM with fallback logic, schema validation, and cost tracking."""
    set_verbose_logging(verbose)

    # Cloud Routing
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
    if use_cloud:
        try:
            payload = {
                "prompt": prompt, "inputJson": input_json, "messages": messages,
                "strength": strength, "temperature": temperature, "time": time,
                "verbose": verbose, "useBatchMode": use_batch_mode, "language": language
            }
            if output_pydantic: payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
            elif output_schema: payload["outputSchema"] = output_schema
            
            cloud_res = _llm_invoke_cloud(payload)
            result = cloud_res["result"]
            if output_pydantic: 
                result = _validate_with_pydantic(result, output_pydantic)
                _unescape_code_newlines(result)
            return {"result": result, "cost": cloud_res["totalCost"], "model_name": cloud_res["modelName"], "thinking_output": cloud_res.get("thinkingOutput")}
        except InsufficientCreditsError: raise
        except Exception as e:
            console.print(f"[yellow]Cloud failed ({e}), falling back to local...[/yellow]")

    # Local logic
    if LLM_MODEL_CSV_PATH:
        df = pd.read_csv(LLM_MODEL_CSV_PATH)
    else:
        csv_text = importlib.resources.files('pdd.data').joinpath('llm_model.csv').read_text()
        df = pd.read_csv(io.StringIO(csv_text))
    
    base_model_name = os.getenv("PDD_MODEL_DEFAULT") or df.iloc[0]['model']
    candidates = df.copy()
    candidates['avg_cost'] = (candidates['input'] + candidates['output']) / 2
    
    if strength < 0.5:
        candidates = candidates.sort_values('avg_cost')
    elif strength > 0.5:
        candidates = candidates.sort_values('coding_arena_elo', ascending=False)
    else:
        base_idx = candidates[candidates['model'] == base_model_name].index
        if not base_idx.empty:
            candidates = pd.concat([candidates.loc[base_idx], candidates.drop(base_idx)])

    last_err = None
    for _, m_info in candidates.iterrows():
        model = m_info['model']
        key_name = m_info['api_key']
        
        # API Key Logic
        api_key = os.getenv(key_name)
        if not api_key and key_name not in ("", "EXISTING_KEY"):
            if os.getenv("PDD_FORCE"): continue
            api_key = _sanitize_api_key(input(f"Enter API key for {key_name}: "))
            os.environ[key_name] = api_key
            _save_key_to_env_file(key_name, api_key)
            logger.warning(f"Key saved to {ENV_PATH}")

        # Reasoning Configuration
        kwargs: Dict[str, Any] = {"model": model, "temperature": temperature, "num_retries": 2, "timeout": LLM_CALL_TIMEOUT}
        if m_info['reasoning_type'] == 'budget':
            budget = int(time * m_info['max_reasoning_tokens'])
            if "anthropic" in str(model).lower():
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                kwargs["temperature"] = 1.0
        elif m_info['reasoning_type'] == 'effort':
            effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
            if "gpt-5" in str(model).lower():
                kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else: kwargs["reasoning_effort"] = effort

        # Invoke
        try:
            if messages: 
                current_msgs = messages
            else:
                if not use_batch_mode:
                    current_msgs = [{"role": "user", "content": prompt.format(**input_json) if input_json else prompt}]
                else:
                    current_msgs = [[{"role": "user", "content": prompt.format(**ij)}] for ij in input_json]

            if use_batch_mode: 
                response = litellm.batch_completion(messages=current_msgs, **kwargs)
            else: 
                response = litellm.completion(messages=current_msgs, **kwargs)
            
            # Response Processing
            resp_obj = response[0] if use_batch_mode else response
            content = resp_obj.choices[0].message.content
            thinking = resp_obj._hidden_params.get('thinking') or getattr(resp_obj.choices[0].message, 'reasoning_content', None)
            
            # Parse & Validate
            final_res = content
            if output_pydantic or output_schema:
                try:
                    json_match = re.search(r'\{.*\}', content, re.DOTALL)
                    if json_match: content = json_match.group()
                    if output_pydantic:
                        final_res = output_pydantic.model_validate_json(content)
                        _unescape_code_newlines(final_res)
                    else: 
                        final_res = json.loads(content)
                except Exception as e:
                    raise SchemaValidationError(str(e), raw_response=content)

            return {
                "result": final_res,
                "cost": _LAST_CALLBACK_DATA["cost"],
                "model_name": model,
                "thinking_output": thinking
            }

        except Exception as e:
            last_err = e
            logger.error(f"Model {model} failed: {e}")
            continue

    raise RuntimeError(f"All models failed. Last: {last_err}")