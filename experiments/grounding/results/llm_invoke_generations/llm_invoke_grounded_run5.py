from __future__ import annotations

import os
import re
import json
import logging
import warnings
import time as time_module
import io
import platform
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError

# Note: rich and litellm.caching are external dependencies
try:
    from rich.console import Console
    from litellm.caching.caching import Cache
except ImportError:
    Console = None
    Cache = None

# Internal package imports - assuming relative path resolution exists
try:
    from .path_resolution import get_default_resolver
except ImportError:
    def get_default_resolver():
        class Dummy:
            def resolve_project_root(self): return Path.cwd()
        return Dummy()

# Global Constants from package
DEFAULT_LLM_MODEL = "gpt-5-nano"  # Surrogate if env not set
LLM_CALL_TIMEOUT = 120

# --- Logging Configuration ---
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")
console = Console() if Console else None

def setup_file_logging(log_file_path: str | None = None) -> None:
    if not log_file_path:
        return
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    litellm_logger.addHandler(handler)

def set_verbose_logging(verbose: bool = False) -> None:
    level = logging.DEBUG if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1" else logging.INFO
    logger.setLevel(level)
    if os.getenv("PDD_ENVIRONMENT") == "production":
        logger.setLevel(logging.WARNING)
    
    litellm_level = logging.DEBUG if verbose else logging.WARNING
    litellm_logger.setLevel(litellm_level)
    litellm.set_verbose = verbose
    litellm.suppress_debug_info = not verbose

# Initial Setup
_drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() == "true"
litellm.drop_params = _drop_params

# --- Path Resolution & Startup ---
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
ENV_PATH = PROJECT_ROOT / ".env"
if ENV_PATH.exists():
    load_dotenv(ENV_PATH)

def _resolve_model_csv() -> Path | None:
    candidates = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for c in candidates:
        if c.is_file():
            return c
    try:
        return importlib.resources.files("pdd.data").joinpath("llm_model.csv")
    except Exception:
        return None

CSV_PATH = _resolve_model_csv()

# --- Exceptions ---
class SchemaValidationError(Exception):
    def __init__(self, message: str, raw_response: str | None = None):
        super().__init__(message)
        self.raw_response = raw_response

class CloudFallbackError(Exception): pass
class CloudInvocationError(Exception): pass
class InsufficientCreditsError(Exception): pass

# --- Caching ---
_LAST_CALLBACK_DATA = {"input_tokens": 0, "output_tokens": 0, "cost": 0.0, "finish_reason": None}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, "usage", None)
    if not usage: return
    
    model = kwargs.get("model", "")
    _LAST_CALLBACK_DATA["input_tokens"] = getattr(usage, "prompt_tokens", 0)
    _LAST_CALLBACK_DATA["output_tokens"] = getattr(usage, "completion_tokens", 0)
    
    try:
        cost = litellm.completion_cost(completion_response=completion_response)
    except Exception:
        rates = _MODEL_RATE_MAP.get(model, (0.0, 0.0))
        cost = (_LAST_CALLBACK_DATA["input_tokens"] * rates[0] + _LAST_CALLBACK_DATA["output_tokens"] * rates[1]) / 1_000_000
    
    _LAST_CALLBACK_DATA["cost"] = cost or 0.0

litellm.success_callback = [_litellm_success_callback]

# --- Helpers ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            _ensure_all_properties_required(prop)
    for k in ["anyOf", "oneOf", "allOf"]:
        if k in schema:
            for sub in schema[k]: _ensure_all_properties_required(sub)
    if "items" in schema: _ensure_all_properties_required(schema["items"])
    if "$defs" in schema:
        for d in schema["$defs"].values(): _ensure_all_properties_required(d)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values(): _add_additional_properties_false(prop)
    if "items" in schema: _add_additional_properties_false(schema["items"])
    for k in ["anyOf", "oneOf", "allOf"]:
        if k in schema:
            for sub in schema[k]: _add_additional_properties_false(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values(): _add_additional_properties_false(d)

def _repair_python_syntax(code: str) -> str:
    import ast
    code = code.strip()
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        for q in ['"', "'"]:
            if code.endswith(q):
                cand = code[:-1]
                try: ast.parse(cand); return cand
                except SyntaxError: pass
    return code

def _smart_unescape_code(code: str) -> str:
    if '\\n' not in code: return code
    return code.encode().decode('unicode_escape')

def _is_prose_field(name: str) -> bool:
    return name.lower() in {"reasoning", "explanation", "analysis", "thought", "summary"}

def _sanitize_key(key: str) -> str:
    return key.strip().replace('\r', '')

def _save_key(name: str, val: str) -> None:
    lines = []
    if ENV_PATH.exists():
        lines = ENV_PATH.read_text().splitlines()
    new_lines = [l for l in lines if not l.startswith(f"{name}=") and not l.startswith(f"# {name}=")]
    new_lines.append(f'{name}="{val}"')
    ENV_PATH.write_text("\n".join(new_lines) + "\n")

# --- Cloud Execution ---
def _pydantic_to_json_schema(model: Type[BaseModel]) -> Dict[str, Any]:
    schema = model.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = model.__name__
    return schema

def _llm_invoke_cloud(**kwargs) -> Dict[str, Any]:
    raise CloudFallbackError("Cloud not configured in this stub")

# --- Model Selection ---
def _get_candidates(strength: float, base_name: str | None, df: pd.DataFrame) -> List[Dict]:
    df = df.copy()
    df['avg_cost'] = (df['input'] + df['output']) / 2
    
    base_row = df[df['model'] == base_name]
    if base_row.empty:
        base_model = df.iloc[0]
    else:
        base_model = base_row.iloc[0]
        
    if strength == 0.5:
        return [base_model.to_dict()] + df[df['model'] != base_name].sort_values('coding_arena_elo', ascending=False).to_dict('records')
    elif strength < 0.5:
        target = df['avg_cost'].min() + (strength / 0.5) * (base_model['avg_cost'] - df['avg_cost'].min())
        df['dist'] = (df['avg_cost'] - target).abs()
    else:
        target = base_model['coding_arena_elo'] + ((strength - 0.5) / 0.5) * (df['coding_arena_elo'].max() - base_model['coding_arena_elo'])
        df['dist'] = (df['coding_arena_elo'] - target).abs()
        
    return df.sort_values('dist').to_dict('records')

# --- Main Function ---
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
    
    if use_cloud is not False and os.getenv("PDD_FORCE_LOCAL") != "1":
        try:
            return _llm_invoke_cloud(prompt=prompt, inputJson=input_json, messages=messages, 
                                    strength=strength, temperature=temperature, time=time, 
                                    verbose=verbose, outputSchema=output_schema or (output_pydantic and _pydantic_to_json_schema(output_pydantic)))
        except CloudFallbackError as e:
            if console: console.print(f"[yellow]Cloud failed: {e}. Falling back...[/yellow]")
        except InsufficientCreditsError: raise

    if not CSV_PATH: raise RuntimeError("Model CSV not found")
    df = pd.read_csv(CSV_PATH)
    global _MODEL_RATE_MAP
    _MODEL_RATE_MAP = {r['model']: (r['input'], r['output']) for _, r in df.iterrows()}
    
    base_model = os.getenv("PDD_MODEL_DEFAULT")
    candidates = _get_candidates(strength, base_model, df)
    
    last_err = None
    for model_info in candidates:
        model_name = model_info['model']
        key_name = model_info['api_key']
        
        api_key = os.getenv(key_name)
        if not api_key and key_name not in ["", "EXISTING_KEY"]:
            if os.getenv("PDD_FORCE") == "1": continue
            if console: console.print(f"[bold red]Missing API Key for {model_name} ({key_name})[/bold red]")
            api_key = _sanitize_key(input(f"Enter {key_name}: "))
            if not api_key: continue
            os.environ[key_name] = api_key
            _save_key(key_name, api_key)
            if console: console.print(f"[green]Key saved to {ENV_PATH}[/green]")

        try:
            if not messages:
                if isinstance(input_json, list): use_batch_mode = True
                curr_msgs = [{"role": "user", "content": prompt.format(**input_json)}] if not use_batch_mode else \
                            [[{"role": "user", "content": prompt.format(**i)}] for i in input_json]
            else:
                curr_msgs = messages

            call_kwargs = {"model": model_name, "messages": curr_msgs, "temperature": temperature, "timeout": LLM_CALL_TIMEOUT}
            rtype = model_info.get("reasoning_type", "none")
            if rtype == "budget":
                budget = int(time * model_info.get("max_reasoning_tokens", 0))
                if "anthropic" in model_name:
                    call_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                    call_kwargs["temperature"] = 1.0
            elif rtype == "effort":
                effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
                if "gpt-5" in model_name: 
                    call_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                else: 
                    call_kwargs["reasoning_effort"] = effort

            if (output_pydantic or output_schema) and model_info.get("structured_output"):
                schema = output_schema or output_pydantic.model_json_schema()
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)
                call_kwargs["response_format"] = {
                    "type": "json_schema", 
                    "json_schema": {"name": "output", "strict": True, "schema": schema}
                }

            if "gpt-5" in model_name:
                response = litellm.responses(**call_kwargs)
            elif use_batch_mode:
                response = litellm.batch_completion(**call_kwargs)
            else:
                response = litellm.completion(**call_kwargs)

            res_list = response if isinstance(response, list) else [response]
            final_results = []
            final_thinking = []
            
            for r in res_list:
                content = r.choices[0].message.content
                thinking = r._hidden_params.get("thinking") or getattr(r.choices[0].message, "reasoning_content", None)
                
                if output_pydantic:
                    try:
                        json_str = content
                        if "```json" in content:
                            json_str = re.search(r"```json\s*(.*?)\s*```", content, re.S).group(1)
                        obj = output_pydantic.model_validate_json(json_str)
                        _unescape_code_newlines(obj)
                        if language in ["python", None] and _has_invalid_python_code(obj):
                            raise SchemaValidationError("Python syntax invalid")
                        final_results.append(obj)
                    except Exception as e:
                        raise SchemaValidationError(f"Parse failed: {e}")
                else:
                    final_results.append(content)
                final_thinking.append(thinking)

            return {
                "result": final_results if use_batch_mode else final_results[0],
                "cost": _LAST_CALLBACK_DATA["cost"],
                "model_name": model_name,
                "thinking_output": final_thinking if use_batch_mode else final_thinking[0]
            }

        except Exception as e:
            last_err = e
            logger.warning(f"Model {model_name} failed: {e}")
            continue

    raise RuntimeError(f"All models failed. Last error: {last_err}")

def _has_invalid_python_code(obj: Any) -> bool:
    import ast
    if isinstance(obj, BaseModel):
        for f, v in obj.model_dump().items():
            if _is_prose_field(f): continue
            if isinstance(v, str) and ("def " in v or "import " in v):
                try: ast.parse(v)
                except SyntaxError: return True
    return False

def _unescape_code_newlines(obj: Any) -> None:
    if isinstance(obj, BaseModel):
        for field in obj.model_fields:
            val = getattr(obj, field)
            if isinstance(val, str):
                setattr(obj, field, _smart_unescape_code(val))
            elif isinstance(val, (list, dict, BaseModel)):
                _unescape_code_newlines(val)
    elif isinstance(obj, list):
        for i in range(len(obj)):
            if isinstance(obj[i], str): obj[i] = _smart_unescape_code(obj[i])
            else: _unescape_code_newlines(obj[i])
    elif isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str): obj[k] = _smart_unescape_code(v)
            else: _unescape_code_newlines(v)