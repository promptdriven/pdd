from __future__ import annotations

import json
import logging
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal package imports
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
CONSOLE = Console()
LOGGER = logging.getLogger("pdd.llm_invoke")
LITELLM_LOGGER = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

LLM_CALL_TIMEOUT = 120
PDD_FORCE_LOCAL = os.getenv("PDD_FORCE_LOCAL", "0") == "1"

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (timeout, 5xx) that should trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required from Cloud."""
    pass

# --- Logging Setup ---

def setup_file_logging() -> None:
    from logging.handlers import RotatingFileHandler
    log_dir = Path.home() / ".pdd" / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "pdd.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    LOGGER.addHandler(handler)

def set_verbose_logging(verbose: bool = True) -> None:
    level = logging.DEBUG if verbose else logging.INFO
    LOGGER.setLevel(level)
    if verbose:
        LITELLM_LOGGER.setLevel(logging.DEBUG)
        litellm.set_verbose = True

# --- Initialization ---

def _initialize() -> None:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    load_dotenv(project_root / ".env")
    
    # Logging Levels
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"
        
    logging.basicConfig(level=logging.WARNING)
    LOGGER.setLevel(pdd_level)
    LITELLM_LOGGER.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # Global Callback
    def success_callback(kwargs, response_obj, start_time, end_time):
        global _LAST_CALLBACK_DATA
        usage = getattr(response_obj, "usage", None)
        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None,
            "response_obj": response_obj
        }
    litellm.success_callback = [success_callback]

    # Cache Configuration
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(
                type="s3",
                s3_bucket_name=os.getenv("GCS_BUCKET_NAME"),
                s3_api_base="https://storage.googleapis.com",
                s3_aws_access_key_id=os.getenv("GCS_HMAC_ACCESS_KEY_ID"),
                s3_aws_secret_access_key=os.getenv("GCS_HMAC_SECRET_ACCESS_KEY"),
            )
        else:
            cache_path = project_root / "litellm_cache.sqlite"
            litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(cache_path))

_initialize()

# --- Helper Functions ---

def _get_model_df() -> pd.DataFrame:
    resolver = get_default_resolver()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    try:
        paths.append(resolver.resolve_data_file("llm_model.csv"))
    except Exception:
        pass
        
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": row.get("input_cost_per_m", 0.0),
                    "output": row.get("output_cost_per_m", 0.0)
                }
            return df
    raise RuntimeError("llm_model.csv not found.")

def _manage_api_key(provider: str, key_name: str) -> None:
    if os.getenv(key_name) or os.getenv("PDD_FORCE"):
        return

    CONSOLE.print(f"[bold yellow]Missing API key for {provider} ({key_name})[/bold yellow]")
    key = input(f"Enter {key_name}: ").strip()
    if not key:
        return
    
    # WSL / Sanitization
    key = "".join(c for c in key if ord(c) >= 32)
    os.environ[key_name] = key
    
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    
    lines = []
    if env_path.exists():
        with open(env_path, "r") as f:
            lines = f.readlines()
            
    # Remove existing and commented
    new_lines = [l for l in lines if not l.strip().startswith(f"{key_name}=") and f"{key_name}=" not in l]
    new_lines.append(f"{key_name}={key}\n")
    
    with open(env_path, "w") as f:
        f.writelines(new_lines)
    
    CONSOLE.print(f"[bold red]SECURITY WARNING:[/bold red] Key saved to {env_path}")

def _repair_python_syntax(code: str) -> str:
    # Basic repair: trailing quotes or incomplete blocks
    code = code.strip()
    if code.count('"""') % 2 != 0:
        code += '"""'
    if code.count("'''") % 2 != 0:
        code += "'''"
    return code

def _smart_unescape_code(json_str: str) -> str:
    # Prevents double escaping of \n while preserving valid JSON
    try:
        data = json.loads(json_str)
        return json.dumps(data)
    except Exception:
        return json_str.replace("\\\\n", "\\n")

def _pydantic_to_json_schema(model: Type[BaseModel]) -> Dict[str, Any]:
    schema = model.model_json_schema()
    schema["__pydantic_class_name__"] = model.__name__
    _add_additional_properties_false(schema)
    _ensure_all_properties_required(schema)
    return schema

def _add_additional_properties_false(schema: Any) -> None:
    if isinstance(schema, dict):
        if "type" in schema and schema["type"] == "object":
            schema["additionalProperties"] = False
        for v in schema.values():
            _add_additional_properties_false(v)
    elif isinstance(schema, list):
        for item in schema:
            _add_additional_properties_false(item)

def _ensure_all_properties_required(schema: Any) -> None:
    if isinstance(schema, dict):
        if "properties" in schema:
            schema["required"] = list(schema["properties"].keys())
        for v in schema.values():
            _ensure_all_properties_required(v)
    elif isinstance(schema, list):
        for item in schema:
            _ensure_all_properties_required(item)

# --- Core Functionality ---

def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict, List[Dict]]] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict] = None,
    time: float = DEFAULT_TIME,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict], List[List[Dict]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    if verbose:
        set_verbose_logging(True)

    # Cloud logic
    if use_cloud is None:
        use_cloud = not PDD_FORCE_LOCAL # Simplified for brevity, usually checks CloudConfig
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt, input_json, strength, temperature, time, verbose,
                output_pydantic, output_schema, use_batch_mode, messages, language
            )
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # Model Selection
    df = _get_model_df()
    base_model = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter for models with keys (simplified logic)
    available_df = df.copy()
    
    # Sort for interpolation
    if strength < 0.5:
        # Interpolate by cost (base -> cheapest)
        candidates = available_df.sort_values("input_cost_per_m", ascending=True)
    elif strength > 0.5:
        # Interpolate by ELO (base -> highest)
        candidates = available_df.sort_values("coding_arena_elo", ascending=False)
    else:
        # Use base
        candidates = available_df # Logic for exact match usually goes here

    # Fallback Loop
    for _, row in candidates.iterrows():
        model_name = row["model"]
        provider = row["provider"]
        api_key_name = row.get("api_key")
        
        if api_key_name and api_key_name != "EXISTING_KEY":
            _manage_api_key(provider, api_key_name)
            
        try:
            # Construct Messages
            current_messages = messages or []
            if not current_messages:
                content = prompt.format(**input_json) if isinstance(input_json, dict) else prompt
                current_messages = [{"role": "user", "content": content}]

            # Reasoning Params
            kwargs: Dict[str, Any] = {
                "model": model_name,
                "messages": current_messages,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT,
            }

            r_type = row.get("reasoning_type", "none")
            max_r = row.get("max_reasoning_tokens", 0)
            
            if r_type == "budget":
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_r)}
                kwargs["temperature"] = 1.0 # Anthropic requirement
            elif r_type == "effort":
                effort = "low" if time < 0.33 else "medium" if time < 0.66 else "high"
                kwargs["reasoning_effort"] = effort

            # Structured Output
            effective_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
            if effective_schema and row.get("structured_output") == 1:
                kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "strict": True, "schema": effective_schema}
                }

            # Call
            if use_batch_mode:
                response = batch_completion(**kwargs)
            elif "gpt-5" in model_name: # Surrogate for Responses API check
                response = litellm.responses(**kwargs)
            else:
                response = completion(**kwargs)

            # Process Response
            content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            
            # JSON Parsing if needed
            result = content
            if effective_schema:
                # Basic JSON cleaning (balanced extraction, fenced blocks)
                json_match = re.search(r"(\{.*\})", content, re.DOTALL)
                if json_match:
                    result = json.loads(json_match.group(1))
                
                if output_pydantic:
                    result = output_pydantic.model_validate(result)

            cost = completion_cost(response)
            if cost is None: # Fallback to CSV
                usage = response.usage
                rates = _MODEL_RATE_MAP.get(model_name, {"input": 0.0, "output": 0.0})
                cost = (usage.prompt_tokens * rates["input"] + usage.completion_tokens * rates["output"]) / 1_000_000

            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            LOGGER.warning(f"Model {model_name} failed: {e}")
            continue

    raise RuntimeError("All LLM candidates exhausted.")

def _llm_invoke_cloud(**params) -> Dict[str, Any]:
    # Logic to hit Firebase Cloud Functions 'llmInvoke'
    # Included as placeholder for the networking logic required
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    # Logic for Firebase Auth token retrieval usually goes here
    token = os.getenv("PDD_CLOUD_TOKEN")
    
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
    # Serialize Pydantic to Schema for transport
    if params.get("output_pydantic"):
        params["output_schema"] = _pydantic_to_json_schema(params.pop("output_pydantic"))

    resp = requests.post(url, json=params, timeout=300)
    if resp.status_code == 402: raise InsufficientCreditsError("Insufficient PDD Cloud credits")
    if resp.status_code >= 500: raise CloudFallbackError(f"Cloud server error: {resp.status_code}")
    
    data = resp.json()
    return data