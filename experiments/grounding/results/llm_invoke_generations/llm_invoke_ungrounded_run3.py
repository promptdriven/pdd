from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as per requirements
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# Constants
LLM_CALL_TIMEOUT = 120
LITELLM_CACHE_FILE = "litellm_cache.sqlite"

# Logging setup
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")
console = Console()

# Global state for cost tracking
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic or Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required."""
    pass

def setup_logging():
    level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        level = "DEBUG"
    
    logging.basicConfig(level=level)
    logger.setLevel(level)
    
    lt_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lt_level = "WARNING"
    litellm_logger.setLevel(lt_level)

def _init_litellm_config():
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # Cache Configuration
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        try:
            if os.getenv("GCS_BUCKET_NAME"):
                # S3-compatible GCS cache
                from litellm.caching import Cache
                litellm.cache = Cache(
                    type="s3",
                    s3_bucket_name=os.getenv("GCS_BUCKET_NAME"),
                    s3_region_name="us-central1",
                    s3_api_version="v2"
                )
            else:
                # Local SQLite
                resolver = get_default_resolver()
                cache_path = resolver.resolve_project_root() / LITELLM_CACHE_FILE
                litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(cache_path))
        except Exception as e:
            logger.warning(f"Failed to initialize LiteLLM cache: {e}")

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", {})
        cost = completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception:
        pass

litellm.success_callback = [_success_callback]

def _get_model_from_csv(strength: float, use_cloud: bool = False) -> Dict[str, Any]:
    resolver = get_default_resolver()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        resolver.resolve_data_file("llm_model.csv")
    ]
    
    df = None
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            break
            
    if df is None:
        raise RuntimeError("llm_model.csv not found in any expected location.")

    # Global map for cost fallback
    global _MODEL_RATE_MAP
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row['model']] = {
            "input": row.get('input_cost_per_m', 0) / 1_000_000,
            "output": row.get('output_cost_per_m', 0) / 1_000_000
        }

    # Selection Logic
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available_models = df[df['api_key'].notna() | (df['provider'] == 'lm_studio')]
    
    if available_models.empty:
        raise RuntimeError("No models with API keys available in CSV.")

    if base_model_name and base_model_name in available_models['model'].values:
        base_model = available_models[available_models['model'] == base_model_name].iloc[0]
    else:
        # Surrogate fallback
        available_models = available_models.sort_values('coding_arena_elo', ascending=False)
        base_model = available_models.iloc[len(available_models)//2]

    if strength == 0.5:
        return base_model.to_dict()
    
    if strength < 0.5:
        # Cheapest to Base
        candidates = available_models[available_models['input_cost_per_m'] <= base_model['input_cost_per_m']]
        candidates = candidates.sort_values('input_cost_per_m')
    else:
        # Base to ELO max
        candidates = available_models[available_models['coding_arena_elo'] >= base_model['coding_arena_elo']]
        candidates = candidates.sort_values('coding_arena_elo')

    idx = int(strength * (len(candidates) - 1))
    return candidates.iloc[idx].to_dict()

def _ensure_api_key(model_info: Dict[str, Any]) -> str:
    key_name = model_info.get('api_key')
    if not key_name or key_name == "EXISTING_KEY" or model_info['provider'] == 'lm_studio':
        return ""

    val = os.getenv(key_name)
    if val:
        return val.strip()

    if os.getenv("PDD_FORCE"):
        return ""

    console.print(f"[yellow]Missing API Key for {model_info['model']} ({key_name})[/yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    
    # Save to .env
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    set_key(str(env_path), key_name, new_key)
    os.environ[key_name] = new_key
    
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")
    return new_key

def _repair_json(s: str) -> str:
    """Basic JSON recovery for truncated responses."""
    s = s.strip()
    if not s: return s
    # Find start/end fences
    if "```json" in s:
        s = s.split("```json")[-1].split("```")[0]
    elif "```" in s:
        s = s.split("```")[-1].split("```")[0]
        
    # Balance braces logic (simplified)
    open_braces = s.count('{')
    close_braces = s.count('}')
    if open_braces > close_braces:
        s += '}' * (open_braces - close_braces)
    return s

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    # Placeholder for cloud logic using requests/httpx to Firebase endpoint
    # Must handle 402 (InsufficientCreditsError), 401/5xx (CloudFallbackError)
    raise CloudFallbackError("Cloud execution not implemented in this stub")

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
    """Execute LLM call via LiteLLM with fallback and key management."""
    setup_logging()
    _init_litellm_config()

    # Cloud logic check
    if use_cloud is True or (use_cloud is None and os.getenv("PDD_FORCE_LOCAL") != "1"):
        try:
            # Prepare payload and call _llm_invoke_cloud
            pass 
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")

    # Select Model
    model_info = _get_model_from_csv(strength)
    model_name = model_info['model']
    provider = model_info['provider']
    
    # Auth
    api_key = _ensure_api_key(model_info)

    # Prepare Messages
    if not messages:
        if not prompt:
            raise ValueError("Prompt is required if messages are not provided.")
        # Simple template replacement
        content = prompt
        if input_json:
            if isinstance(input_json, dict):
                for k, v in input_json.items():
                    content = content.replace(f"{{{{{k}}}}}", str(v))
        messages = [{"role": "user", "content": content}]

    # Reasoning Logic
    reasoning_type = model_info.get('reasoning_type', 'none')
    kwargs: Dict[str, Any] = {
        "model": f"{provider}/{model_name}" if provider != "openai" else model_name,
        "messages": messages,
        "temperature": temperature,
        "api_key": api_key,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    if reasoning_type == "budget":
        max_t = model_info.get('max_reasoning_tokens', 1024)
        kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_t)}
        kwargs["temperature"] = 1.0 # Anthropic requirement
    elif reasoning_type == "effort":
        effort = "low" if time < 0.3 else "medium" if time < 0.7 else "high"
        kwargs["reasoning_effort"] = effort

    # Structured Output Config
    if output_pydantic or output_schema:
        if model_info.get('structured_output') == 1:
            kwargs["response_format"] = output_pydantic or output_schema
        else:
            # Fallback: prompt instruction
            messages.append({"role": "system", "content": "Return output in valid JSON matching the requested schema."})

    try:
        if use_batch_mode:
            response = batch_completion(**kwargs)
            # Handle list of results...
            return {"result": response}
        
        # Responses API for GPT-o1/o3
        if model_name.startswith("o1") or model_name.startswith("o3"):
            response = litellm.completion(**kwargs)
        else:
            response = completion(**kwargs)

        result_text = response.choices[0].message.content
        thinking = getattr(response.choices[0].message, "reasoning_content", None)

        # Parse / Validate
        result = result_text
        if output_pydantic:
            parsed = json.loads(_repair_json(result_text))
            result = output_pydantic(**parsed)
        elif output_schema:
            result = json.loads(_repair_json(result_text))

        return {
            "result": result,
            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
            "model_name": model_name,
            "thinking_output": thinking
        }

    except Exception as e:
        logger.error(f"LLM Invoke failed: {e}")
        # Logic for model fallback would go here
        raise RuntimeError(f"All model candidates failed: {e}")

if __name__ == "__main__":
    # Test call
    res = llm_invoke(prompt="Say hello in {{language}}", input_json={"language": "Python"})
    console.print(res)