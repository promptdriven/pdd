from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as per requirements
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    LLM_CALL_TIMEOUT,
    PDD_MODEL_DEFAULT,
)
from .path_resolution import get_default_resolver

# --- Global Configuration ---
console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_NEWLY_ACQUIRED_KEYS: set[str] = set()

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (5xx, timeout, network) -> Try local."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error (4xx except 402)."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Setup & Initialization ---

def setup_logging() -> None:
    level_name = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    level = getattr(logging, level_name, logging.INFO)
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        level = max(level, logging.WARNING)
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        level = logging.DEBUG

    logging.basicConfig(level=level)
    logger.setLevel(level)
    
    lt_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    litellm_logger.setLevel(getattr(logging, lt_level, logging.WARNING))
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    litellm.success_callback = [_capture_callback]

def _capture_callback(kwargs: Any, response_obj: Any) -> None:
    """LiteLLM callback to capture usage and cost."""
    try:
        usage = response_obj.get("usage", {})
        cost = litellm.completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA.update({
            "usage": usage,
            "cost": cost,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        })
    except Exception as e:
        logger.debug(f"Callback capture failed: {e}")

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    # Priority order as per requirements
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    
    # Finally, packaged data
    try:
        paths.append(resolver.resolve_data_file("llm_model.csv"))
    except Exception:
        pass

    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": row.get("input_cost_per_m", 0) / 1_000_000,
                    "output": row.get("output_cost_per_m", 0) / 1_000_000,
                }
            return df
    raise FileNotFoundError("llm_model.csv not found in search paths.")

# --- Utilities ---

def _ensure_api_key(provider: str, key_name: str) -> Optional[str]:
    """Interactively fetch and save missing API keys."""
    if key_name == "EXISTING_KEY" or not key_name:
        return None
        
    val = os.getenv(key_name)
    if val:
        return val.strip()

    if os.getenv("PDD_FORCE"):
        return None

    console.print(f"[bold yellow]Missing API key for {provider} ({key_name}).[/bold yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    
    # WSL / OS Sanity
    new_key = "".join(c for c in new_key if c.isprintable()).strip()
    
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    
    set_key(str(env_path), key_name, new_key)
    os.environ[key_name] = new_key
    _NEWLY_ACQUIRED_KEYS.add(key_name)
    
    console.print(f"[green]Key saved to {env_path}.[/green] [bold red]Security Note: Ensure .env is gitignored.[/bold red]")
    return new_key

def _repair_json(text: str) -> str:
    """Clean and repair common LLM JSON truncation/formatting issues."""
    text = text.strip()
    # Extract from fenced block
    if "```json" in text:
        text = text.split("```json")[-1].split("```")[0]
    elif "```" in text:
        text = text.split("```")[-1].split("```")[0]
        
    text = text.strip()
    # Basic truncation repair
    if text.startswith("{") and not text.endswith("}"):
        # Simple attempt: add closing braces
        open_braces = text.count("{")
        close_braces = text.count("}")
        text += "}" * (open_braces - close_braces)
        
    return text

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for p in props.values():
            _ensure_all_properties_required(p)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    # Handle composites
    for key in ["anyOf", "oneOf", "allOf", "$defs"]:
        if key in schema:
            if isinstance(schema[key], dict):
                for v in schema[key].values(): _ensure_all_properties_required(v)
            else:
                for item in schema[key]: _ensure_all_properties_required(item)

# --- Core Logic ---

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
    
    setup_logging()
    
    # Cloud Logic
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt, input_json, strength, temperature, verbose, 
                output_pydantic, output_schema, time, use_batch_mode, language
            )
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise
        except Exception as e:
            if use_cloud is True: # Force cloud mode
                raise CloudInvocationError(f"Cloud execution failed: {e}")
            logger.warning(f"Cloud invocation failed, trying local: {e}")

    # Local Logic
    df = _load_model_csv()
    df = df.sort_values("coding_arena_elo", ascending=False)
    
    # Filter candidates by API key presence or availability
    candidates = df.copy()
    
    # Select Model via Strength Interpolation
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row = candidates[candidates["model"] == base_model_name]
    if base_row.empty:
        base_row = candidates.head(1)
    
    target_row = base_row.iloc[0]
    if strength < 0.5:
        # Interpolate cost down
        candidates = candidates[candidates["input_cost_per_m"] <= target_row["input_cost_per_m"]]
        candidates = candidates.sort_values("input_cost_per_m", ascending=False)
    elif strength > 0.5:
        # Interpolate ELO up
        candidates = candidates[candidates["coding_arena_elo"] >= target_row["coding_arena_elo"]]
        candidates = candidates.sort_values("coding_arena_elo", ascending=True)

    # Simple selection from sorted candidates
    idx = int(strength * (len(candidates) - 1))
    selected_model_row = candidates.iloc[idx]
    
    # Prepare messages
    if not messages:
        formatted_prompt = prompt
        if input_json:
            # Simple template replacement
            if isinstance(input_json, dict):
                for k, v in input_json.items():
                    formatted_prompt = formatted_prompt.replace(f"{{{{{k}}}}}", str(v))
        messages = [{"role": "user", "content": formatted_prompt}]

    return _execute_local_call(selected_model_row, messages, temperature, time, output_pydantic, output_schema)

def _execute_local_call(
    model_row: pd.Series,
    messages: Any,
    temperature: float,
    time: float,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict],
) -> Dict[str, Any]:
    
    model = model_row["model"]
    provider = model_row["provider"]
    api_key_env = model_row["api_key"]
    
    api_key = _ensure_api_key(provider, api_key_env)
    
    params: Dict[str, Any] = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
        "api_key": api_key,
    }

    # Handle Reasoning
    reasoning_type = model_row.get("reasoning_type", "none")
    max_tokens = model_row.get("max_reasoning_tokens", 0)
    
    if reasoning_type == "budget" and max_tokens > 0:
        budget = int(time * max_tokens)
        params["thinking"] = {"type": "enabled", "budget_tokens": budget}
        params["temperature"] = 1.0 # Anthropic requirement
    elif reasoning_type == "effort":
        effort = "low" if time < 0.33 else "medium" if time < 0.66 else "high"
        params["reasoning_effort"] = effort

    # Handle Structured Output
    if output_pydantic or output_schema:
        schema = output_schema or output_pydantic.model_json_schema()
        _ensure_all_properties_required(schema)
        
        if model_row.get("structured_output"):
            params["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "output", "schema": schema, "strict": True}
            }
        else:
            # Fallback for models without native support
            messages[0]["content"] += f"\nReturn strictly valid JSON matching this schema: {json.dumps(schema)}"

    try:
        response = litellm.completion(**params)
        content = response.choices[0].message.content
        
        # Thinking extraction
        thinking = getattr(response.choices[0].message, "reasoning_content", None)
        if not thinking and hasattr(response, "_hidden_params"):
            thinking = response._hidden_params.get("thinking")

        result = content
        if output_pydantic or output_schema:
            parsed = json.loads(_repair_json(content))
            if output_pydantic:
                result = output_pydantic(**parsed)
            else:
                result = parsed

        return {
            "result": result,
            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
            "model_name": model,
            "thinking_output": thinking
        }

    except Exception as e:
        logger.error(f"LLM Call failed: {e}")
        # Logic for retry or key re-prompt would go here
        raise

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Any,
    strength: float,
    temperature: float,
    verbose: bool,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict],
    time: float,
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    """Client implementation for the llmInvoke cloud endpoint."""
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudInvocationError("PDD_CLOUD_TOKEN not found for cloud execution.")

    schema = output_schema
    if not schema and output_pydantic:
        schema = output_pydantic.model_json_schema()
        _ensure_all_properties_required(schema)

    payload = {
        "prompt": prompt,
        "inputJson": input_json,
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "outputSchema": schema,
        "useBatchMode": use_batch_mode,
        "language": language
    }

    try:
        resp = requests.post(
            url, 
            json=payload, 
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits for cloud execution.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {resp.status_code}")
        
        resp.raise_for_status()
        data = resp.json()
        
        # If we expect pydantic, wrap the dict result
        if output_pydantic and isinstance(data.get("result"), dict):
            data["result"] = output_pydantic(**data["result"])
            
        return {
            "result": data.get("result"),
            "cost": data.get("totalCost", 0.0),
            "model_name": data.get("modelName"),
            "thinking_output": data.get("thinkingOutput")
        }
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Network error in cloud invocation: {e}")