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
from pydantic import BaseModel
from rich.console import Console

# Internal package imports
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Logging Configuration ---
LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
VERBOSE = os.getenv("PDD_VERBOSE_LOGGING") == "1"
if VERBOSE:
    LOG_LEVEL = "DEBUG"

logger = logging.getLogger("pdd.llm_invoke")
logger.setLevel(LOG_LEVEL)

litellm_logger = logging.getLogger("litellm")
litellm_logger.setLevel(os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper())

litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

console = Console()

# Global state for cost tracking
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """User has no credits; do not fall back to local."""
    pass

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", None)
        cost = litellm.completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "cost": cost,
            "model": kwargs.get("model")
        }
    except Exception:
        pass

litellm.success_callback = [_success_callback]

def _get_model_candidates(strength: float) -> List[Dict[str, Any]]:
    """Selects and orders models from CSV based on strength/ELO/Cost."""
    resolver = get_default_resolver()
    csv_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        Path(resolver.resolve_project_root()) / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    
    df = None
    for p in csv_paths:
        if p.exists():
            df = pd.read_csv(p)
            break
            
    if df is None:
        raise FileNotFoundError("Could not find llm_model.csv")

    # Filter for models with API keys available or placeholder
    df["has_key"] = df["api_key"].apply(lambda k: os.getenv(str(k)) is not None or k == "EXISTING_KEY")
    
    # Store rates globally as fallback
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row["model"]] = {
            "input": row.get("input_cost", 0),
            "output": row.get("output_cost", 0)
        }

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_model = df[df["model"] == base_model_name].iloc[0] if base_model_name in df["model"].values else df.iloc[0]

    if strength == 0.5:
        candidates = df.sort_values(by="coding_arena_elo", ascending=False)
    elif strength < 0.5:
        # Interpolate by cost: cheapest to base
        candidates = df[df["input_cost"] <= base_model["input_cost"]].sort_values("input_cost")
    else:
        # Interpolate by ELO: base to highest
        candidates = df[df["coding_arena_elo"] >= base_model["coding_arena_elo"]].sort_values("coding_arena_elo", ascending=False)
        
    return candidates.to_dict("records")

def _handle_api_key(key_name: str) -> None:
    """Interactively fetches and saves missing API keys."""
    if not key_name or key_name == "EXISTING_KEY" or os.getenv(key_name):
        return

    if os.getenv("PDD_FORCE"):
        return

    console.print(f"[yellow]Missing API key for {key_name}.[/yellow]")
    key_val = input(f"Enter value for {key_name}: ").strip()
    
    # WSL Sanity
    if "wsl" in open("/proc/version").read().lower() or os.getenv("WSL_DISTRO_NAME"):
        key_val = key_val.replace("\r", "")

    os.environ[key_name] = key_val
    
    resolver = get_default_resolver()
    env_path = Path(resolver.resolve_project_root()) / ".env"
    set_key(str(env_path), key_name, key_val)
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for v in props.values():
            _ensure_all_properties_required(v)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])

def _repair_json(text: str) -> str:
    """Attempts to fix truncated or malformed JSON from LLM."""
    text = text.strip()
    if text.startswith("```json"):
        text = text.split("```json")[1].split("```")[0].strip()
    
    # Basic truncation repair
    if text.count("{") > text.count("}"):
        text += "}" * (text.count("{") - text.count("}"))
    return text

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
    
    # 1. Cloud Execution Path
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
        
    if use_cloud:
        try:
            # Note: Cloud implementation would use requests/httpx to call Firebase
            # Placeholder for cloud logic per requirements
            pass
        except CloudFallbackError as e:
            console.print(f"[bold yellow]Cloud Error: {e}. Falling back to local.[/bold yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution
    candidates = _get_model_candidates(strength)
    
    for model_row in candidates:
        model_name = model_row["model"]
        api_key_name = model_row["api_key"]
        
        _handle_api_key(api_key_name)
        
        # Build messages if not provided
        if not messages:
            content = prompt or ""
            if input_json:
                content += "\n\nInput Data: " + json.dumps(input_json)
            msgs = [{"role": "user", "content": content}]
        else:
            msgs = messages

        # Reasoning logic
        reasoning_type = model_row.get("reasoning_type", "none")
        max_r_tokens = int(model_row.get("max_reasoning_tokens", 0))
        extra_params = {}
        
        if reasoning_type == "budget":
            extra_params["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_r_tokens)}
            temperature = 1.0 # Required for Anthropic thinking
        elif reasoning_type == "effort":
            effort = "low" if time < 0.3 else "medium" if time < 0.7 else "high"
            extra_params["reasoning_effort"] = effort

        # Structured output logic
        if output_pydantic or output_schema:
            schema = output_schema or output_pydantic.model_json_schema()
            _ensure_all_properties_required(schema)
            if model_row.get("structured_output") == 1:
                extra_params["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": schema, "strict": True}}

        try:
            if "gpt-5" in model_name: # Surrogate for O1/O3 style
                response = litellm.responses(model=model_name, messages=msgs, **extra_params)
            elif use_batch_mode:
                response = litellm.batch_completion(model=model_name, messages=msgs, temperature=temperature, **extra_params)
            else:
                response = litellm.completion(model=model_name, messages=msgs, temperature=temperature, num_retries=2, timeout=120, **extra_params)

            # Process result
            res_obj = response[0] if isinstance(response, list) else response
            raw_content = res_obj.choices[0].message.content
            
            # JSON parsing if structured
            result = raw_content
            if output_pydantic or output_schema:
                try:
                    clean_json = _repair_json(raw_content)
                    parsed = json.loads(clean_json)
                    result = output_pydantic(**parsed) if output_pydantic else parsed
                except Exception as e:
                    logger.warning(f"Schema validation failed for {model_name}, falling back.")
                    continue

            thinking = getattr(res_obj.choices[0].message, "reasoning_content", None)
            
            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.error(f"Error invoking {model_name}: {e}")
            continue

    raise RuntimeError("All LLM candidates failed.")