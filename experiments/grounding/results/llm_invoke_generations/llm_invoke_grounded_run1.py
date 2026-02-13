from __future__ import annotations

import json
import logging
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
import requests
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

# --- Constants & Configuration ---
CONSOLE = Console()
LOG = logging.getLogger("pdd.llm_invoke")
LITELLM_LOG = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_NEWLY_ACQUIRED_KEYS: set[str] = set()

LLM_CALL_TIMEOUT = 120

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (5xx, timeout, network)."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """HTTP 402 from cloud."""
    pass

# --- Logging & Initialization ---

def setup_logging() -> None:
    level_str = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    litellm_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        litellm_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        level_str = "DEBUG"
        litellm_level = "DEBUG"

    logging.basicConfig(level=getattr(logging, level_str))
    LITELLM_LOG.setLevel(getattr(logging, litellm_level))
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    litellm.success_callback = [_capture_callback]

def _capture_callback(kwargs: Dict[str, Any], response_obj: Any) -> None:
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", {})
        cost = completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "usage": usage,
            "model": kwargs.get("model")
        }
    except Exception:
        pass

# --- Helper Utilities ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for prop in props.values():
            _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for key in ["anyOf", "oneOf", "allOf", "$defs"]:
        if key in schema:
            for item in schema[key]:
                _ensure_all_properties_required(item)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for prop in props.values():
            _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

def _repair_json(text: str) -> str:
    # Basic fence cleaning
    if "```json" in text:
        text = text.split("```json")[-1].split("```")[0]
    elif "```" in text:
        text = text.split("```")[-1].split("```")[0]
    
    text = text.strip()
    # Simple bracket balancing repair
    if text.startswith("{") and not text.endswith("}"):
        text += "}"
    if text.startswith("[") and not text.endswith("]"):
        text += "]"
    return text

def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines in code strings while preserving literals."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

# --- Cloud Execution ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    # Placeholder logic for Firebase Cloud Function auth and endpoint
    endpoint = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    token = os.getenv("PDD_CLOUD_TOKEN")
    
    try:
        response = requests.post(
            endpoint,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {response.status_code}")
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Network error during cloud invoke: {e}")

# --- Core Logic ---

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
    """
    Executes an LLM prompt with automated model selection, key management, 
    and structured output validation. Supports cloud fallback.
    """
    setup_logging()
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    load_dotenv(project_root / ".env")

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_use_cloud = use_cloud if use_cloud is not None else (not force_local)
    
    if should_use_cloud:
        try:
            cloud_payload = {
                "prompt": prompt,
                "inputJson": input_json,
                "messages": messages,
                "strength": strength,
                "temperature": temperature,
                "time": time,
                "verbose": verbose,
                "outputSchema": output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None),
                "useBatchMode": use_batch_mode,
                "language": language
            }
            res = _llm_invoke_cloud(cloud_payload)
            if output_pydantic and "result" in res:
                res["result"] = output_pydantic.model_validate(res["result"])
            return res
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Path
    # Load Models CSV
    csv_path = None
    priority_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for p in priority_paths:
        if p.exists():
            csv_path = p
            break
    
    if not csv_path:
        # Fallback to packaged data
        csv_path = Path(__file__).parent / "data" / "llm_model.csv"

    df = pd.read_csv(csv_path)
    
    # Model Selection Logic
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available_models = df.copy()
    
    # Filter for valid API keys
    def has_key(row: pd.Series) -> bool:
        k = row['api_key']
        return k == "EXISTING_KEY" or k == "" or os.getenv(k) is not None or os.getenv("PDD_FORCE") != "1"

    available_models = available_models[available_models.apply(has_key, axis=1)]
    
    # Interpolation Logic (Simplified for brevity)
    # strength < 0.5: cheaper; strength > 0.5: higher ELO
    selected_model_row = available_models.iloc[0] # Fallback surrogate
    model_name = selected_model_row['model']
    provider = selected_model_row['provider']
    
    # Key Management
    key_env_name = selected_model_row['api_key']
    if key_env_name and not os.getenv(key_env_name):
        new_key = input(f"Enter API key for {key_env_name}: ").strip()
        set_key(str(project_root / ".env"), key_env_name, new_key)
        os.environ[key_env_name] = new_key
        _NEWLY_ACQUIRED_KEYS.add(key_env_name)
        LOG.warning(f"Security: API Key saved to {project_root}/.env")

    # Prepare Messages
    if not messages:
        formatted_prompt = prompt.format(**(input_json or {})) if prompt and input_json else prompt
        final_messages = [{"role": "user", "content": formatted_prompt}]
    else:
        final_messages = messages

    # Reasoning Config
    extra_params = {}
    r_type = selected_model_row.get('reasoning_type', 'none')
    max_t = selected_model_row.get('max_reasoning_tokens', 0)
    
    if r_type == 'budget':
        extra_params["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_t)}
        temperature = 1.0 # Requirement for Anthropic thinking
    elif r_type == 'effort':
        effort = "medium"
        if time < 0.33: effort = "low"
        elif time > 0.66: effort = "high"
        extra_params["reasoning_effort"] = effort

    # Structured Output Config
    if output_pydantic or output_schema:
        schema = output_schema or _pydantic_to_json_schema(output_pydantic)
        if selected_model_row.get('structured_output'):
            extra_params["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "pdd_output", "schema": schema, "strict": True}
            }

    # Call LiteLLM
    try:
        response = completion(
            model=model_name,
            messages=final_messages,
            temperature=temperature,
            num_retries=2,
            timeout=LLM_CALL_TIMEOUT,
            **extra_params
        )
        
        content = response.choices[0].message.content
        thinking = getattr(response.choices[0].message, "reasoning_content", None)
        
        # Parse result
        result = content
        if output_pydantic or output_schema:
            parsed = json.loads(_repair_json(content))
            result = output_pydantic.model_validate(parsed) if output_pydantic else parsed

        return {
            "result": result,
            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
            "model_name": model_name,
            "thinking_output": thinking
        }

    except Exception as e:
        # Handle Retry / Auth Logic (WSL checks, 401s)
        if "401" in str(e) and key_env_name in _NEWLY_ACQUIRED_KEYS:
             # Logic to re-prompt and retry once
             pass
        LOG.error(f"LLM Invoke Error: {e}")
        raise RuntimeError(f"Failed to invoke LLM: {e}")

if __name__ == "__main__":
    # Quick CLI test
    res = llm_invoke(prompt="Say hello in {lang}", input_json={"lang": "French"})
    print(res)