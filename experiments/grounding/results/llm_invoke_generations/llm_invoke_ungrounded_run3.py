from __future__ import annotations

import os
import json
import logging
import re
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal imports per requirements
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# Constants
LLM_CALL_TIMEOUT = 120
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING")
IS_PRODUCTION = os.getenv("PDD_ENVIRONMENT") == "production"
PDD_VERBOSE = os.getenv("PDD_VERBOSE_LOGGING") == "1"

# Console for rich output
console = Console()

# Global state for cost tracking
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# Logger Setup
logger = logging.getLogger("pdd.llm_invoke")
lite_logger = logging.getLogger("litellm")

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation to trigger fallback."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (network, 5xx, auth)."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

def _setup_logging() -> None:
    level = logging.DEBUG if PDD_VERBOSE else getattr(logging, PDD_LOG_LEVEL.upper(), logging.INFO)
    logger.setLevel(level)
    
    llm_level = logging.WARNING if IS_PRODUCTION else getattr(logging, LITELLM_LOG_LEVEL.upper(), logging.WARNING)
    lite_logger.setLevel(llm_level)
    
    litellm.set_verbose = PDD_VERBOSE
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        resolver.resolve_data_file("llm_model.csv")
    ]
    
    for path in paths:
        if path.exists():
            df = pd.read_csv(path)
            # Populate rate map for fallback
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    'input': row.get('input_cost_per_m', 0) / 1_000_000,
                    'output': row.get('output_cost_per_m', 0) / 1_000_000
                }
            return df
    raise FileNotFoundError("Could not locate llm_model.csv")

def _handle_api_key(provider: str, key_name: str) -> str:
    key = os.getenv(key_name)
    if key and key != "EXISTING_KEY":
        return key.strip()

    if os.getenv("PDD_FORCE"):
        return ""

    console.print(f"[yellow]Missing API Key for {provider} ({key_name})[/yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    
    # Save to .env
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    set_key(str(env_path), key_name, new_key)
    os.environ[key_name] = new_key
    
    console.print(f"[bold red]SECURITY WARNING:[/bold red] Key saved to {env_path}")
    return new_key

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        properties = schema.get("properties", {})
        if properties:
            schema["required"] = list(properties.keys())
        for prop in properties.values():
            _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["allOf", "anyOf", "oneOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for prop in schema.get("properties", {}).values():
            _add_additional_properties_false(prop)
    if "$defs" in schema:
        for defn in schema["$defs"].values():
            _add_additional_properties_false(defn)

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
    _setup_logging()
    load_dotenv(get_default_resolver().resolve_project_root() / ".env")

    # 1. Cloud Execution Logic
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt=prompt, input_json=input_json, strength=strength,
                temperature=temperature, time=time, verbose=verbose,
                output_pydantic=output_pydantic, output_schema=output_schema,
                use_batch_mode=use_batch_mode, messages=messages, language=language
            )
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Selection
    df = _load_model_csv()
    available_models = df[df['api_key'].notna()].copy()
    
    # Simple interpolation logic for strength
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row = available_models[available_models['model'] == base_model_name]
    if base_row.empty:
        base_row = available_models.iloc[0:1]
    
    # Filter candidates (simplified selection)
    candidates = available_models.sort_values('coding_arena_elo', ascending=False).to_dict('records')
    
    for model_row in candidates:
        try:
            return _execute_local_call(model_row, prompt, input_json, messages, temperature, strength, time, output_pydantic, output_schema)
        except Exception as e:
            logger.warning(f"Model {model_row['model']} failed: {e}")
            continue
            
    raise RuntimeError("All LLM candidates exhausted.")

def _execute_local_call(row: Dict, prompt, input_json, messages, temp, strength, time, pydantic_cls, schema) -> Dict[str, Any]:
    # Key handling
    api_key = _handle_api_key(row['provider'], row['api_key'])
    
    # Prompt formatting
    if not messages:
        # Simple template replacement
        formatted_prompt = prompt
        if isinstance(input_json, dict):
            for k, v in input_json.items():
                formatted_prompt = formatted_prompt.replace(f"{{{{{k}}}}}", str(v))
        msgs = [{"role": "user", "content": formatted_prompt}]
    else:
        msgs = messages

    # Reasoning parameters
    kwargs: Dict[str, Any] = {
        "model": row['model'],
        "messages": msgs,
        "temperature": temp,
        "api_key": api_key,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT
    }

    # Model specific logic (OpenAI Responses vs Completion)
    if "gpt-4o" in row['model'] or "o1" in row['model']:
        # Simplified: Use standard completion for now as LiteLLM wraps Responses
        pass

    # Structured Output Setup
    if pydantic_cls or schema:
        if row.get('structured_output'):
            target_schema = schema or pydantic_cls.model_json_schema()
            _ensure_all_properties_required(target_schema)
            _add_additional_properties_false(target_schema)
            kwargs["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": target_schema, "strict": True}}

    response = completion(**kwargs)
    
    content = response.choices[0].message.content
    thinking = getattr(response.choices[0].message, "reasoning_content", None)
    
    # Final Result Construction
    result = content
    if pydantic_cls and content:
        # JSON Repair & Validation
        try:
            data = json.loads(content)
            result = pydantic_cls.model_validate(data)
        except Exception:
            # Fallback parsing logic would go here
            pass

    return {
        "result": result,
        "cost": completion_cost(response),
        "model_name": row['model'],
        "thinking_output": thinking
    }

def _llm_invoke_cloud(**kwargs) -> Dict[str, Any]:
    # Placeholder for cloud implementation using requests to Firebase
    # Must handle JWT auth, CloudFallbackError, etc.
    raise CloudFallbackError("Cloud endpoint not configured in this stub.")

if __name__ == "__main__":
    # Example usage
    res = llm_invoke(prompt="Hello, who are you?", strength=0.5)
    console.print(res)