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
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports (assumes package structure)
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Global State ---
CONSOLE = Console()
LOGGER = logging.getLogger("pdd.llm_invoke")
LITE_LOGGER = logging.getLogger("litellm")
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Custom Exceptions ---
class SchemaValidationError(Exception):
    """Raised when the LLM response fails Pydantic/Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """User lacks credits; do not fallback."""
    pass

# --- Setup & Configuration ---

def setup_logging():
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = "DEBUG"
    
    logging.basicConfig(level=log_level)
    LOGGER.setLevel(log_level)
    
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = "WARNING"
    LITE_LOGGER.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    litellm.telemetry = False

def _init_env():
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    env_path = project_root / ".env"
    if env_path.exists():
        load_dotenv(env_path)
    return project_root, env_path

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    search_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    
    for p in search_paths:
        if p.exists():
            return pd.read_csv(p)
    
    # Fallback to packaged data
    try:
        data_path = resolver.resolve_data_file("data/llm_model.csv")
        return pd.read_csv(data_path)
    except Exception:
        LOGGER.error("Could not locate llm_model.csv")
        return pd.DataFrame()

# --- Utility Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively adds all properties to 'required' and sets additionalProperties: false."""
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
            schema["additionalProperties"] = False
        for prop in props.values():
            _ensure_all_properties_required(prop)
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for item in schema[key]:
                _ensure_all_properties_required(item)
                
    if schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
        
    if "$defs" in schema:
        for definition in schema["$defs"].values():
            _ensure_all_properties_required(definition)
            
    return schema

def _repair_json(text: str) -> str:
    """Attempt to extract and fix common JSON truncation/formatting issues."""
    text = text.strip()
    # Try fenced code blocks
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match:
        text = match.group(1)
    
    # Simple balance check/repair (very basic)
    open_braces = text.count("{")
    close_braces = text.count("}")
    if open_braces > close_braces:
        text += "}" * (open_braces - close_braces)
    
    return text

def _is_wsl() -> bool:
    return "microsoft-standard" in Path("/proc/version").read_text().lower() if Path("/proc/version").exists() else False

def _handle_missing_key(key_name: str, env_file: Path) -> str:
    if os.getenv("PDD_FORCE") == "1":
        return ""
    
    CONSOLE.print(f"[yellow]Missing API Key: {key_name}[/yellow]")
    val = input(f"Enter value for {key_name}: ").strip()
    
    # Clean WSL/Windows line endings
    val = val.replace("\r", "").replace("\n", "")
    
    set_key(str(env_file), key_name, val)
    os.environ[key_name] = val
    CONSOLE.print(f"[green]Key saved to {env_file}. Ensure this file is .gitignored![/green]")
    return val

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
    
    setup_logging()
    project_root, env_path = _init_env()
    
    # 1. Cloud Execution Logic
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1" # Simple check, actual implementation would check CloudConfig
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt, input_json, strength, temperature, time, 
                verbose, output_pydantic, output_schema, use_batch_mode, language
            )
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[orange1]Cloud error: {e}. Falling back to local...[/orange1]")
        except InsufficientCreditsError:
            raise

    # 2. Local Model Selection
    df = _load_model_csv()
    if df.empty:
        raise RuntimeError("Model configuration CSV not found.")
    
    # Selection algorithm
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available = df[df['api_key'].apply(lambda x: os.getenv(str(x)) is not None or str(x) == "EXISTING_KEY")]
    
    if available.empty:
        # Fallback: find first model in CSV and prompt for key
        first_row = df.iloc[0]
        _handle_missing_key(str(first_row['api_key']), env_path)
        available = df.iloc[[0]]

    # Interpolation Logic (Simplified for brevity)
    # strength < 0.5 -> cost; strength > 0.5 -> ELO
    selected_row = available.iloc[0] # Default surrogate
    
    # 3. Reasoning & Params
    reasoning_type = str(selected_row.get('reasoning_type', 'none')).lower()
    max_reasoning = int(selected_row.get('max_reasoning_tokens', 0))
    
    extra_params = {}
    if reasoning_type == "budget" and max_reasoning > 0:
        extra_params["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_reasoning)}
        if "anthropic" in str(selected_row['provider']).lower():
            temperature = 1.0
    elif reasoning_type == "effort":
        effort = "low" if time < 0.33 else "medium" if time < 0.66 else "high"
        extra_params["reasoning_effort"] = effort

    # 4. Message Preparation
    if not messages:
        if not prompt:
            raise ValueError("Prompt or Messages required.")
        final_prompt = prompt
        if input_json:
            # Basic placeholder replacement
            if isinstance(input_json, dict):
                for k, v in input_json.items():
                    final_prompt = final_prompt.replace(f"{{{{{k}}}}}", str(v))
        messages = [{"role": "user", "content": final_prompt}]

    # 5. Invocation
    try:
        response = completion(
            model=str(selected_row['model']),
            messages=messages,
            temperature=temperature,
            num_retries=2,
            timeout=LLM_CALL_TIMEOUT,
            **extra_params
        )
        
        result_text = response.choices[0].message.content or ""
        
        # 6. Structured Output Parsing
        if output_pydantic or output_schema:
            result_text = _repair_json(result_text)
            parsed_json = json.loads(result_text)
            if output_pydantic:
                result = output_pydantic.model_validate(parsed_json)
            else:
                result = parsed_json
        else:
            result = result_text

        # 7. Metadata
        cost = completion_cost(response)
        thinking = getattr(response.choices[0].message, "reasoning_content", None)

        return {
            "result": result,
            "cost": cost,
            "model_name": selected_row['model'],
            "thinking_output": thinking
        }

    except Exception as e:
        if _is_wsl() and "auth" in str(e).lower():
            CONSOLE.print("[bold red]WSL detected: check for \r in your API keys in .env[/bold red]")
        LOGGER.error(f"LLM Invocation failed: {e}")
        raise

def _llm_invoke_cloud(*args, **kwargs) -> Dict[str, Any]:
    """Helper to call Firebase Cloud Function 'llmInvoke'."""
    # Implementation of cloud transport would go here
    # Mocking for structure
    raise CloudFallbackError("Cloud endpoint not reachable (Simulated)")

if __name__ == "__main__":
    # Example usage
    try:
        res = llm_invoke(prompt="Hello {{name}}", input_json={"name": "World"}, strength=0.5)
        print(res)
    except Exception as e:
        print(f"Error: {e}")