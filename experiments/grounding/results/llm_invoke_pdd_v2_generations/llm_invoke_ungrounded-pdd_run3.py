from __future__ import annotations

import json
import logging
import logging.handlers
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

# Internal relative imports as per requirements
try:
    from . import DEFAULT_STRENGTH, EXTRACTION_STRENGTH
    from .path_resolution import get_default_resolver
except (ImportError, ValueError):
    # Fallbacks for standalone execution
    DEFAULT_STRENGTH = 0.5
    EXTRACTION_STRENGTH = 0.7
    def get_default_resolver():
        class Resolver:
            def resolve_project_root(self):
                return Path.cwd()
        return Resolver()

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING")
PDD_ENVIRONMENT = os.getenv("PDD_ENVIRONMENT", "production")
PDD_VERBOSE_LOGGING = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"
LITELLM_DROP_PARAMS = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}

# --- Custom Exceptions ---

class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable error (network, auth, 5xx) that allows falling back to local."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable error in cloud execution."""
    pass

class InsufficientCreditsError(Exception):
    """User has no credits. Should not fall back to local."""
    pass

# --- Setup & Initialization ---

def setup_logging() -> None:
    """Configure hierarchical logging for the package and LiteLLM."""
    level = logging.DEBUG if PDD_VERBOSE_LOGGING else getattr(logging, PDD_LOG_LEVEL.upper())
    logging.basicConfig(level=level)
    
    # LiteLLM logging
    ll_level = getattr(logging, LITELLM_LOG_LEVEL.upper())
    if PDD_ENVIRONMENT == "production" and not PDD_VERBOSE_LOGGING:
        ll_level = logging.WARNING
    litellm_logger.setLevel(ll_level)
    
    litellm.drop_params = LITELLM_DROP_PARAMS

def setup_file_logging(log_file: str = "pdd_llm.log") -> None:
    """Configures rotating file handlers (10MB, 5 backups)."""
    handler = logging.handlers.RotatingFileHandler(
        log_file, maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(enabled: bool = True) -> None:
    """Toggle DEBUG level logging."""
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    if enabled:
        litellm.set_verbose = True

# Initialize environment
resolver = get_default_resolver()
project_root = resolver.resolve_project_root()
load_dotenv(project_root / ".env" if project_root else None)
setup_logging()

# --- Callback Handler ---

def _litellm_success_callback(kwargs, response_obj, start_time, end_time):
    """Capture usage and cost data from LiteLLM calls."""
    global _LAST_CALLBACK_DATA
    try:
        model = kwargs.get("model", "unknown")
        cost = completion_cost(completion_response=response_obj)
        usage = getattr(response_obj, "usage", {})
        _LAST_CALLBACK_DATA = {
            "cost": cost or 0.0,
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.debug(f"Callback error: {e}")

litellm.success_callback = [_litellm_success_callback]

# --- Model & Key Management ---

def _load_model_csv() -> pd.DataFrame:
    """Resolve and load llm_model.csv in priority order."""
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv" if project_root else None,
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    for p in paths:
        if p and p.exists():
            return pd.read_csv(p)
    raise FileNotFoundError("llm_model.csv not found in any standard location.")

def _get_api_key_interactively(key_name: str) -> str:
    """Prompt user for missing API key and save to .env."""
    if os.getenv("PDD_FORCE"):
        return ""
    
    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name}")
    key_value = input(f"Enter value for {key_name}: ").strip()
    
    if key_value:
        # Sanitize for WSL
        key_value = key_value.replace("\r", "").replace("\n", "")
        os.environ[key_name] = key_value
        
        env_path = project_root / ".env" if project_root else Path.cwd() / ".env"
        # In-place update using python-dotenv logic
        set_key(str(env_path), key_name, key_value)
        
        console.print(f"[bold green]Security Warning:[/bold green] Key saved to {env_path}. Ensure this file is git-ignored.")
        return key_value
    return ""

def _select_models(strength: float) -> List[Dict[str, Any]]:
    """Select and rank models based on strength, ELO, and cost."""
    df = _load_model_csv()
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter for models where we have keys or keys aren't required
    available_indices = []
    for idx, row in df.iterrows():
        key_name = str(row['api_key'])
        if key_name in ["", "nan", "EXISTING_KEY", "LM_STUDIO"]:
            available_indices.append(idx)
        elif os.getenv(key_name):
            available_indices.append(idx)
        else:
            # Interactive check
            if not os.getenv("PDD_FORCE") and _get_api_key_interactively(key_name):
                available_indices.append(idx)

    df_avail = df.loc[available_indices].copy()
    if df_avail.empty:
        raise RuntimeError("No models available with valid API keys.")

    # Surrogate logic
    base_row = df_avail[df_avail['model'] == base_model_name]
    if base_row.empty:
        base_row = df_avail.iloc[0:1]
    
    base_elo = float(base_row['coding_arena_elo'].iloc[0])
    base_cost = float(base_row['input'].iloc[0]) + float(base_row['output'].iloc[0])

    if strength == 0.5:
        # Priority: Base, then higher ELOs
        candidates = df_avail.sort_values('coding_arena_elo', ascending=False)
    elif strength < 0.5:
        # Interpolate by cost from base down to cheapest
        candidates = df_avail[df_avail['input'] + df_avail['output'] <= base_cost].sort_values('input')
    else:
        # Interpolate by ELO from base up to highest
        candidates = df_avail[df_avail['coding_arena_elo'] >= base_elo].sort_values('coding_arena_elo', ascending=False)

    return candidates.to_dict('records')

# --- Formatting & Parsing Helpers ---

def _repair_json(text: str) -> str:
    """Attempt to fix truncated or poorly formatted JSON."""
    text = text.strip()
    if not text: return ""
    # Extract from code fences
    json_match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if json_match:
        text = json_match.group(1)
    
    # Basic truncation repair (close braces)
    open_braces = text.count('{') - text.count('}')
    if open_braces > 0:
        text += '}' * open_braces
    open_brackets = text.count('[') - text.count(']')
    if open_brackets > 0:
        text += ']' * open_brackets
    return text

def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines while preserving literals."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively enforce all properties in 'required' for strict schemas."""
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for k, v in props.items():
            _ensure_all_properties_required(v)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    return schema

def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively add additionalProperties: false for OpenAI strict mode."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for v in props.values():
            _add_additional_properties_false(v)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    return schema

# --- Cloud Execution ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    schema = _ensure_all_properties_required(schema)
    schema = _add_additional_properties_false(schema)
    schema["title"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Generic cloud bridge to llmInvoke endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")
    
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
    try:
        resp = requests.post(url, json=payload, timeout=300)
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in [401, 403]:
            # Possible expired token
            raise CloudFallbackError(f"Cloud Auth Error: {resp.status_code}")
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

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
    """
    Expert-level LLM invocation with ELO-based model selection, 
    structured output enforcement, and cloud/local fallback.
    """
    if verbose: set_verbose_logging(True)

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_use_cloud = use_cloud
    if should_use_cloud is None:
        should_use_cloud = not force_local and os.getenv("PDD_CLOUD_TOKEN") is not None

    if should_use_cloud:
        try:
            schema = output_schema
            if output_pydantic:
                schema = _pydantic_to_json_schema(output_pydantic)
            
            cloud_payload = {
                "prompt": prompt,
                "inputJson": input_json,
                "messages": messages,
                "strength": strength,
                "temperature": temperature,
                "time": time,
                "verbose": verbose,
                "outputSchema": schema,
                "useBatchMode": use_batch_mode,
                "language": language
            }
            cloud_res = _llm_invoke_cloud(cloud_payload)
            
            # Re-validate result if pydantic was expected
            result = cloud_res["result"]
            if output_pydantic and isinstance(result, dict):
                result = output_pydantic.model_validate(result)
            
            return {
                "result": result,
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName", "cloud"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud Warning:[/yellow] {e}. Falling back to local.")
            # Continue to local execution

    # 2. Local Execution Logic
    candidate_models = _select_models(strength)
    last_exception = None

    for model_meta in candidate_models:
        model_name = model_meta['model']
        provider = model_meta['provider']
        
        # Prepare params
        call_params: Dict[str, Any] = {
            "model": model_name,
            "temperature": temperature,
            "timeout": LLM_CALL_TIMEOUT,
            "num_retries": 2
        }

        # Reasoning Logic
        r_type = model_meta.get('reasoning_type', 'none')
        max_r = int(model_meta.get('max_reasoning_tokens', 0))
        
        if r_type == 'budget' and max_r > 0:
            budget = int(time * max_r)
            if "anthropic" in provider.lower():
                call_params["thinking"] = {"type": "enabled", "budget_tokens": budget}
                call_params["temperature"] = 1.0 # Requirement
        elif r_type == 'effort':
            effort = "medium"
            if time < 0.33: effort = "low"
            elif time > 0.66: effort = "high"
            call_params["reasoning_effort"] = effort

        # Structured Output
        is_strict = str(model_meta.get('structured_output', 'False')).lower() == 'true'
        final_messages = messages
        if not final_messages:
            content = prompt.format(**input_json) if input_json and isinstance(input_json, dict) else prompt
            final_messages = [{"role": "user", "content": content}]

        if is_strict:
            if output_pydantic:
                call_params["response_format"] = output_pydantic
            elif output_schema:
                call_params["response_format"] = {
                    "type": "json_schema", 
                    "json_schema": {"name": "output", "schema": output_schema, "strict": True}
                }

        # Invoke
        try:
            if use_batch_mode:
                # LiteLLM batch expects List[List[Dict]]
                resp = batch_completion(**call_params, messages=final_messages)
                results = [r.choices[0].message.content for r in resp]
                return {"result": results, "cost": sum(c.get("cost", 0) for c in [_LAST_CALLBACK_DATA]), "model_name": model_name}
            
            # Standard completion call
            resp = completion(**call_params, messages=final_messages)

            content = resp.choices[0].message.content
            thinking = getattr(resp.choices[0].message, "reasoning_content", None)
            
            # Post-processing
            if output_pydantic or output_schema:
                try:
                    parsed = json.loads(_repair_json(content))
                    if output_pydantic:
                        content = output_pydantic.model_validate(parsed)
                    else:
                        content = parsed
                except Exception as e:
                    raise SchemaValidationError(f"JSON validation failed: {e}")

            return {
                "result": content,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.warning(f"Model {model_name} failed: {e}")
            last_exception = e
            continue

    raise RuntimeError(f"All models failed. Last error: {last_exception}")

if __name__ == "__main__":
    # Simple test run
    try:
        res = llm_invoke(prompt="Say hello in {lang}", input_json={"lang": "Python"}, strength=0)
        console.print(res)
    except Exception as exc:
        console.print(f"[red]Error:[/red] {exc}")