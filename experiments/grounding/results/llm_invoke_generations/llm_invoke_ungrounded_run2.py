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
LLM_CALL_TIMEOUT = 120
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING")
PDD_ENVIRONMENT = os.getenv("PDD_ENVIRONMENT", "production")
PDD_VERBOSE = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"

# Global state for cost tracking
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger("pdd.llm_invoke")

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when the LLM response fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud errors that trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """Raised when user has no credits. Does NOT fall back."""
    pass

# --- Logging Setup ---

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    log_dir = Path.home() / ".pdd" / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "llm_invoke.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(enabled: bool = True):
    if enabled:
        logger.setLevel(logging.DEBUG)
        logging.getLogger("litellm").setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.INFO)

# --- Path & Model Resolution ---

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv",
    ]
    
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            # Cache rates for fallback
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    'input': row.get('input_cost_per_m', 0) / 1_000_000,
                    'output': row.get('output_cost_per_m', 0) / 1_000_000
                }
            return df
    raise FileNotFoundError("llm_model.csv not found in any resolved location.")

# --- API Key Management ---

def _handle_missing_key(key_name: str, provider: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
        
    val = os.getenv(key_name)
    if val and val != "EXISTING_KEY":
        return val

    console.print(f"[bold yellow]Missing API Key for {provider} ({key_name})[/bold yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    
    # WSL / Sanitize
    new_key = re.sub(r'[\r\n\t]', '', new_key)
    
    # Save to .env
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    env_path = root / ".env"
    
    if env_path.exists():
        content = env_path.read_text()
        # Remove commented versions and existing keys
        lines = [line for line in content.splitlines() if not line.strip().startswith(f"# {key_name}") and not line.strip().startswith(f"{key_name}=")]
        env_path.write_text("\n".join(lines) + f"\n{key_name}={new_key}\n")
    else:
        env_path.write_text(f"{key_name}={new_key}\n")
        
    os.environ[key_name] = new_key
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")
    return new_key

# --- Structured Output Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for p_val in props.values():
            _ensure_all_properties_required(p_val)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for item in schema[key]:
                _ensure_all_properties_required(item)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for p_val in props.values():
            _add_additional_properties_false(p_val)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

def _repair_json(raw: str) -> str:
    # Try to find JSON block
    match = re.search(r'```json\s*(.*?)\s*```', raw, re.DOTALL)
    if match:
        return match.group(1)
    # Simple balance attempt
    start = raw.find('{')
    end = raw.rfind('}')
    if start != -1 and end != -1:
        return raw[start:end+1]
    return raw

def _smart_unescape_code(text: str) -> str:
    # Fix double escaped newlines in strings
    return text.replace("\\\\n", "\\n")

# --- Cloud Execution ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    # Placeholder for Firebase/Cloud auth and request
    jwt_token = os.getenv("PDD_CLOUD_JWT")
    if not jwt_token:
        raise CloudFallbackError("No Cloud JWT found")
    
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    try:
        resp = requests.post(
            url, 
            json=payload, 
            headers={"Authorization": f"Bearer {jwt_token}"},
            timeout=300
        )
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in [401, 403]:
            # Clear cache placeholder
            raise CloudFallbackError(f"Cloud Auth error: {resp.text}")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {str(e)}")

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
    """
    Expert implementation of LLM invocation with LiteLLM, including selection logic,
    reasoning parameters, and Cloud/Local fallback.
    """
    load_dotenv(get_default_resolver().resolve_project_root() / ".env")
    
    if verbose:
        set_verbose_logging(True)

    # 1. Cloud Execution Logic
    if use_cloud is None:
        use_cloud = (os.getenv("PDD_FORCE_LOCAL") != "1")
    
    if use_cloud:
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
            cloud_res = _llm_invoke_cloud(cloud_payload)
            
            # Validation of cloud result if pydantic provided
            res_obj = cloud_res["result"]
            if output_pydantic and isinstance(res_obj, dict):
                cloud_res["result"] = output_pydantic.model_validate(res_obj)
                
            return {
                "result": cloud_res["result"],
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName", "unknown-cloud"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")

    # 2. Local Invocation Path
    df = _load_model_csv()
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter for available keys
    available_df = df.copy()
    # Logic to filter by key availability would go here
    
    # Interpolation Logic
    if base_model_name and base_model_name in available_df['model'].values:
        base_model = available_df[available_df['model'] == base_model_name].iloc[0]
    else:
        base_model = available_df.iloc[0]

    # Model Selection Strategy
    if strength == 0.5:
        candidates = [base_model]
    elif strength < 0.5:
        # Interpolate cost down
        candidates = available_df[available_df['input_cost_per_m'] <= base_model['input_cost_per_m']].sort_values('input_cost_per_m', ascending=False).to_dict('records')
    else:
        # Interpolate ELO up
        candidates = available_df[available_df['coding_arena_elo'] >= base_model['coding_arena_elo']].sort_values('coding_arena_elo').to_dict('records')

    # 3. Invocation Loop (Retries & Fallbacks)
    last_err = None
    for model_row in candidates:
        model_id = model_row['model']
        provider = model_row['provider']
        
        # Key check
        key_name = model_row.get('api_key')
        if key_name and key_name not in ["", "EXISTING_KEY"]:
            _handle_missing_key(key_name, provider)

        # Build Reasoning Params
        kwargs: Dict[str, Any] = {
            "model": model_id,
            "messages": messages or [{"role": "user", "content": prompt.format(**(input_json or {})) if prompt else ""}],
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        r_type = model_row.get('reasoning_type', 'none')
        max_r = model_row.get('max_reasoning_tokens', 0)
        
        if r_type == 'budget':
            budget = int(time * max_r)
            if "anthropic" in provider.lower():
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                kwargs["temperature"] = 1.0  # Anthropic requirement
        elif r_type == 'effort':
            effort = "medium"
            if time < 0.33: effort = "low"
            elif time > 0.66: effort = "high"
            kwargs["reasoning_effort"] = effort

        # Call API
        try:
            if "gpt-5" in model_id: # Theoretical future gpt-5 Responses API
                resp = litellm.responses(**kwargs)
            elif use_batch_mode:
                resp = batch_completion(**kwargs)
            else:
                resp = completion(**kwargs)

            # Extract Result
            content = resp.choices[0].message.content
            thinking = getattr(resp.choices[0].message, "reasoning_content", None)
            
            # 4. Structured Output handling
            final_result = content
            if output_pydantic or output_schema:
                try:
                    cleaned_json = _repair_json(content)
                    data = json.loads(cleaned_json)
                    if output_pydantic:
                        final_result = output_pydantic.model_validate(data)
                    else:
                        final_result = data
                except Exception as e:
                    logger.warning(f"Schema validation failed for {model_id}, retrying next model.")
                    continue

            # Cost calculation
            cost = completion_cost(resp) or 0.0
            
            return {
                "result": final_result,
                "cost": cost,
                "model_name": model_id,
                "thinking_output": thinking
            }

        except Exception as e:
            last_err = e
            logger.error(f"Error invoking {model_id}: {e}")
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_err}")

if __name__ == "__main__":
    # Quick test
    try:
        res = llm_invoke(prompt="Say hello in {{lang}}", input_json={"lang": "Python"}, strength=0.5)
        console.print(res)
    except Exception as e:
        console.print(f"[red]Execution failed: {e}[/red]")