from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import completion, batch_completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as required
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from pydantic import BaseModel

# Constants
LLM_CALL_TIMEOUT = 120
PDD_LOG_NAME = "pdd.llm_invoke"
console = Console()

# Global state for cost tracking
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# Exception Classes
class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic/Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable errors that trigger a fallback to local LLM."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required."""
    pass

# --- Logging Setup ---

def setup_file_logging():
    """Configures rotating file handlers (10MB, 5 backups)."""
    from logging.handlers import RotatingFileHandler
    log_file = Path.cwd() / "pdd_llm.log"
    handler = RotatingFileHandler(log_file, maxBytes=10 * 1024 * 1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    
    logger = logging.getLogger(PDD_LOG_NAME)
    logger.addHandler(handler)
    
    litellm_logger = logging.getLogger("litellm")
    litellm_logger.addHandler(handler)

def set_verbose_logging(verbose: bool):
    """Toggles DEBUG level."""
    level = logging.DEBUG if verbose else logging.INFO
    logging.getLogger(PDD_LOG_NAME).setLevel(level)

def _configure_loggers():
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    llm_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        llm_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"

    logging.basicConfig(level=logging.WARNING)
    logging.getLogger(PDD_LOG_NAME).setLevel(pdd_level)
    logging.getLogger("litellm").setLevel(llm_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- Path & Model CSV Handling ---

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    
    search_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    
    for path in search_paths:
        if path.exists():
            df = pd.read_csv(path)
            # Cache rates for fallback
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    "input": row.get('input_cost_per_m', 0) / 1_000_000,
                    "output": row.get('output_cost_per_m', 0) / 1_000_000
                }
            return df
    raise FileNotFoundError("Could not locate llm_model.csv")

# --- Key Management ---

def _manage_api_key(key_name: str, provider: str) -> bool:
    """Interactively fetches and saves missing API keys."""
    current_val = os.getenv(key_name)
    if current_val and current_val not in ["", "EXISTING_KEY", "lm-studio"]:
        return True
    
    if provider.lower() == "lm-studio":
        os.environ[key_name] = "lm-studio"
        return True

    if os.getenv("PDD_FORCE"):
        return False

    console.print(f"[bold yellow]Missing API Key for {provider} ({key_name})[/bold yellow]")
    new_key = console.input(f"Enter {key_name}: ").strip()
    
    # Sanitize for WSL/Carriage returns
    new_key = new_key.replace("\r", "").replace("\n", "")
    
    if not new_key:
        return False

    os.environ[key_name] = new_key
    
    # Save to .env
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    set_key(str(env_path), key_name, new_key)
    
    console.print(f"[cyan]Key saved to {env_path}. Ensure this file is .gitignored![/cyan]")
    return True

# --- Structured Output Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for prop in props.values():
            _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for prop in schema.get("properties", {}).values():
            _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _add_additional_properties_false(d)

# --- Repair Logic ---

def _repair_python_syntax(code: str) -> str:
    """Basic fixes for truncated code or common LLM syntax errors."""
    code = code.strip()
    if code.count('"""') % 2 != 0:
        code += '\n"""'
    if code.count("'''") % 2 != 0:
        code += "\n'''"
    return code

def _smart_unescape_code(text: str) -> str:
    """Fixes double escaped newlines in code fields."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

# --- Cloud Invocation ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["title"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Calls the PDD Cloud llmInvoke endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=300)
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if response.status_code in [401, 403]:
            raise CloudFallbackError("Cloud authentication/approval error.")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {str(e)}")

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
    Main entry point for running LLM prompts with LiteLLM and PDD logic.
    """
    _configure_loggers()
    set_verbose_logging(verbose)
    logger = logging.getLogger(PDD_LOG_NAME)

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is None:
        use_cloud = not force_local # Simplified logic for example

    if use_cloud and not os.getenv("_PDD_INTERNAL_CLOUD_CALL"):
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
            if output_pydantic:
                res["result"] = output_pydantic.model_validate(res["result"])
            return res
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Path
    df_models = _load_model_csv()
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter by API key availability
    available_models = []
    for _, row in df_models.iterrows():
        if _manage_api_key(row['api_key'], row['provider']):
            available_models.append(row)
    
    if not available_models:
        raise RuntimeError("No models available with valid API keys.")

    # Model Interpolation Logic
    df_avail = pd.DataFrame(available_models)
    base_row = df_avail[df_avail['model'] == base_model_name]
    if base_row.empty:
        base_row = df_avail.iloc[0:1] # Fallback surrogate

    if strength == 0.5:
        candidates = base_row.to_dict('records')
    elif strength < 0.5:
        # Interpolate by cost (cheapest to base)
        df_range = df_avail[df_avail['input_cost_per_m'] <= base_row.iloc[0]['input_cost_per_m']]
        candidates = df_range.sort_values('input_cost_per_m', ascending=False).to_dict('records')
    else:
        # Interpolate by ELO (base to highest)
        df_range = df_avail[df_avail['coding_arena_elo'] >= base_row.iloc[0]['coding_arena_elo']]
        candidates = df_range.sort_values('coding_arena_elo', ascending=True).to_dict('records')

    # Prepare Messages
    if not messages:
        # Simple templating
        final_prompt = prompt or ""
        if isinstance(input_json, dict):
            for k, v in input_json.items():
                final_prompt = final_prompt.replace(f"{{{{{k}}}}}", str(v))
        msgs = [{"role": "user", "content": final_prompt}]
    else:
        msgs = messages

    # 3. Invocation Loop (Fallbacks)
    last_err = None
    for model_info in candidates:
        try:
            model_id = model_info['model']
            provider = model_info['provider']
            
            # Setup Reasoning
            reasoning_args = {}
            r_type = model_info.get('reasoning_type', 'none')
            max_r = model_info.get('max_reasoning_tokens', 0)
            
            if r_type == 'budget':
                budget = int(time * max_r)
                if "anthropic" in provider.lower():
                    reasoning_args["thinking"] = {"type": "enabled", "budget_tokens": budget}
                    temperature = 1.0 # Required for Anthropic thinking
            elif r_type == 'effort':
                effort = "medium"
                if time < 0.3: effort = "low"
                elif time > 0.7: effort = "high"
                reasoning_args["reasoning_effort"] = effort

            # Structured Output
            resp_format = None
            if output_pydantic or output_schema:
                schema = output_schema or _pydantic_to_json_schema(output_pydantic)
                if model_info.get('structured_output'):
                    resp_format = {
                        "type": "json_schema",
                        "json_schema": {"name": "pdd_output", "strict": True, "schema": schema}
                    }

            # API Call
            call_kwargs = {
                "model": model_id,
                "messages": msgs,
                "temperature": temperature,
                "timeout": LLM_CALL_TIMEOUT,
                "num_retries": 2,
                "response_format": resp_format,
                **reasoning_args
            }

            # Vertex specific
            if "vertex" in provider.lower():
                call_kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
                call_kwargs["vertex_location"] = model_info.get("location") or os.getenv("VERTEX_LOCATION")

            # Execute
            if "gpt-5" in model_id: # Placeholder for Responses API logic
                # responses() logic here
                response = completion(**call_kwargs)
            elif use_batch_mode:
                response = batch_completion(**call_kwargs)
            else:
                response = completion(**call_kwargs)

            # Extract Result
            raw_content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, 'reasoning_content', None)
            
            result = raw_content
            if output_pydantic or output_schema:
                try:
                    # Logic to parse/repair JSON if content is string
                    parsed = json.loads(raw_content)
                    if output_pydantic:
                        result = output_pydantic.model_validate(parsed)
                    else:
                        result = parsed
                except Exception as e:
                    raise SchemaValidationError(f"JSON/Schema validation failed: {e}")

            return {
                "result": result,
                "cost": completion_cost(response),
                "model_name": model_id,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.warning(f"Model {model_info['model']} failed: {e}")
            last_err = e
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_err}")

if __name__ == "__main__":
    # Example usage
    load_dotenv()
    setup_file_logging()
    try:
        out = llm_invoke(prompt="Say hello to {{name}}", input_json={"name": "World"}, verbose=True)
        console.print(out)
    except Exception as exc:
        console.print(f"[red]Error: {exc}[/red]")