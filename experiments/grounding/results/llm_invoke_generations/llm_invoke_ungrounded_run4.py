from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports (as per requirement)
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from pydantic import BaseModel

# Configuration and Constants
LLM_CALL_TIMEOUT = 120
LITELLM_CACHE_FILE = "litellm_cache.sqlite"
CONSOLE = Console()

# Global state for cost tracking via callbacks
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# Logging Setup
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

def setup_logging():
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    env = os.getenv("PDD_ENVIRONMENT", "production").lower()
    verbose = os.getenv("PDD_VERBOSE_LOGGING") == "1"

    logging.basicConfig(level=log_level)
    
    if env == "production":
        litellm_logger.setLevel(logging.WARNING)
    else:
        litellm_logger.setLevel(os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper())

    if verbose:
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)

def set_verbose_logging(enabled: bool = True):
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)

# Exceptions
class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable errors that trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud-side errors."""
    pass

class InsufficientCreditsError(Exception):
    """Raised when 402 Payment Required is returned by Cloud."""
    pass

# Helper Utilities
def _is_wsl() -> bool:
    return "microsoft-standard" in Path("/proc/version").read_text().lower() if Path("/proc/version").exists() else False

def _sanitize_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        properties = schema.get("properties", {})
        if properties:
            schema["required"] = list(properties.keys())
        for prop in properties.values():
            _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for prop in schema.get("properties", {}).values():
            _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

def _repair_truncated_json(text: str) -> str:
    text = text.strip()
    if not text: return text
    # Simple heuristic to close unclosed objects/arrays
    opens = {"{": 0, "[": 0}
    for char in text:
        if char == "{": opens["{"] += 1
        elif char == "}": opens["{"] -= 1
        elif char == "[": opens["["] += 1
        elif char == "]": opens["["] -= 1
    
    text += "]" * max(0, opens["["])
    text += "}" * max(0, opens["{"])
    return text

def _smart_unescape_code(text: str) -> str:
    # Unescape double-escaped newlines only if likely inside a string block
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _repair_python_syntax(code: str) -> str:
    # Remove trailing quotes or incomplete blocks often seen in truncated LLM outputs
    code = code.strip()
    if (code.count('"""') % 2) != 0: code += '"""'
    if (code.count("'''") % 2) != 0: code += "'''"
    return code

# Cloud Invocation Logic
def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    try:
        response = requests.post(
            url, 
            json=payload, 
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits for cloud execution.")
        if response.status_code in [401, 403]:
            # Clear cache placeholder logic
            raise CloudFallbackError(f"Cloud Auth Error: {response.status_code}")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {response.status_code}")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud Network Error: {str(e)}")

# Core Functionality
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
    """Execute a prompt using LiteLLM with fallback logic, cloud support, and key management."""
    
    setup_logging()
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    load_dotenv(project_root / ".env")

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is True or (use_cloud is None and not force_local):
        try:
            payload = {
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
            cloud_res = _llm_invoke_cloud(payload)
            
            # Re-validate result if pydantic model provided
            result_data = cloud_res["result"]
            if output_pydantic and isinstance(result_data, (dict, str)):
                if isinstance(result_data, str):
                    result_data = json.loads(result_data)
                result_data = output_pydantic.model_validate(result_data)
            
            return {
                "result": result_data,
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName", "cloud-redirect"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            if use_cloud is True:
                raise # If forced cloud, don't fall back silently
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")

    # 2. Local Execution Setup
    # Resolve CSV
    csv_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    df = None
    for p in csv_paths:
        if p.exists():
            df = pd.read_csv(p)
            break
    
    if df is None:
        raise RuntimeError("llm_model.csv not found in any expected location.")

    # Model Selection Logic
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available_df = df.copy()
    
    # Filter by API key availability (interactive check handled later)
    # strength interpolation
    base_model_row = available_df[available_df['model'] == default_model_name]
    if base_model_row.empty:
        base_model_row = available_df.iloc[[0]] # surrogate
    
    base_elo = base_model_row['coding_arena_elo'].values[0]
    base_cost = base_model_row['input_cost_per_m'].values[0]

    if strength < 0.5:
        # Lower cost models
        candidates = available_df[available_df['input_cost_per_m'] <= base_cost].sort_values('input_cost_per_m')
    elif strength > 0.5:
        # Higher ELO models
        candidates = available_df[available_df['coding_arena_elo'] >= base_elo].sort_values('coding_arena_elo', ascending=False)
    else:
        candidates = base_model_row

    # 3. Iterative Invocation (Fallback Loop)
    for _, model_row in candidates.iterrows():
        model_name = model_row['model']
        provider = model_row['provider']
        key_env_var = model_row['api_key']
        
        # API Key Management
        api_key = os.getenv(key_env_var)
        is_new_key = False
        
        if not api_key and key_env_var not in ["", "EXISTING_KEY", "nan"]:
            if os.getenv("PDD_FORCE"):
                continue
            CONSOLE.print(f"[bold cyan]Missing API key for {provider} ({key_env_var}).[/bold cyan]")
            api_key = _sanitize_key(input(f"Enter {key_env_var}: "))
            set_key(str(project_root / ".env"), key_env_var, api_key)
            os.environ[key_env_var] = api_key
            is_new_key = True
            logger.warning(f"Security: API key for {provider} saved to .env")

        # Formatting Messages
        if messages:
            final_messages = messages
        else:
            # Simple template rendering logic
            rendered_prompt = prompt
            if input_json and isinstance(input_json, dict):
                for k, v in input_json.items():
                    rendered_prompt = rendered_prompt.replace(f"{{{{{k}}}}}", str(v))
            final_messages = [{"role": "user", "content": rendered_prompt}]

        # Reasoning & Extra Params
        kwargs = {
            "model": model_name,
            "messages": final_messages,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
            "api_key": api_key
        }

        # Handle Reasoning
        r_type = str(model_row.get('reasoning_type', 'none')).lower()
        max_r_tokens = model_row.get('max_reasoning_tokens', 0)
        
        if r_type == 'budget':
            budget = int(time * max_r_tokens)
            if "anthropic" in provider.lower():
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                kwargs["temperature"] = 1.0 # Required for Anthropic thinking
        elif r_type == 'effort':
            effort = "medium"
            if time < 0.3: effort = "low"
            elif time > 0.7: effort = "high"
            
            if "gpt-5" in model_name: # Placeholder check for next-gen OpenAI
                kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                kwargs["reasoning_effort"] = effort

        # Structured Output
        if output_pydantic or output_schema:
            if model_row.get('structured_output') == 1:
                if "gpt" in model_name:
                    schema_to_use = output_schema or _pydantic_to_json_schema(output_pydantic)
                    kwargs["response_format"] = {
                        "type": "json_schema",
                        "json_schema": {"name": "pdd_output", "schema": schema_to_use, "strict": True}
                    }
            elif "groq" in provider.lower():
                kwargs["response_format"] = {"type": "json_object"}
                final_messages[0]["content"] += f"\nReturn valid JSON matching: {output_schema or output_pydantic.model_json_schema()}"

        # 4. LiteLLM Call
        try:
            if "gpt-5" in model_name: # Use responses API for O1/Next-gen logic
                response = litellm.responses(**kwargs)
            elif use_batch_mode:
                response = batch_completion(**kwargs)
            else:
                response = completion(**kwargs)

            # Extract result
            raw_content = response.choices[0].message.content
            
            # Post-processing JSON
            if output_pydantic or output_schema:
                try:
                    # Clean content
                    if "```json" in raw_content:
                        raw_content = raw_content.split("```json")[1].split("```")[0]
                    
                    data = json.loads(raw_content)
                    if output_pydantic:
                        parsed = output_pydantic.model_validate(data)
                        result = parsed
                    else:
                        result = data
                except Exception as e:
                    # Repair attempts
                    repaired = _repair_truncated_json(raw_content)
                    data = json.loads(repaired)
                    result = output_pydantic.model_validate(data) if output_pydantic else data

            else:
                result = raw_content

            # Cost calculation
            cost = completion_cost(response)
            
            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": getattr(response.choices[0].message, "reasoning_content", None)
            }

        except Exception as e:
            logger.error(f"Error with model {model_name}: {e}")
            if "AuthenticationError" in str(e) and is_new_key:
                # Retry once after re-prompting for key
                CONSOLE.print("[red]Authentication failed with the provided key. Please try again.[/red]")
                os.environ.pop(key_env_var, None)
                return llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic, output_schema, time, use_batch_mode, messages, language, use_cloud)
            
            continue # Try next candidate in the fallback loop

    raise RuntimeError("Exhausted all LLM candidates without a successful response.")

if __name__ == "__main__":
    # Example usage
    res = llm_invoke(prompt="Say hello to {{name}}", input_json={"name": "PDD Engineer"}, strength=0.5)
    print(res)