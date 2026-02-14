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
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
LITELLM_CACHE_FILE = "litellm_cache.sqlite"
CONSOLE = Console()
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Logging Setup ---
logger = logging.getLogger("pdd.llm_invoke")
lite_logger = logging.getLogger("litellm")

def setup_logging():
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = "DEBUG"
    
    logging.basicConfig(level=log_level)
    logger.setLevel(log_level)
    
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = "WARNING"
    lite_logger.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    litellm.telemetry = False

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler("pdd_llm.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

# --- Exceptions ---
class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic/Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud errors triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required from Cloud."""
    pass

# --- LiteLLM Callbacks ---
def _litellm_success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", None)
        cost = completion_cost(completion_response=response_obj)
        model = kwargs.get("model", "unknown")
        
        # Fallback to CSV rates if cost is 0 or None
        if (not cost or cost == 0) and model in _MODEL_RATE_MAP:
            rates = _MODEL_RATE_MAP[model]
            in_tokens = usage.prompt_tokens if usage else 0
            out_tokens = usage.completion_tokens if usage else 0
            cost = (in_tokens * rates['input'] / 1e6) + (out_tokens * rates['output'] / 1e6)

        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "cost": cost or 0.0,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.error(f"Callback error: {e}")

litellm.success_callback = [_litellm_success_callback]

# --- Helper Functions ---

def _get_project_root() -> Path:
    resolver = get_default_resolver()
    return Path(resolver.resolve_project_root())

def _load_env():
    root = _get_project_root()
    env_path = root / ".env"
    load_dotenv(dotenv_path=env_path)

def _get_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    priority_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        _get_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    
    for p in priority_paths:
        if p.exists():
            return pd.read_csv(p)
    
    # Fallback to packaged data
    try:
        pkg_csv = resolver.resolve_data_file("data/llm_model.csv")
        return pd.read_csv(pkg_csv)
    except Exception:
        raise FileNotFoundError("Could not locate llm_model.csv")

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
        props = schema.get("properties", {})
        for prop in props.values():
            _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    
    if "$defs" in schema:
        for definition in schema["$defs"].values():
            _add_additional_properties_false(definition)

def _repair_json(text: str) -> str:
    """Attempt to clean and repair truncated or malformed JSON."""
    text = text.strip()
    # Try to find JSON in fenced blocks
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match:
        text = match.group(1)
    
    # Simple bracket balancing repair
    open_braces = text.count('{')
    close_braces = text.count('}')
    if open_braces > close_braces:
        text += '}' * (open_braces - close_braces)
    
    return text

def _handle_api_key(key_name: str, provider: str) -> bool:
    """Interactively fetch and save missing API keys."""
    if os.getenv(key_name):
        return True
    
    if os.getenv("PDD_FORCE") == "1":
        return False

    CONSOLE.print(f"[yellow]Missing API key {key_name} for {provider}[/yellow]")
    key_val = input(f"Enter {key_name}: ").strip()
    if not key_val:
        return False

    # Sanitize for WSL/OS
    key_val = "".join(char for char in key_val if char.isprintable()).strip()
    
    env_path = _get_project_root() / ".env"
    set_key(str(env_path), key_name, key_val)
    os.environ[key_name] = key_val
    
    CONSOLE.print(f"[green]Key saved to {env_path}[/green]")
    return True

# --- Cloud Invocation Logic ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    import requests
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudInvocationError("No PDD_CLOUD_TOKEN found.")
    
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
    try:
        response = requests.post(url, json=payload, timeout=300)
        if response.status_code == 402:
            raise InsufficientCreditsError("PDD Cloud: Insufficient credits.")
        if response.status_code in [401, 403]:
            # Simple placeholder for clearing JWT cache logic
            raise CloudFallbackError(f"Auth error {response.status_code}")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {response.status_code}")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Network error: {str(e)}")

# --- Main Logic ---

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
    _load_env()
    setup_logging()

    # 1. Cloud Execution Path
    is_cloud_forced_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is True or (use_cloud is None and not is_cloud_forced_local):
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
            
            # Re-validate result if local pydantic class is provided
            if output_pydantic and cloud_res.get("result"):
                cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            
            return cloud_res
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
            if use_cloud is True:
                raise

    # 2. Local Model Selection
    df = _get_model_csv()
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row['model']] = {'input': row['input_cost'], 'output': row['output_cost']}

    # Basic filtering by key presence
    available_models = df.copy()
    
    # Strength logic (simplified interpolation placeholder)
    # real implementation would sort by ELO/Cost and pick based on 0.5 pivot
    selected_row = available_models.iloc[0] 
    model_name = selected_row['model']
    provider = selected_row['provider']
    api_key_name = selected_row['api_key']

    # 3. Key management
    if api_key_name and api_key_name != "EXISTING_KEY":
        if not _handle_api_key(api_key_name, provider):
            raise RuntimeError(f"No API key for {model_name}")

    # 4. Prompt Preparation
    if not messages:
        # Simple Jinja-like replacement for {{var}}
        if prompt and isinstance(input_json, dict):
            formatted_prompt = prompt
            for k, v in input_json.items():
                formatted_prompt = formatted_prompt.replace("{{" + k + "}}", str(v))
            messages = [{"role": "user", "content": formatted_prompt}]
        else:
            messages = [{"role": "user", "content": str(prompt)}]

    # 5. Reasoning Logic
    extra_params = {}
    r_type = selected_row.get('reasoning_type', 'none')
    max_r_tokens = selected_row.get('max_reasoning_tokens', 0)
    
    if r_type == 'budget' and max_r_tokens > 0:
        budget = int(time * max_r_tokens)
        if "anthropic" in provider:
            extra_params["thinking"] = {"type": "enabled", "budget_tokens": budget}
            temperature = 1.0 # Required for Anthropic thinking
    elif r_type == 'effort':
        effort = "medium"
        if time < 0.3: effort = "low"
        elif time > 0.7: effort = "high"
        
        if "gpt-5" in model_name: # Hypothetical
            extra_params["reasoning"] = {"effort": effort, "summary": "auto"}
        else:
            extra_params["reasoning_effort"] = effort

    # 6. Structured Output
    if output_pydantic or output_schema:
        schema = output_schema or _pydantic_to_json_schema(output_pydantic) # type: ignore
        if selected_row.get('structured_output') == 1:
            extra_params["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "output", "schema": schema, "strict": True}
            }

    # 7. Call LiteLLM
    try:
        if use_batch_mode:
            # Type ignoring for complex batch message types
            resp = batch_completion(
                model=model_name,
                messages=messages, # type: ignore
                temperature=temperature,
                **extra_params
            )
            result = [r.choices[0].message.content for r in resp]
        else:
            # Handle OpenAI Responses API special case if needed
            call_fn = completion
            if "gpt-5" in model_name:
                # Placeholder for litellm.responses() if/when implemented
                pass
            
            resp = call_fn(
                model=model_name,
                messages=messages, # type: ignore
                temperature=temperature,
                timeout=LLM_CALL_TIMEOUT,
                num_retries=2,
                **extra_params
            )
            
            raw_content = resp.choices[0].message.content
            
            # Post-processing
            if output_pydantic or output_schema:
                raw_content = _repair_json(raw_content)
                parsed = json.loads(raw_content)
                if output_pydantic:
                    result = output_pydantic.model_validate(parsed)
                else:
                    result = parsed
            else:
                result = raw_content

            thinking = getattr(resp.choices[0].message, "reasoning_content", None)
            if not thinking and hasattr(resp, "_hidden_params"):
                thinking = resp._hidden_params.get("thinking")

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

    except Exception as e:
        logger.error(f"Invocation failed: {e}")
        raise RuntimeError(f"LLM Invoke failed: {str(e)}")

    return {}

if __name__ == "__main__":
    setup_logging()
    # Example usage:
    # res = llm_invoke(prompt="Hello {{name}}", input_json={"name": "PDD"})
    # print(res)