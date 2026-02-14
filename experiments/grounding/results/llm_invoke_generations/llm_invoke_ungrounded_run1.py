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
from pydantic import BaseModel, ValidationError
from rich.console import Console

# Internal relative imports as per requirements
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# Constants
LLM_CALL_TIMEOUT = 120
PROJECT_ROOT = get_default_resolver().resolve_project_root()
console = Console()

# Logging Configuration
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}


class SchemaValidationError(Exception):
    """Raised when the LLM response fails Pydantic or JSON schema validation."""
    pass


class CloudFallbackError(Exception):
    """Recoverable cloud error (network, auth, 5xx) triggering local fallback."""
    pass


class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass


class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required."""
    pass


def setup_logging():
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        log_level = "WARNING"
        lite_level = "ERROR"
    
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = "DEBUG"
        lite_level = "DEBUG"

    logging.basicConfig(level=log_level)
    logger.setLevel(log_level)
    litellm_logger.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"


def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", None)
        cost = 0.0
        try:
            cost = completion_cost(completion_response=response_obj)
        except Exception:
            model = kwargs.get("model", "")
            if model in _MODEL_RATE_MAP and usage:
                rates = _MODEL_RATE_MAP[model]
                cost = (usage.prompt_tokens * rates["input"] + 
                        usage.completion_tokens * rates["output"]) / 1_000_000
        
        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.error(f"Callback error: {e}")


litellm.success_callback = [_success_callback]


def _get_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        resolver.resolve_data_file("llm_model.csv")
    ]
    
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    "input": float(row.get('input_cost', 0)),
                    "output": float(row.get('output_cost', 0))
                }
            return df
    raise FileNotFoundError("llm_model.csv not found in any resolved paths.")


def _handle_api_key(key_name: str, provider: str) -> Optional[str]:
    key = os.getenv(key_name)
    if key:
        return key.strip().strip('"').strip("'")
    
    if os.getenv("PDD_FORCE"):
        return None

    console.print(f"[bold yellow]Missing API key for {provider} ({key_name}).[/bold yellow]")
    new_key = console.input(f"Enter {key_name}: ").strip().strip('"').strip("'")
    
    if new_key:
        env_path = PROJECT_ROOT / ".env"
        set_key(str(env_path), key_name, new_key)
        os.environ[key_name] = new_key
        console.print(f"[green]Key saved to {env_path}[/green]")
        return new_key
    return None


def _repair_json(text: str) -> str:
    # Handle fenced code blocks
    json_match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if json_match:
        text = json_match.group(1)
    
    # Simple bracket balancing and truncation repair
    text = text.strip()
    if not text: return "{}"
    
    open_brackets = text.count('{')
    close_brackets = text.count('}')
    if open_brackets > close_brackets:
        text += '}' * (open_brackets - close_brackets)
    
    return text


def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        schema["additionalProperties"] = False
        for p in props.values():
            _ensure_all_properties_required(p)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])


def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Any,
    messages: Optional[List[Dict]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    # Placeholder for Firebase Cloud Function endpoint
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    token = os.getenv("PDD_CLOUD_TOKEN")
    
    payload = {
        "prompt": prompt,
        "inputJson": input_json,
        "messages": messages,
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "outputSchema": output_schema,
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
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in [401, 403, 500, 502, 503, 504]:
            raise CloudFallbackError(f"Cloud error {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")


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
    """Expert-level implementation of PDD LLM invocation logic."""
    setup_logging()
    load_dotenv(PROJECT_ROOT / ".env")

    # 1. Cloud Execution Logic
    if use_cloud is None:
        force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
        use_cloud = not force_local and os.getenv("PDD_CLOUD_ENABLED") == "1"

    if use_cloud:
        effective_schema = output_schema
        if output_pydantic:
            effective_schema = output_pydantic.model_json_schema()
            _ensure_all_properties_required(effective_schema)

        try:
            cloud_res = _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, 
                time, verbose, effective_schema, use_batch_mode, language
            )
            if output_pydantic and "result" in cloud_res:
                cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            return cloud_res
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Logic
    df = _get_model_csv()
    base_model_id = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter valid models
    valid_models = []
    for _, row in df.iterrows():
        key_env = str(row.get('api_key', ''))
        if key_env == "EXISTING_KEY" or os.getenv(key_env) or not os.getenv("PDD_FORCE"):
            valid_models.append(row)
    
    if not valid_models:
        raise RuntimeError("No models available (missing API keys and PDD_FORCE is set)")

    # Selection Logic
    base_row = next((r for r in valid_models if r['model'] == base_model_id), valid_models[0])
    
    if strength == 0.5:
        candidates = [base_row] + sorted(valid_models, key=lambda x: x.get('coding_arena_elo', 0), reverse=True)
    elif strength < 0.5:
        candidates = sorted(valid_models, key=lambda x: x.get('input_cost', 0))
    else:
        candidates = sorted(valid_models, key=lambda x: x.get('coding_arena_elo', 0), reverse=True)

    # 3. Invocation Loop
    last_exception = None
    for model_row in candidates:
        model_name = model_row['model']
        provider = model_row['provider']
        
        # Auth check
        api_key = _handle_api_key(str(model_row['api_key']), provider)
        if not api_key and str(model_row['api_key']) != "EXISTING_KEY":
            continue

        # Prepare reasoning params
        kwargs: Dict[str, Any] = {
            "model": model_name,
            "temperature": temperature,
            "timeout": LLM_CALL_TIMEOUT,
            "num_retries": 2
        }

        r_type = model_row.get('reasoning_type', 'none')
        max_r = int(model_row.get('max_reasoning_tokens', 0))
        
        if r_type == 'budget':
            budget = int(time * max_r)
            if "anthropic" in provider:
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                kwargs["temperature"] = 1.0 # Required for Anthropic thinking
        elif r_type == 'effort':
            effort = "medium"
            if time < 0.3: effort = "low"
            elif time > 0.7: effort = "high"
            kwargs["reasoning_effort"] = effort

        # Build Messages
        current_messages = messages
        if not current_messages:
            p_text = prompt or "{{input}}"
            if input_json:
                p_text = p_text.replace("{{input}}", json.dumps(input_json, indent=2))
            current_messages = [{"role": "user", "content": p_text}]

        try:
            # Call litellm
            if use_batch_mode:
                response = batch_completion(messages=current_messages, **kwargs)
            else:
                # Handle special GPT-5/Responses API if detected (omitted for brevity, usage standard completion)
                response = completion(messages=current_messages, **kwargs)

            # Process response
            content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            
            # Structured Output Processing
            result = content
            if output_pydantic or output_schema:
                try:
                    parsed = json.loads(_repair_json(content))
                    if output_pydantic:
                        result = output_pydantic.model_validate(parsed)
                    else:
                        result = parsed
                except (json.JSONDecodeError, ValidationError) as e:
                    logger.warning(f"Schema validation failed for {model_name}: {e}")
                    raise SchemaValidationError(str(e))

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except SchemaValidationError:
            continue # Fallback to next model
        except Exception as e:
            logger.error(f"Error invoking {model_name}: {e}")
            last_exception = e
            continue

    raise RuntimeError(f"All models exhausted. Last error: {last_exception}")

if __name__ == "__main__":
    # Example usage
    try:
        res = llm_invoke(prompt="Say hello in {{lang}}", input_json={"lang": "Python"})
        console.print(res)
    except Exception as e:
        console.print(f"[red]Execution failed: {e}[/red]")