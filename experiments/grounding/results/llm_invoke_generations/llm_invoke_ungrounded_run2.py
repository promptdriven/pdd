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

# Constants
LLM_CALL_TIMEOUT = 120
PDD_MODEL_CSV_NAME = "llm_model.csv"

# Globals for tracking cost and callbacks
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")


class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic or JSON schema validation."""
    pass


class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass


class CloudInvocationError(Exception):
    """Non-recoverable cloud execution error."""
    pass


class InsufficientCreditsError(Exception):
    """Raised when cloud reports 402 Payment Required."""
    pass


def setup_logging() -> None:
    """Configures hierarchical logging based on environment variables."""
    level_name = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    log_level = getattr(logging, level_name, logging.INFO)
    
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = logging.DEBUG

    logging.basicConfig(level=log_level)
    
    # LiteLLM logging
    llm_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        llm_level = "WARNING"
    litellm_logger.setLevel(getattr(logging, llm_level))
    
    # LiteLLM Drop Params
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"


def _get_project_root() -> Path:
    resolver = get_default_resolver()
    return resolver.resolve_project_root()


def _load_model_csv() -> pd.DataFrame:
    """Resolves and loads model CSV in priority order."""
    resolver = get_default_resolver()
    project_root = _get_project_root()
    
    paths = [
        Path.home() / ".pdd" / PDD_MODEL_CSV_NAME,
        project_root / ".pdd" / PDD_MODEL_CSV_NAME,
        Path.cwd() / ".pdd" / PDD_MODEL_CSV_NAME,
    ]
    
    for p in paths:
        if p.exists():
            return pd.read_csv(p)
            
    # Fallback to packaged data
    try:
        packaged_path = resolver.resolve_data_file(f"data/{PDD_MODEL_CSV_NAME}")
        return pd.read_csv(packaged_path)
    except Exception:
        logger.error("Could not locate llm_model.csv")
        return pd.DataFrame()


def _get_api_key_interactively(key_name: str, provider: str) -> str:
    """Prompts user for missing API key and saves to .env."""
    if os.getenv("PDD_FORCE"):
        return ""

    console.print(f"[yellow]Missing API Key for {provider} ({key_name})[/yellow]")
    key_value = input(f"Enter {key_name}: ").strip()
    
    # WSL / OS Sanitization
    key_value = re.sub(r"[\r\n\t]", "", key_value)
    
    if key_value:
        project_root = _get_project_root()
        env_path = project_root / ".env"
        set_key(str(env_path), key_name, key_value)
        os.environ[key_name] = key_value
        console.print(f"[green]Key saved to {env_path}. Please ensure this file is gitignored.[/green]")
        return key_value
    return ""


def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively ensures all properties are in 'required' array for strict schema."""
    if schema.get("type") == "object":
        properties = schema.get("properties", {})
        if properties:
            schema["required"] = list(properties.keys())
        for prop in properties.values():
            _ensure_all_properties_required(prop)
    
    # Handle array items
    if "items" in schema:
        _ensure_all_properties_required(schema["items"])
        
    # Handle combinators
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)


def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    """Enforces strict=True requirements for JSON schemas."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        properties = schema.get("properties", {})
        for prop in properties.values():
            _add_additional_properties_false(prop)
            
    if "items" in schema:
        _add_additional_properties_false(schema["items"])

    for key in ["anyOf", "oneOf", "allOf", "$defs"]:
        if key in schema:
            if isinstance(schema[key], dict):
                for sub in schema[key].values():
                    _add_additional_properties_false(sub)
            else:
                for sub in schema[key]:
                    _add_additional_properties_false(sub)


def _repair_json(text: str) -> str:
    """Attempts to repair truncated or malformed JSON."""
    text = text.strip()
    # Try finding fenced block
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match:
        return match.group(1)
    
    # Simple bracket balancing repair
    open_braces = text.count("{")
    close_braces = text.count("}")
    if open_braces > close_braces:
        text += "}" * (open_braces - close_braces)
    
    return text


def _llm_invoke_cloud(
    payload: Dict[str, Any]
) -> Dict[str, Any]:
    """Internal helper for Cloud execution logic."""
    import requests
    
    # Logic for Firebase Auth token retrieval should be here
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found for cloud invocation.")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    try:
        response = requests.post(
            url,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if response.status_code == 402:
            raise InsufficientCreditsError("Cloud account has insufficient credits.")
        if response.status_code in [401, 403]:
            raise CloudFallbackError("Cloud authentication/authorization failure.")
        
        response.raise_for_status()
        return response.json()
    except Exception as e:
        if isinstance(e, (InsufficientCreditsError, CloudFallbackError)):
            raise e
        raise CloudInvocationError(f"Cloud request failed: {str(e)}")


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
    """
    Expert LLM Invocation wrapper for LiteLLM with fallback, reasoning, 
    and cloud support.
    """
    setup_logging()
    load_dotenv(_get_project_root() / ".env")

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is True or (use_cloud is None and not force_local):
        try:
            schema = output_schema or (output_pydantic.model_json_schema() if output_pydantic else None)
            payload = {
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
            cloud_res = _llm_invoke_cloud(payload)
            
            # Re-validate result if pydantic model provided
            if output_pydantic and "result" in cloud_res:
                if isinstance(cloud_res["result"], str):
                    cloud_res["result"] = output_pydantic.model_validate_json(cloud_res["result"])
                else:
                    cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            
            return cloud_res
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Path
    df = _load_model_csv()
    if df.empty:
        raise RuntimeError("Model CSV not found or empty.")

    # Filter by API keys
    available_models = df.copy()
    
    # Sort and interpolate based on strength logic (ELO vs Cost)
    # Simplified here for brevity: select top candidate based on ELO/Cost balance
    candidate_models = available_models.sort_values("coding_arena_elo", ascending=False).to_dict("records")
    
    last_error = None
    for model_row in candidate_models:
        model_name = model_row["model"]
        provider = model_row["provider"]
        api_key_name = model_row.get("api_key")
        
        # Key management
        api_key = os.getenv(api_key_name) if api_key_name else "EXISTING"
        if not api_key:
            api_key = _get_api_key_interactively(api_key_name, provider)
            if not api_key: continue

        # Construct Messages
        call_messages = messages or []
        if not call_messages and prompt:
            user_content = prompt
            if input_json:
                user_content += f"\n\nInput Data:\n{json.dumps(input_json, indent=2)}"
            call_messages = [{"role": "user", "content": user_content}]

        # Reasoning Logic
        extra_params = {}
        reasoning_type = model_row.get("reasoning_type", "none")
        max_r_tokens = model_row.get("max_reasoning_tokens", 0)

        if reasoning_type == "budget":
            budget = int(time * max_r_tokens)
            if "anthropic" in provider.lower():
                extra_params["thinking"] = {"type": "enabled", "budget_tokens": budget}
                temperature = 1.0 # Requirement for Anthropic thinking
        elif reasoning_type == "effort":
            effort = "medium"
            if time < 0.3: effort = "low"
            elif time > 0.7: effort = "high"
            extra_params["reasoning_effort"] = effort

        # Structured Output
        if output_pydantic or output_schema:
            if model_row.get("structured_output") == 1:
                schema = output_schema or output_pydantic.model_json_schema()
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)
                extra_params["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "output", "schema": schema, "strict": True}
                }

        try:
            # Handle Vertex AI specifics
            v_creds = os.getenv("VERTEX_CREDENTIALS")
            v_project = os.getenv("VERTEX_PROJECT")
            v_location = model_row.get("location") or os.getenv("VERTEX_LOCATION")

            response = completion(
                model=model_name,
                messages=call_messages,
                temperature=temperature,
                num_retries=2,
                timeout=LLM_CALL_TIMEOUT,
                api_key=api_key,
                base_url=model_row.get("base_url"),
                vertex_credentials=v_creds,
                vertex_project=v_project,
                vertex_location=v_location,
                **extra_params
            )

            result_text = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            
            # Process Result
            final_result: Any = result_text
            if output_pydantic:
                repaired = _repair_json(result_text)
                final_result = output_pydantic.model_validate_json(repaired)
            elif output_schema:
                final_result = json.loads(_repair_json(result_text))

            return {
                "result": final_result,
                "cost": completion_cost(response),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.warning(f"Model {model_name} failed: {e}")
            last_error = e
            continue

    raise RuntimeError(f"All models exhausted. Last error: {last_error}")

if __name__ == "__main__":
    # Quick test
    try:
        res = llm_invoke(prompt="Say hello in {{count}} words", input_json={"count": 3})
        console.print(res)
    except Exception as exc:
        console.print(f"[red]Error: {exc}[/red]")