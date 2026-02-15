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

# Use relative imports for internal modules as requested
try:
    from . import (
        DEFAULT_STRENGTH,
        DEFAULT_TIME,
        EXTRACTION_STRENGTH,
    )
    from .path_resolution import get_default_resolver
except ImportError:
    # Fallback for direct execution/testing
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = 0.25
    EXTRACTION_STRENGTH = 0.5

# --- Global Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
console = Console()

# --- Logging Configuration ---
logger = logging.getLogger("pdd.llm_invoke")
lite_logger = logging.getLogger("litellm")

def setup_logging() -> None:
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        pdd_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"

    logging.basicConfig(level=logging.WARNING)
    logger.setLevel(pdd_level)
    lite_logger.setLevel(lite_level)
    
    litellm.set_verbose = (pdd_level == "DEBUG")
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

def success_callback(kwargs: Dict[str, Any], response_obj: Any) -> None:
    """LiteLLM callback to capture usage data."""
    try:
        model = kwargs.get("model", "unknown")
        cost = completion_cost(completion_response=response_obj) or 0.0
        _LAST_CALLBACK_DATA["cost"] = cost
        _LAST_CALLBACK_DATA["usage"] = getattr(response_obj, "usage", None)
        _LAST_CALLBACK_DATA["finish_reason"] = response_obj.choices[0].finish_reason if response_obj.choices else None
    except Exception as e:
        logger.debug(f"Callback error: {e}")

litellm.success_callback = [success_callback]

# --- Exceptions ---
class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic/JSON validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (auth, 5xx, timeout)."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Helper Functions ---

def _is_wsl() -> bool:
    return "microsoft-standard" in open("/proc/version", "r").read().lower() if Path("/proc/version").exists() else "WSL_DISTRO_NAME" in os.environ

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively adds all properties to 'required' and sets additionalProperties=False."""
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
        for def_schema in schema["$defs"].values():
            _ensure_all_properties_required(def_schema)

def _repair_json(text: str) -> str:
    """Attempts to extract and repair JSON from prose."""
    text = text.strip()
    # Try finding markdown block
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match:
        text = match.group(1)
    
    # Simple balance check and closure
    if text.startswith("{") and not text.endswith("}"):
        text += "}"
    elif text.startswith("[") and not text.endswith("]"):
        text += "]"
    
    return text

def _smart_unescape_code(text: str) -> str:
    """Unescapes double-escaped newlines while preserving literals."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _handle_missing_key(key_name: str, provider: str) -> Optional[str]:
    """Interactively fetches and saves missing API keys."""
    if os.getenv("PDD_FORCE"):
        return None
    
    console.print(f"[bold yellow]Missing API key '{key_name}' for provider '{provider}'.[/bold yellow]")
    key_val = input(f"Enter {key_name}: ").strip()
    if not key_val:
        return None
    
    # Save to .env
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    env_path = project_root / ".env"
    
    set_key(str(env_path), key_name, key_val)
    os.environ[key_name] = key_val
    
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")
    logger.warning(f"Security: API key for {provider} saved to local .env file.")
    return key_val

def _get_model_candidates(strength: float) -> List[Dict[str, Any]]:
    """Loads CSV and filters/sorts models based on strength and ELO."""
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    
    csv_path = next((p for p in paths if p.exists()), None)
    if not csv_path:
        raise RuntimeError("llm_model.csv not found.")
        
    df = pd.read_csv(csv_path)
    
    # Global rates for fallback
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row["model"]] = {"input": row["input"], "output": row["output"]}

    # Identify base model
    base_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row = df[df["model"] == base_name] if base_name else pd.DataFrame()
    if base_row.empty:
        base_row = df.iloc[[0]]
    
    base_elo = base_row["coding_arena_elo"].values[0]
    base_cost = base_row["input"].values[0] + base_row["output"].values[0]

    # Model Selection Logic
    if strength == 0.5:
        candidates = df.sort_values(by="coding_arena_elo", ascending=False)
    elif strength < 0.5:
        # Interpolate by cost (cheapest to base)
        candidates = df[df["input"] + df["output"] <= base_cost].sort_values(by="input")
    else:
        # Interpolate by ELO (base to highest)
        candidates = df[df["coding_arena_elo"] >= base_elo].sort_values(by="coding_arena_elo", ascending=False)
        
    return candidates.to_dict("records")

# --- Cloud Invocation ---

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict, List[Dict]]],
    messages: Optional[Union[List[Dict], List[List[Dict]]]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    import requests
    
    # Simple check for cloud readiness (this would use a real token/JWT manager in production)
    id_token = os.getenv("PDD_CLOUD_TOKEN")
    if not id_token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {id_token}", "Content-Type": "application/json"}
    
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
        response = requests.post(url, json=payload, headers=headers, timeout=300)
        if response.status_code == 402:
            raise InsufficientCreditsError("PDD Cloud: Insufficient credits.")
        if response.status_code in [401, 403]:
            # Clear cache placeholder
            raise CloudFallbackError("Cloud auth error.")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {response.status_code}")
        
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
    """Invokes an LLM with model selection, fallback, and key management."""
    setup_logging()
    load_dotenv(get_default_resolver().resolve_project_root() / ".env")

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_cloud = False
    if use_cloud is True:
        should_cloud = True
    elif use_cloud is False or force_local:
        should_cloud = False
    else:
        # Check if cloud is configured (e.g. env var exists)
        should_cloud = bool(os.getenv("PDD_CLOUD_TOKEN"))

    if should_cloud:
        schema = output_schema
        if output_pydantic:
            schema = output_pydantic.model_json_schema()
            _ensure_all_properties_required(schema)
            
        try:
            cloud_res = _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, 
                time, verbose, schema, use_batch_mode, language
            )
            # Validate structured output locally if pydantic provided
            if output_pydantic and "result" in cloud_res:
                res_data = cloud_res["result"]
                if isinstance(res_data, str):
                    res_data = json.loads(_repair_json(res_data))
                cloud_res["result"] = output_pydantic.model_validate(res_data)
            return cloud_res
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
            # Fall through to local

    # 2. Local Preparation
    candidates = _get_model_candidates(strength)
    
    # Build final schema
    final_schema = output_schema
    if output_pydantic:
        final_schema = output_pydantic.model_json_schema()
        _ensure_all_properties_required(final_schema)

    # Prepare Messages
    final_messages = messages
    if not final_messages:
        if not prompt:
            raise ValueError("Prompt or Messages required.")
        content = prompt.format(**(input_json if isinstance(input_json, dict) else {}))
        final_messages = [{"role": "user", "content": content}]

    # 3. Execution Loop
    last_error = None
    for model_row in candidates:
        model_name = model_row["model"]
        provider = model_row["provider"]
        api_key_name = model_row["api_key"]
        
        # Key Management
        api_key = os.getenv(api_key_name)
        if not api_key and api_key_name not in ["EXISTING_KEY", ""]:
            api_key = _handle_missing_key(api_key_name, provider)
            if not api_key:
                continue

        # Reasoning & Extra Params
        kwargs: Dict[str, Any] = {
            "model": model_name,
            "messages": final_messages,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
            "api_key": api_key,
        }
        
        # Reasoning logic
        r_type = model_row.get("reasoning_type", "none")
        max_r = int(model_row.get("max_reasoning_tokens", 0))
        if r_type == "budget" and max_r > 0:
            kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_r)}
            kwargs["temperature"] = 1.0 # Anthropic requirement
        elif r_type == "effort":
            effort_map = {0.0: "low", 0.5: "medium", 1.0: "high"}
            effort_val = effort_map.get(time, "medium")
            if "gpt-5" in model_name: # Responses API logic
                kwargs["reasoning"] = {"effort": effort_val, "summary": "auto"}
                kwargs.pop("temperature", None)
            else:
                kwargs["reasoning_effort"] = effort_val

        # Structured Output logic
        if final_schema and model_row.get("structured_output"):
            if "gpt-5" in model_name:
                kwargs["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": final_schema, "strict": True}}
            else:
                kwargs["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": final_schema, "strict": True}}

        # Vertex AI Special Handling
        if provider == "vertex_ai" or model_name.startswith("vertex_ai/"):
            kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
            kwargs["vertex_location"] = model_row.get("location") or os.getenv("VERTEX_LOCATION", "us-central1")
            v_creds = os.getenv("VERTEX_CREDENTIALS")
            if v_creds:
                kwargs["vertex_credentials"] = v_creds

        try:
            if use_batch_mode:
                response = batch_completion(**kwargs)
            elif "gpt-5" in model_name:
                # Custom handler for Responses API if needed, otherwise litellm.completion usually wraps it
                response = completion(**kwargs)
            else:
                response = completion(**kwargs)

            # Process Response
            content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            
            result_obj: Any = content
            if final_schema:
                try:
                    parsed_json = json.loads(_repair_json(content))
                    if output_pydantic:
                        result_obj = output_pydantic.model_validate(parsed_json)
                    else:
                        result_obj = parsed_json
                except Exception as e:
                    logger.warning(f"Schema validation failed for {model_name}: {e}")
                    raise SchemaValidationError(str(e))

            cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
            if cost == 0: # Fallback to CSV rates
                usage = _LAST_CALLBACK_DATA.get("usage")
                if usage:
                    in_r = _MODEL_RATE_MAP.get(model_name, {}).get("input", 0)
                    out_r = _MODEL_RATE_MAP.get(model_name, {}).get("output", 0)
                    cost = (usage.prompt_tokens * in_r + usage.completion_tokens * out_r) / 1_000_000

            return {
                "result": result_obj,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except (SchemaValidationError, litellm.exceptions.BadRequestError) as e:
            last_error = e
            if _is_wsl() and "401" in str(e):
                console.print("[red]WSL Warning: Check for hidden carriage returns in your API keys.[/red]")
            continue
        except Exception as e:
            last_error = e
            logger.error(f"Error invoking {model_name}: {e}")
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_error}")

if __name__ == "__main__":
    # Quick test
    try:
        res = llm_invoke(prompt="Tell me a joke about {thing}", input_json={"thing": "Python engineers"}, strength=0.5)
        console.print(res)
    except Exception as err:
        console.print(f"[bold red]Execution failed:[/bold red] {err}")