from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

if TYPE_CHECKING:
    from pydantic import ConfigDict

# Package-level imports (relative)
try:
    from . import (
        DEFAULT_STRENGTH,
        DEFAULT_TIME,
        EXTRACTION_STRENGTH,
    )
except ImportError:
    # Fallback for standalone script testing
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = 0.25
    EXTRACTION_STRENGTH = 0.7

# --- Constants & Globals ---
CONSOLE = Console()
LOGGER = logging.getLogger("pdd.llm_invoke")
LITELLM_LOGGER = logging.getLogger("litellm")
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation or JSON parsing."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required from Cloud."""
    pass

# --- Configuration & Setup ---

def setup_logging() -> None:
    """Configures hierarchical logging."""
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"

    logging.basicConfig(level=logging.WARNING)
    LOGGER.setLevel(pdd_level)
    LITELLM_LOGGER.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

def _load_env() -> Path:
    """Detects project root and loads .env."""
    # Simplified resolver logic as per prompt requirements
    cwd = Path.cwd()
    root = cwd
    markers = [".git", "pyproject.toml", "data", ".env"]
    for parent in [cwd] + list(cwd.parents):
        if any((parent / m).exists() for m in markers):
            root = parent
            break
    
    env_path = root / ".env"
    load_dotenv(dotenv_path=env_path)
    return root

# --- Model Selection Logic ---

def _load_model_csv(project_root: Path) -> pd.DataFrame:
    """Resolves and loads llm_model.csv in priority order."""
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv",
    ]
    
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            # Build rate map for fallback
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": row.get("input", 0.0),
                    "output": row.get("output", 0.0)
                }
            return df
    raise FileNotFoundError("llm_model.csv not found in any expected location.")

def _select_models(df: pd.DataFrame, strength: float) -> List[Dict[str, Any]]:
    """Filters and ranks models based on strength and ELO/Cost."""
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter for models where we have keys or keys are placeholders
    def has_key(row):
        key_name = str(row["api_key"])
        if key_name in ["", "nan", "None"]: return False
        if key_name == "EXISTING_KEY" or os.getenv(key_name): return True
        return not os.getenv("PDD_FORCE") # Interactive mode allowed

    available = df[df.apply(has_key, axis=1)].copy()
    if available.empty:
        available = df.head(1) # Surrogate

    base_model = available[available["model"] == default_model_name]
    if base_model.empty:
        base_model = available.iloc[:1]
    
    base_idx = base_model.index[0]
    
    if strength == 0.5:
        # Sort others by ELO descending as fallback
        candidates = pd.concat([base_model, available.drop(base_idx).sort_values("coding_arena_elo", ascending=False)])
    elif strength < 0.5:
        # Interpolate by cost (cheapest to base)
        available["cost_sum"] = available["input"] + available["output"]
        candidates = available[available["cost_sum"] <= base_model["cost_sum"].iloc[0]].sort_values("cost_sum")
    else:
        # Interpolate by ELO (base to highest)
        candidates = available[available["coding_arena_elo"] >= base_model["coding_arena_elo"].iloc[0]].sort_values("coding_arena_elo", ascending=False)

    return candidates.to_dict("records")

# --- Key Management ---

def _ensure_api_key(key_name: str) -> Optional[str]:
    """Interactively fetches and saves missing API keys."""
    if not key_name or key_name == "EXISTING_KEY":
        return None
        
    val = os.getenv(key_name)
    if val:
        return val.strip()

    if os.getenv("PDD_FORCE"):
        return None

    CONSOLE.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name}")
    new_key = input(f"Enter value for {key_name}: ").strip()
    
    # WSL Diagnostic
    if "microsoft" in open("/proc/version").read().lower() or os.getenv("WSL_DISTRO_NAME"):
        new_key = new_key.replace("\r", "")

    os.environ[key_name] = new_key
    project_root = _load_env()
    env_path = project_root / ".env"
    
    # In-place update of .env
    set_key(str(env_path), key_name, new_key)
    CONSOLE.print(f"[bold green]Key saved to {env_path}[/bold green]")
    return new_key

# --- Structured Output Utilities ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively ensures all properties are in 'required' array for strict mode."""
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for p in props.values():
            _ensure_all_properties_required(p)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    """Recursively adds additionalProperties: false to all object schemas."""
    if schema.get("type") == "object":
        schema["additional_properties"] = False
        props = schema.get("properties", {})
        for p in props.values():
            _add_additional_properties_false(p)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

# --- LLM Response Cleaning ---

def _repair_json(text: str) -> str:
    """Attempts to extract and repair JSON from prose."""
    # 1. Try fenced code blocks
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match: return match.group(1)
    
    # 2. Balanced braces
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end != -1:
        return text[start:end+1]
    return text

def _smart_unescape_code(text: str) -> str:
    """Unescapes double-escaped newlines while preserving literals."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

# --- Cloud Invocation ---

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
    language: Optional[str]
) -> Dict[str, Any]:
    """Calls the pdd cloud endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
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
        resp = requests.post(url, json=payload, headers={"Authorization": f"Bearer {token}"}, timeout=300)
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits for cloud execution.")
        if resp.status_code in [401, 403]:
            raise CloudFallbackError("Cloud auth failure.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.RequestException as e:
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
    Invokes an LLM with fallback, key management, and structured output support.
    """
    setup_logging()
    project_root = _load_env()

    # 1. Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_cloud = use_cloud if use_cloud is not None else (not force_local and os.getenv("PDD_CLOUD_TOKEN"))
    
    if should_cloud:
        schema = output_schema or (output_pydantic.model_json_schema() if output_pydantic else None)
        try:
            cloud_res = _llm_invoke_cloud(prompt, input_json, messages, strength, temperature, time, verbose, schema, use_batch_mode, language)
            if output_pydantic:
                cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            return cloud_res
        except CloudFallbackError as e:
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Setup
    df = _load_model_csv(project_root)
    candidates = _select_models(df, strength)
    
    if not messages:
        if isinstance(input_json, list):
            use_batch_mode = True
            msgs_list = []
            for item in input_json:
                formatted = prompt.format(**item) if prompt else ""
                msgs_list.append([{"role": "user", "content": formatted}])
            final_messages = msgs_list
        else:
            formatted = prompt.format(**(input_json or {})) if prompt else ""
            final_messages = [{"role": "user", "content": formatted}]
    else:
        final_messages = messages

    # 3. Iterative Invocation through candidates
    last_err = None
    for model_info in candidates:
        model_name = model_info["model"]
        provider = model_info["provider"]
        
        api_key = _ensure_api_key(model_info["api_key"])
        
        # Reasoning Config
        reasoning_params = {}
        r_type = model_info.get("reasoning_type", "none")
        max_r = int(model_info.get("max_reasoning_tokens", 0))
        
        if r_type == "budget" and max_r > 0:
            reasoning_params["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_r)}
            temperature = 1.0 # Anthropic requirement
        elif r_type == "effort":
            effort = "low" if time < 0.3 else "medium" if time < 0.7 else "high"
            reasoning_params["reasoning_effort"] = effort

        # Structured Output Config
        resp_format = None
        if output_pydantic or output_schema:
            schema = output_schema or output_pydantic.model_json_schema()
            _ensure_all_properties_required(schema)
            _add_additional_properties_false(schema)
            
            if model_info.get("structured_output"):
                resp_format = {
                    "type": "json_schema",
                    "json_schema": {"name": "output", "schema": schema, "strict": True}
                }

        try:
            # LiteLLM Call
            call_kwargs = {
                "model": model_name,
                "messages": final_messages,
                "temperature": temperature,
                "timeout": LLM_CALL_TIMEOUT,
                "api_key": api_key,
                "response_format": resp_format,
                **reasoning_params
            }
            
            # Provider Specifics
            if provider == "vertex_ai":
                call_kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
                call_kwargs["vertex_location"] = model_info.get("location") or os.getenv("VERTEX_LOCATION")
                # credentials logic...
            
            if use_batch_mode:
                responses = batch_completion(**call_kwargs)
                results = [r.choices[0].message.content for r in responses]
                thinking = [getattr(r.choices[0].message, "reasoning_content", None) for r in responses]
            else:
                response = completion(**call_kwargs)
                raw_result = response.choices[0].message.content
                thinking = getattr(response.choices[0].message, "reasoning_content", None)
                
                # Validation & Parsing
                if output_pydantic:
                    clean_json = _repair_json(raw_result)
                    parsed = json.loads(clean_json)
                    result = output_pydantic.model_validate(parsed)
                elif output_schema:
                    result = json.loads(_repair_json(raw_result))
                else:
                    result = raw_result

            return {
                "result": result,
                "cost": completion_cost(response) if not use_batch_mode else 0.0,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            LOGGER.warning(f"Model {model_name} failed: {e}")
            last_err = e
            continue

    raise RuntimeError(f"All models failed. Last error: {last_err}")

if __name__ == "__main__":
    # Example usage
    res = llm_invoke(prompt="Say hello in {lang}", input_json={"lang": "French"})
    print(res)