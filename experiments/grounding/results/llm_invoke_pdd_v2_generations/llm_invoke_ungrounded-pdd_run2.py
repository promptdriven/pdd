from __future__ import annotations

import json
import logging
import os
import re

import sqlite3
import time as time_module
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal imports as requested
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
PDD_VERBOSE_LOGGING = os.getenv("PDD_VERBOSE_LOGGING", "0") == "1"

console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

# Global to store callback data from LiteLLM
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Custom Exceptions ---

class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required on Cloud."""
    pass

# --- Helper Functions ---

def _setup_logging() -> None:
    level = logging.DEBUG if PDD_VERBOSE_LOGGING else getattr(logging, PDD_LOG_LEVEL.upper(), logging.INFO)
    logger.setLevel(level)
    
    lt_level = getattr(logging, LITELLM_LOG_LEVEL.upper(), logging.WARNING)
    if PDD_ENVIRONMENT == "production":
        lt_level = max(lt_level, logging.WARNING)
    litellm_logger.setLevel(lt_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

def _is_wsl() -> bool:
    if "WSL_DISTRO_NAME" in os.environ:
        return True
    try:
        with open("/proc/version", "r") as f:
            if "microsoft" in f.read().lower():
                return True
    except FileNotFoundError:
        pass
    return False

def _sanitize_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively adds all properties to the 'required' array for strict JSON schemas."""
    if schema.get("type") == "object":
        properties = schema.get("properties", {})
        if properties:
            schema["required"] = list(properties.keys())
            for prop in properties.values():
                _ensure_all_properties_required(prop)
    
    # Handle structured combinators
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    
    if "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    """Recursively adds additionalProperties: false for strict JSON schemas."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        properties = schema.get("properties", {})
        for prop in properties.values():
            _add_additional_properties_false(prop)
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
    
    if "items" in schema:
        _add_additional_properties_false(schema["items"])

def _repair_json_string(text: str) -> str:
    """Attempts to repair truncated or malformed JSON."""
    text = text.strip()
    # Try to find the start of the object/array
    start_idx = text.find("{")
    if start_idx == -1:
        start_idx = text.find("[")
    
    if start_idx != -1:
        text = text[start_idx:]

    # Heuristic: close open brackets
    open_braces = text.count("{") - text.count("}")
    open_brackets = text.count("[") - text.count("]")
    
    if open_braces > 0:
        text += "}" * open_braces
    if open_brackets > 0:
        text += "]" * open_brackets
        
    return text

def _smart_unescape_code(code: str) -> str:
    """Unescapes double-escaped newlines while preserving literal strings."""
    return code.replace("\\n", "\n").replace("\\\"", "\"")

def _repair_python_syntax(code: str) -> str:
    """Cleans up common LLM artifacts in Python code blocks."""
    code = code.strip()
    if code.startswith("```python"):
        code = code[9:]
    if code.startswith("```"):
        code = code[3:]
    if code.endswith("```"):
        code = code[:-3]
    return code.strip()

# --- Model Management ---

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    
    # Priority order
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    
    try:
        packaged_path = resolver.resolve_data_file("llm_model.csv")
        paths.append(packaged_path)
    except Exception:
        pass

    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": float(row.get("input", 0)),
                    "output": float(row.get("output", 0))
                }
            return df
    
    raise RuntimeError("llm_model.csv not found.")

def _get_api_key_interactively(key_name: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
        
    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name}")
    val = input(f"Please enter your {key_name}: ").strip()
    val = _sanitize_key(val)
    
    if not val:
        return ""

    # Save to .env
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    env_path = root / ".env"
    
    set_key(str(env_path), key_name, val)
    os.environ[key_name] = val
    
    console.print(f"[bold green]Security Warning:[/bold green] API key saved to {env_path}")
    return val

def _select_model(strength: float, csv_df: pd.DataFrame) -> List[Dict[str, Any]]:
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter for models where we have keys
    available_models = []
    for _, row in csv_df.iterrows():
        key_name = str(row["api_key"])
        if key_name == "nan" or key_name == "" or key_name == "EXISTING_KEY":
            available_models.append(row.to_dict())
        elif os.getenv(key_name):
            available_models.append(row.to_dict())
            
    if not available_models:
        # Fallback to surrogate: use the first model in CSV but try to get its key
        surrogate = csv_df.iloc[0].to_dict()
        available_models = [surrogate]

    # Model Selection Logic
    available_df = pd.DataFrame(available_models)
    base_model_row = None
    if default_model_name:
        matches = available_df[available_df["model"] == default_model_name]
        if not matches.empty:
            base_model_row = matches.iloc[0].to_dict()
            
    if base_model_row is None:
        # Silently use first available if base not specified or found
        base_model_row = available_df.iloc[0].to_dict()

    if strength == 0.5:
        # Just use base model, followed by others sorted by ELO
        sorted_candidates = [base_model_row] + available_df.sort_values("coding_arena_elo", ascending=False).to_dict("records")
    elif strength < 0.5:
        # Interpolate by cost from base down to cheapest
        base_cost = base_model_row["input"] + base_model_row["output"]
        cheaper = available_df[(available_df["input"] + available_df["output"]) <= base_cost]
        sorted_candidates = cheaper.sort_values("input", ascending=True).to_dict("records")
    else:
        # Interpolate by ELO from base up to highest
        base_elo = base_model_row["coding_arena_elo"]
        better = available_df[available_df["coding_arena_elo"] >= base_elo]
        sorted_candidates = better.sort_values("coding_arena_elo", ascending=False).to_dict("records")

    # Remove duplicates preserving order
    seen = set()
    unique_candidates = []
    for c in sorted_candidates:
        if c["model"] not in seen:
            unique_candidates.append(c)
            seen.add(c["model"])
            
    return unique_candidates

# --- LiteLLM Callback ---

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        model = kwargs.get("model", "unknown")
        usage = getattr(response_obj, "usage", None)
        cost = 0.0
        if usage:
            try:
                cost = completion_cost(completion_response=response_obj)
            except Exception:
                # Fallback to CSV rates
                rates = _MODEL_RATE_MAP.get(model, {"input": 0, "output": 0})
                cost = (usage.prompt_tokens * rates["input"] + usage.completion_tokens * rates["output"]) / 1_000_000

        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None,
            "model": model
        }
    except Exception as e:
        logger.error(f"Callback error: {e}")

litellm.success_callback = [_success_callback]

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
    """Handles transport to Firebase Cloud Functions."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("PDD_CLOUD_TOKEN not set")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
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
        "language": language,
    }

    try:
        response = requests.post(url, json=payload, headers=headers, timeout=300)
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits for cloud invocation.")
        if response.status_code in [401, 403]:
            raise CloudFallbackError(f"Cloud Auth Error: {response.status_code}")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {response.status_code}")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

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
    """Invokes an LLM with specified parameters, handling model selection, cloud fallback, and schema validation."""
    _setup_logging()
    
    # 1. Cloud Pre-check
    force_local = os.getenv("PDD_FORCE_LOCAL", "0") == "1"
    effective_use_cloud = use_cloud
    if effective_use_cloud is None:
        effective_use_cloud = not force_local and os.getenv("PDD_CLOUD_ENABLED") == "1"

    if effective_use_cloud:
        try:
            # Prepare schema for cloud
            schema = output_schema
            if output_pydantic:
                schema = output_pydantic.model_json_schema()
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)

            cloud_res = _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, 
                time, verbose, schema, use_batch_mode, language
            )
            
            # Re-validate locally if pydantic provided
            if output_pydantic and "result" in cloud_res:
                try:
                    res_data = cloud_res["result"]
                    if isinstance(res_data, str):
                        res_data = json.loads(res_data)
                    cloud_res["result"] = output_pydantic.model_validate(res_data)
                except Exception as e:
                    logger.warning(f"Cloud response failed local validation: {e}")
            return cloud_res
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud Warning:[/yellow] {e}. Falling back to local.")
        except InsufficientCreditsError:
            raise

    # 2. Local Execution Path
    load_dotenv(get_default_resolver().resolve_project_root() / ".env")
    csv_df = _load_model_csv()
    candidates = _select_model(strength, csv_df)
    
    # Caching Setup
    resolver = get_default_resolver()
    cache_path = resolver.resolve_project_root() / "litellm_cache.sqlite"
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        litellm.cache = litellm.Cache(type="disk", storage_path=str(cache_path))

    last_exception = None
    
    for model_meta in candidates:
        model_name = model_meta["model"]
        provider = model_meta["provider"]
        api_key_env = model_meta["api_key"]
        
        # Key check
        api_key = os.getenv(api_key_env)
        newly_acquired = False
        if not api_key and api_key_env not in ["nan", "", "EXISTING_KEY"]:
            api_key = _get_api_key_interactively(api_key_env)
            newly_acquired = True
            
        if not api_key and api_key_env not in ["nan", "", "EXISTING_KEY", "VERTEX_CREDENTIALS"]:
            continue

        # Prepare reasoning params
        reasoning_type = model_meta.get("reasoning_type", "none")
        max_r_tokens = int(model_meta.get("max_reasoning_tokens", 0))
        extra_kwargs = {}
        
        if reasoning_type == "budget" and max_r_tokens > 0:
            extra_kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_r_tokens)}
            temperature = 1.0 # Requirement for Anthropic thinking
        elif reasoning_type == "effort":
            effort = "medium"
            if time < 0.33: effort = "low"
            elif time > 0.66: effort = "high"
            
            if "gpt-5" in model_name:
                extra_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                extra_kwargs["reasoning_effort"] = effort

        # Structured Output config
        if output_pydantic or output_schema:
            schema_dict = output_schema or output_pydantic.model_json_schema()
            _ensure_all_properties_required(schema_dict)
            _add_additional_properties_false(schema_dict)
            
            if model_meta.get("structured_output"):
                extra_kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "schema": schema_dict, "strict": True}
                }
            elif "groq" in provider.lower():
                extra_kwargs["response_format"] = {"type": "json_object"}
            
            # LM Studio Bypass
            if "lm_studio" in provider.lower():
                extra_kwargs["extra_body"] = {"response_format": extra_kwargs.get("response_format")}

        # Vertex Logic
        if "vertex" in provider.lower() or "vertex" in model_name:
            extra_kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
            extra_kwargs["vertex_location"] = model_meta.get("location") or os.getenv("VERTEX_LOCATION", "us-central1")
            v_cred = os.getenv("VERTEX_CREDENTIALS")
            if v_cred and Path(v_cred).exists():
                with open(v_cred, "r") as f:
                    extra_kwargs["vertex_credentials"] = f.read()

        # Build Messages
        call_messages = messages
        if not call_messages:
            if not prompt: raise ValueError("Prompt or Messages required.")
            formatted_prompt = prompt.format(**(input_json or {}))
            call_messages = [{"role": "user", "content": formatted_prompt}]

        try:
            # Invocation
            if "gpt-5" in model_name:
                response = litellm.completion(
                    model=model_name,
                    messages=call_messages,
                    num_retries=2,
                    timeout=LLM_CALL_TIMEOUT,
                    api_key=api_key,
                    **extra_kwargs
                )
            elif use_batch_mode:
                response = batch_completion(
                    model=model_name,
                    messages=cast(List[List[Dict]], call_messages),
                    api_key=api_key,
                    **extra_kwargs
                )
            else:
                response = completion(
                    model=model_name,
                    messages=cast(List[Dict], call_messages),
                    temperature=temperature,
                    num_retries=2,
                    timeout=LLM_CALL_TIMEOUT,
                    api_key=api_key,
                    **extra_kwargs
                )

            # Processing Response
            content = response.choices[0].message.content
            if content is None:
                raise SchemaValidationError("Empty response from model.")

            # JSON Parsing & Repair
            result = content
            if output_pydantic or output_schema:
                try:
                    json_str = content
                    if "```json" in content:
                        json_str = content.split("```json")[1].split("```")[0]
                    elif "```" in content:
                        json_str = content.split("```")[1].split("```")[0]
                    
                    try:
                        parsed = json.loads(json_str)
                    except json.JSONDecodeError:
                        repaired = _repair_json_string(json_str)
                        parsed = json.loads(repaired)

                    # Python Syntax Repair (if language is python)
                    if (language is None or language == "python") and isinstance(parsed, dict):
                        for k, v in parsed.items():
                            if k not in ["reasoning", "explanation", "analysis"] and isinstance(v, str):
                                parsed[k] = _repair_python_syntax(_smart_unescape_code(v))

                    if output_pydantic:
                        result = output_pydantic.model_validate(parsed)
                    else:
                        result = parsed
                except Exception as e:
                    raise SchemaValidationError(f"Structure validation failed: {e}")

            # Extraction of thinking
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            if not thinking and hasattr(response, "_hidden_params"):
                thinking = response._hidden_params.get("thinking")

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except litellm.AuthenticationError:
            if newly_acquired and not os.getenv("PDD_FORCE"):
                console.print(f"[red]Authentication failed with new key for {model_name}.[/red]")
                if _is_wsl():
                    console.print("[yellow]WSL Detected:[/yellow] Ensure no carriage returns (\\r) are in your key.")
                os.environ.pop(api_key_env, None)
                # Recursive retry with locals
                return llm_invoke(prompt=prompt, input_json=input_json, strength=strength, temperature=temperature, verbose=verbose, output_pydantic=output_pydantic, output_schema=output_schema, time=time, use_batch_mode=use_batch_mode, messages=messages, language=language, use_cloud=use_cloud)
            continue
        except SchemaValidationError as e:
            logger.warning(f"Model {model_name} failed schema: {e}")
            last_exception = e
            continue
        except Exception as e:
            logger.error(f"Error invoking {model_name}: {e}")
            last_exception = e
            continue

    raise RuntimeError(f"All models exhausted. Last error: {last_exception}")

if __name__ == "__main__":
    # Example usage
    try:
        res = llm_invoke(prompt="Hello, who are you?", strength=0.5)
        print(res)
    except Exception as e:
        print(f"Failed: {e}")