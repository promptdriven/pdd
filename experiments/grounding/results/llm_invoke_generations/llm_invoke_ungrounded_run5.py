from __future__ import annotations

import os
import json
import logging
import logging.handlers
import re
import platform
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv, set_key
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as required by package structure
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    PDD_MODEL_DEFAULT,
    LLM_CALL_TIMEOUT,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
CONSOLE = Console()

# Logging setup
logger = logging.getLogger("pdd.llm_invoke")
lite_logger = logging.getLogger("litellm")

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud errors (network, auth, 5xx) triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Logging Configuration ---

def setup_file_logging() -> None:
    resolver = get_default_resolver()
    log_dir = resolver.resolve_project_root() / "logs"
    log_dir.mkdir(exist_ok=True)
    handler = logging.handlers.RotatingFileHandler(
        log_dir / "llm_invoke.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(verbose: bool) -> None:
    level = logging.DEBUG if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1" else logging.INFO
    logger.setLevel(level)
    
    # LiteLLM Level logic
    lite_level_env = os.getenv("LITELLM_LOG_LEVEL")
    if lite_level_env:
        lite_logger.setLevel(lite_level_env.upper())
    elif os.getenv("PDD_ENVIRONMENT") == "production":
        lite_logger.setLevel(logging.WARNING)
    else:
        lite_logger.setLevel(logging.INFO)

# --- LiteLLM Callbacks ---

def _litellm_success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        cost = litellm.completion_cost(completion_response=response_obj)
    except Exception:
        cost = 0.0
    
    usage = getattr(response_obj, "usage", {})
    _LAST_CALLBACK_DATA = {
        "cost": cost,
        "usage": usage,
        "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
    }

litellm.success_callback = [_litellm_success_callback]

# --- Helper Functions ---

def _is_wsl() -> bool:
    return "microsoft-standard" in platform.release().lower() or os.getenv("WSL_DISTRO_NAME") is not None

def _sanitize_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_api_key(key_name: str, provider: str) -> Optional[str]:
    key = os.getenv(key_name)
    if key and key != "EXISTING_KEY":
        return _sanitize_key(key)
    
    if os.getenv("PDD_FORCE"):
        return None

    CONSOLE.print(f"[yellow]Missing API Key for {provider} ({key_name}).[/yellow]")
    user_key = input(f"Please enter your {key_name}: ").strip()
    if not user_key:
        return None
    
    user_key = _sanitize_key(user_key)
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    
    # Remove old keys and save new one
    set_key(str(env_path), key_name, user_key)
    os.environ[key_name] = user_key
    
    CONSOLE.print(f"[bold green]Key saved to {env_path}. Ensure this file is gitignored![/bold green]")
    return user_key

def _get_model_candidates(strength: float) -> List[Dict[str, Any]]:
    resolver = get_default_resolver()
    csv_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    
    df = None
    for p in csv_paths:
        if p.exists():
            df = pd.read_csv(p)
            break
    
    if df is None:
        raise RuntimeError("No llm_model.csv found in search paths.")

    # Fill rates for callback fallback
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row["model"]] = {
            "input": row.get("input_cost_per_m", 0) / 1_000_000,
            "output": row.get("output_cost_per_m", 0) / 1_000_000
        }

    # Surrogate logic
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available_models = df[df["api_key"].notna() | (df["provider"] == "lm_studio")].copy()
    
    if base_model_name and base_model_name in available_models["model"].values:
        base_row = available_models[available_models["model"] == base_model_name].iloc[0]
    else:
        base_row = available_models.iloc[0]

    # Interpolation
    if strength == 0.5:
        sorted_models = available_models.sort_values("coding_arena_elo", ascending=False)
    elif strength < 0.5:
        # Interpolate by cost (cheapest to base)
        sorted_models = available_models.sort_values("input_cost_per_m", ascending=True)
    else:
        # Interpolate by ELO (base to highest)
        sorted_models = available_models.sort_values("coding_arena_elo", ascending=False)

    return sorted_models.to_dict("records")

def _repair_json(text: str) -> str:
    """Brute force JSON repair for common truncation/fence issues."""
    text = text.strip()
    if text.startswith("```json"):
        match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
        if match: text = match.group(1)
    
    # Try to find balanced braces if junk exists outside
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end != -1:
        text = text[start : end + 1]
    
    # Basic truncation repair
    if text.count("{") > text.count("}"):
        text += "}" * (text.count("{") - text.count("}"))
    return text

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for v in props.values():
            _ensure_all_properties_required(v)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for v in schema.get("properties", {}).values():
            _add_additional_properties_false(v)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf", "$defs"]:
        if key in schema:
            for item in schema[key]:
                _add_additional_properties_false(item)

# --- Cloud Transport ---

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
        resp = requests.post(
            url,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if resp.status_code == 401 or resp.status_code == 403:
            raise CloudFallbackError(f"Cloud Auth Error: {resp.text}")
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits on PDD Cloud.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Network error: {str(e)}")

# --- Main Invocation Function ---

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
    set_verbose_logging(verbose)
    
    # 1. Cloud Execution Detection
    if use_cloud is None:
        use_cloud = (os.getenv("PDD_FORCE_LOCAL") != "1" and os.getenv("PDD_CLOUD_ENABLED") == "1")

    if use_cloud:
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
            if output_pydantic and "result" in cloud_res:
                cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            return cloud_res
        except CloudFallbackError as e:
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise
        except Exception as e:
            CONSOLE.print(f"[red]Cloud invocation error: {e}[/red]")

    # 2. Local Preparation
    candidates = _get_model_candidates(strength)
    if not candidates:
        raise RuntimeError("No models available for selection.")

    # 3. Model Iteration / Retry Loop
    for model_info in candidates:
        model_name = model_info["model"]
        provider = model_info["provider"]
        
        # Key Handling
        api_key_name = model_info.get("api_key")
        api_key = None
        if provider == "lm_studio":
            api_key = "lm-studio"
        elif api_key_name:
            api_key = _ensure_api_key(api_key_name, provider)
            if not api_key: continue

        # Formatting Messages
        current_messages = messages
        if not current_messages:
            if not prompt: raise ValueError("Prompt or Messages required.")
            # Simple placeholder injection
            system_prompt = prompt
            if input_json:
                # Basic string formatting if prompt has {{}}
                fmt_data = input_json[0] if isinstance(input_json, list) else input_json
                for k, v in fmt_data.items():
                    system_prompt = system_prompt.replace(f"{{{{{k}}}}}", str(v))
            current_messages = [{"role": "user", "content": system_prompt}]

        # Reasoning & Extra Params
        extra_params: Dict[str, Any] = {
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
            "drop_params": os.getenv("LITELLM_DROP_PARAMS", "True") == "True"
        }
        
        reasoning_type = model_info.get("reasoning_type", "none")
        max_tokens = model_info.get("max_reasoning_tokens", 0)
        
        if reasoning_type == "budget" and max_tokens > 0:
            budget = int(time * max_tokens)
            extra_params["thinking"] = {"type": "enabled", "budget_tokens": budget}
            temperature = 1.0 # Required for Anthropic thinking
        elif reasoning_type == "effort":
            effort = "medium"
            if time < 0.3: effort = "low"
            elif time > 0.7: effort = "high"
            extra_params["reasoning_effort"] = effort

        # Structured Output Setup
        if output_pydantic or output_schema:
            schema = output_schema or _pydantic_to_json_schema(output_pydantic) # type: ignore
            if model_info.get("structured_output"):
                extra_params["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "strict": True, "schema": schema}
                }
            else:
                current_messages[0]["content"] += f"\n\nReturn ONLY a JSON object matching this schema: {json.dumps(schema)}"

        # Invoke
        try:
            if "gpt-5" in model_name: # Surrogate for Responses API check
                 # Responses API implementation logic here...
                 response = litellm.completion(model=model_name, messages=current_messages, api_key=api_key, **extra_params)
            elif use_batch_mode:
                response = litellm.batch_completion(model=model_name, messages=current_messages, api_key=api_key, **extra_params)
            else:
                response = litellm.completion(model=model_name, messages=current_messages, api_key=api_key, temperature=temperature, **extra_params)

            # Processing
            choice = response.choices[0]
            content = choice.message.content
            
            # Unpack results
            if output_pydantic:
                parsed = json.loads(_repair_json(content))
                result = output_pydantic.model_validate(parsed)
            elif output_schema:
                result = json.loads(_repair_json(content))
            else:
                result = content

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": getattr(choice.message, "reasoning_content", None)
            }

        except Exception as e:
            logger.error(f"Model {model_name} failed: {e}")
            if _is_wsl() and "auth" in str(e).lower():
                CONSOLE.print("[bold red]WSL detected: Check for carriage returns in your API keys![/bold red]")
            continue

    raise RuntimeError("All LLM candidates exhausted without success.")