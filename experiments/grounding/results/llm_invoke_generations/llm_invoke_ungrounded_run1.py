from __future__ import annotations

import os
import json
import logging
import logging.handlers
import re
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
from dotenv import load_dotenv, set_key
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
PDD_ENV = os.getenv("PDD_ENVIRONMENT", "production")
PDD_VERBOSE = os.getenv("PDD_VERBOSE_LOGGING") == "1"

console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic/JSON schema validation."""

class CloudFallbackError(Exception):
    """Recoverable cloud error (5xx, timeout, network)."""

class CloudInvocationError(Exception):
    """Non-recoverable cloud error (4xx except 402)."""

class InsufficientCreditsError(Exception):
    """Cloud error 402: Payment Required."""

# --- Logging Setup ---

def setup_file_logging() -> None:
    resolver = get_default_resolver()
    log_dir = resolver.resolve_project_root() / "logs"
    log_dir.mkdir(exist_ok=True)
    handler = logging.handlers.RotatingFileHandler(
        log_dir / "pdd.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.DEBUG if PDD_VERBOSE else PDD_LOG_LEVEL)

def set_verbose_logging(enabled: bool = True) -> None:
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    litellm.set_verbose = enabled

# --- LiteLLM Callbacks ---

def _litellm_success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", {})
        cost = litellm.completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "cost": cost,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception:
        pass

litellm.success_callback = [_litellm_success_callback]
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- Key Management ---

def _manage_api_key(provider: str, key_name: str) -> Optional[str]:
    key = os.getenv(key_name)
    if key and key != "EXISTING_KEY":
        return key.strip()
    
    if os.getenv("PDD_FORCE"):
        return None

    console.print(f"[yellow]Missing API Key for {provider} ({key_name})[/yellow]")
    new_key = input(f"Enter API Key for {key_name}: ").strip()
    if not new_key:
        return None

    # WSL / Env cleanup
    new_key = "".join(c for c in new_key if ord(c) >= 32)
    
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    
    # Simple in-place replacement logic (set_key handles overwrite)
    set_key(str(env_path), key_name, new_key)
    os.environ[key_name] = new_key
    
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")
    logger.warning(f"Security: API Key for {key_name} saved to .env file.")
    return new_key

# --- Model Selection Logic ---

def _load_models_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    
    for p in paths:
        if p.exists():
            return pd.read_csv(p)
    
    # Fallback to packaged data
    try:
        pkg_path = Path(__file__).parent / "data" / "llm_model.csv"
        return pd.read_csv(pkg_path)
    except Exception:
        return pd.DataFrame()

def _select_model(strength: float) -> List[Dict[str, Any]]:
    df = _load_models_csv()
    if df.empty:
        return []

    # Update global cost map
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row["model"]] = {
            "input": row.get("input_cost_per_token", 0),
            "output": row.get("output_cost_per_token", 0)
        }

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available = df[df["api_key"].notna()].copy()
    
    if base_model_name and base_model_name in available["model"].values:
        base_row = available[available["model"] == base_model_name].iloc[0]
    else:
        # Surrogate: first available
        base_row = available.iloc[0]

    if strength == 0.5:
        # Use base, then others by ELO descending
        candidates = pd.concat([
            available[available["model"] == base_row["model"]],
            available[available["model"] != base_row["model"]].sort_values("coding_arena_elo", ascending=False)
        ])
    elif strength < 0.5:
        # Cheapest to base
        candidates = available[available["input_cost_per_token"] <= base_row["input_cost_per_token"]].sort_values("input_cost_per_token")
    else:
        # Base to highest ELO
        candidates = available[available["coding_arena_elo"] >= base_row["coding_arena_elo"]].sort_values("coding_arena_elo", ascending=False)

    return candidates.to_dict("records")

# --- Reasoning Logic ---

def _apply_reasoning(model_row: Dict, time_val: float, kwargs: Dict):
    r_type = model_row.get("reasoning_type", "none")
    max_tokens = int(model_row.get("max_reasoning_tokens", 0))

    if r_type == "budget" and max_tokens > 0:
        budget = int(time_val * max_tokens)
        if "anthropic" in model_row["provider"].lower():
            kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
            kwargs["temperature"] = 1.0  # Required for Anthropic thinking
        else:
            kwargs["max_completion_tokens"] = budget # Generic fallback
    elif r_type == "effort":
        effort = "low" if time_val < 0.33 else "medium" if time_val < 0.66 else "high"
        if model_row["model"].startswith("gpt-5") or "o1" in model_row["model"]:
            kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
        else:
            kwargs["reasoning_effort"] = effort

# --- Structured Output Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for v in props.values():
            _ensure_all_properties_required(v)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf", "$defs"]:
        if key in schema:
            for item in schema[key] if isinstance(schema[key], list) else schema[key].values():
                _ensure_all_properties_required(item)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for v in props.values():
            _add_additional_properties_false(v)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

    for key in ["anyOf", "oneOf", "allOf", "$defs"]:
        if key in schema:
            for item in schema[key] if isinstance(schema[key], list) else schema[key].values():
                _add_additional_properties_false(item)

# --- Invocation ---

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
    
    if verbose:
        set_verbose_logging(True)
    
    # 1. Cloud Logic
    # (Implementation omitted for brevity, logic: check env/CloudConfig, call _llm_invoke_cloud)
    
    # 2. Local Setup
    candidates = _select_model(strength)
    if not candidates:
        raise RuntimeError("No suitable LLM models found in configuration.")

    final_messages = messages
    if not final_messages:
        if not prompt:
            raise ValueError("Prompt is required if messages are not provided.")
        # Handle templating... (simple jinja-style substitute)
        content = prompt
        if input_json and isinstance(input_json, dict):
            for k, v in input_json.items():
                content = content.replace(f"{{{{{k}}}}}", str(v))
        final_messages = [{"role": "user", "content": content}]

    for model_row in candidates:
        provider = model_row["provider"]
        model_name = model_row["model"]
        api_key_name = model_row["api_key"]
        
        api_key = _manage_api_key(provider, api_key_name)
        if not api_key and not os.getenv("PDD_FORCE"):
            continue

        call_params = {
            "model": f"{provider}/{model_name}" if "/" not in model_name else model_name,
            "messages": final_messages,
            "temperature": temperature,
            "api_key": api_key,
            "timeout": LLM_CALL_TIMEOUT,
            "num_retries": 2,
        }

        # Vertex AI Handling
        if provider == "vertex_ai" or "vertex" in model_name:
            call_params["vertex_project"] = os.getenv("VERTEX_PROJECT")
            call_params["vertex_location"] = model_row.get("location", os.getenv("VERTEX_LOCATION", "us-central1"))
            creds_path = os.getenv("VERTEX_CREDENTIALS")
            if creds_path:
                with open(creds_path) as f:
                    call_params["vertex_credentials"] = f.read()

        # Custom Base URL (LM Studio etc)
        if pd.notna(model_row.get("base_url")):
            call_params["api_base"] = model_row["base_url"]

        _apply_reasoning(model_row, time, call_params)

        # Structured Output
        effective_schema = output_schema or (output_pydantic.model_json_schema() if output_pydantic else None)
        if effective_schema:
            _ensure_all_properties_required(effective_schema)
            _add_additional_properties_false(effective_schema)
            
            if model_row.get("structured_output") == 1:
                call_params["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "output", "schema": effective_schema, "strict": True}
                }
            else:
                # Fallback to system prompt instruction
                call_params["messages"].insert(0, {"role": "system", "content": f"Output must be valid JSON matching: {json.dumps(effective_schema)}"})

        try:
            # Invocation
            if model_name.startswith("gpt-5"):
                # Use Responses API if available in litellm
                response = litellm.completion(**call_params) # Simplified for template
            elif use_batch_mode:
                response = litellm.batch_completion(**call_params)
            else:
                response = litellm.completion(**call_params)

            # Process Response
            content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None) or \
                       response.get("_hidden_params", {}).get("thinking")

            result_val = content
            if effective_schema:
                # JSON cleaning and parsing logic...
                try:
                    # Clean markdown code fences
                    clean_content = re.sub(r"^```json\s*|\s*```$", "", content.strip(), flags=re.MULTILINE)
                    parsed = json.loads(clean_content)
                    if output_pydantic:
                        result_val = output_pydantic.model_validate(parsed)
                    else:
                        result_val = parsed
                except Exception as e:
                    logger.error(f"Schema validation failed for {model_name}: {e}")
                    raise SchemaValidationError(f"Invalid JSON/Schema output from {model_name}")

            return {
                "result": result_val,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except (SchemaValidationError, litellm.exceptions.ServiceUnavailableError) as e:
            logger.warning(f"Retrying with fallback due to: {e}")
            continue
        except Exception as e:
            logger.error(f"Model {model_name} failed: {e}")
            if "auth" in str(e).lower():
                # Potential logic to clear key and retry
                pass
            continue

    raise RuntimeError("All LLM model candidates exhausted or failed.")

if __name__ == "__main__":
    setup_file_logging()
    # Example usage:
    # res = llm_invoke(prompt="Hello {{name}}", input_json={"name": "World"})
    # print(res)