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
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as per requirement
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from pydantic import BaseModel

# --- Configuration & Globals ---
console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

LLM_CALL_TIMEOUT = 120

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when the LLM output fails to validate against the provided schema/Pydantic model."""
    pass

class CloudFallbackError(Exception):
    """Recoverable errors that should trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Logging Setup ---

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    resolver = get_default_resolver()
    log_dir = resolver.resolve_project_root() / "logs"
    log_dir.mkdir(exist_ok=True)
    handler = RotatingFileHandler(log_dir / "pdd.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(verbose: bool = True):
    level = logging.DEBUG if verbose else logging.INFO
    logger.setLevel(level)
    if verbose:
        litellm.set_verbose = True

def _init_logging():
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"
        lite_level = "DEBUG"
    
    logging.basicConfig(level=logging.WARNING)
    logger.setLevel(pdd_level)
    litellm_logger.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- Callbacks ---

def _litellm_success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = response_obj.get("usage", {})
        cost = litellm.completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "cost": cost,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.debug(f"Callback error: {e}")

litellm.success_callback = [_litellm_success_callback]

# --- Helper Utilities ---

def _is_wsl() -> bool:
    return "microsoft-standard" in Path("/proc/version").read_text().lower() if Path("/proc/version").exists() else "WSL_DISTRO_NAME" in os.environ

def _sanitize_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
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
            for item in schema[key]:
                _ensure_all_properties_required(item)
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _ensure_all_properties_required(d)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for p in props.values():
            _add_additional_properties_false(p)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for item in schema[key]:
                _add_additional_properties_false(item)
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _add_additional_properties_false(d)

def _repair_python_syntax(code: str) -> str:
    """Basic repair for truncated strings or triple quotes."""
    code = code.strip()
    if code.count('"""') % 2 != 0:
        code += '\n"""'
    if code.count("'''") % 2 != 0:
        code += "\n'''"
    return code

def _smart_unescape_code(code: str) -> str:
    """Unescape double-escaped newlines while preserving literals."""
    return code.replace("\\n", "\n").replace("\\\\n", "\\n")

# --- Cloud Execution ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> Any:
    if isinstance(result, str):
        try:
            return pydantic_class.model_validate_json(result)
        except Exception:
            # Fallback to string parsing if it was a raw JSON string
            import json
            data = json.loads(result)
            return pydantic_class.model_validate(data)
    return pydantic_class.model_validate(result)

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict, List[Dict]]],
    messages: Optional[List[Dict]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str]
) -> Dict[str, Any]:
    # Placeholder for actual cloud logic using Firebase Auth & Requests
    # In a real implementation, this would fetch a JWT and call the 'llmInvoke' endpoint.
    raise CloudFallbackError("Cloud execution not configured in this standalone stub.")

# --- Model & Key Management ---

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    for p in paths:
        if p.exists():
            df = pd.read_pandas(p) if hasattr(pd, "read_pandas") else pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    'input': row.get('input_cost_per_m', 0) / 1_000_000,
                    'output': row.get('output_cost_per_m', 0) / 1_000_000
                }
            return df
    raise RuntimeError("llm_model.csv not found.")

def _get_api_key_interactively(key_name: str, provider: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
    
    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name} for {provider}")
    val = input(f"Enter {key_name}: ").strip()
    val = _sanitize_key(val)
    
    if val:
        os.environ[key_name] = val
        resolver = get_default_resolver()
        env_path = resolver.resolve_project_root() / ".env"
        
        # In-place update/append to .env
        lines = []
        if env_path.exists():
            lines = env_path.read_text().splitlines()
        
        new_lines = [line for line in lines if not line.startswith(f"{key_name}=") and not line.startswith(f"# {key_name}=")]
        new_lines.append(f"{key_name}={val}")
        env_path.write_text("\n".join(new_lines) + "\n")
        
        console.print(f"[bold red]SECURITY WARNING:[/bold red] Key saved to {env_path}")
    return val

# --- The Main Function ---

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
    
    _init_logging()
    if verbose: set_verbose_logging(True)

    # 1. Cloud Execution Path
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1" # Simplified auto-detect
    
    if use_cloud:
        try:
            effective_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
            cloud_res = _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, time, verbose, effective_schema, use_batch_mode, language
            )
            if output_pydantic:
                cloud_res['result'] = _validate_with_pydantic(cloud_res['result'], output_pydantic)
            return cloud_res
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")

    # 2. Local Model Selection
    df = _load_model_csv()
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter by API key availability
    def has_key(row):
        kn = str(row['api_key'])
        if not kn or kn == "nan" or kn == "EXISTING_KEY": return True
        return os.getenv(kn) is not None or not os.getenv("PDD_FORCE")

    available_df = df[df.apply(has_key, axis=1)].copy()
    if available_df.empty:
        raise RuntimeError("No models available with valid API keys.")

    # Model Selection Logic (Simplification of ELO/Cost interpolation)
    if base_model_name and base_model_name in available_df['model'].values:
        base_row = available_df[available_df['model'] == base_model_name].iloc[0]
    else:
        base_row = available_df.iloc[0]

    # For this implementation, we pick the base row or its neighbors based on strength
    # A production version would sort by ELO/Cost and slice
    selected_model_row = base_row 
    model_name = selected_model_row['model']
    provider = selected_model_row['provider']
    api_key_name = str(selected_model_row['api_key'])

    # 3. API Key Handling
    api_key_val = None
    if api_key_name and api_key_name != "nan" and api_key_name != "EXISTING_KEY":
        api_key_val = os.getenv(api_key_name)
        if not api_key_val:
            api_key_val = _get_api_key_interactively(api_key_name, provider)
            if not api_key_val:
                # Skip this model and retry selection if possible, else error
                raise RuntimeError(f"API Key {api_key_name} required.")

    # 4. Prepare Parameters
    final_messages = messages
    if not final_messages:
        # Template interpolation
        text = prompt if prompt else ""
        if isinstance(input_json, dict):
            for k, v in input_json.items():
                text = text.replace(f"{{{{{k}}}}}", str(v))
        final_messages = [{"role": "user", "content": text}]

    # Reasoning
    reasoning_type = str(selected_model_row.get('reasoning_type', 'none')).lower()
    max_reasoning = int(selected_model_row.get('max_reasoning_tokens', 0))
    completion_kwargs = {
        "model": model_name,
        "messages": final_messages,
        "temperature": temperature,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    if reasoning_type == "budget":
        budget = int(time * max_reasoning)
        if "anthropic" in provider.lower():
            completion_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
            completion_kwargs["temperature"] = 1.0 # Required for Anthropic thinking
    elif reasoning_type == "effort":
        effort = "medium"
        if time < 0.33: effort = "low"
        elif time > 0.66: effort = "high"
        completion_kwargs["reasoning_effort"] = effort

    # Structured Output Setup
    supports_structured = str(selected_model_row.get('structured_output', 'False')).lower() == 'true'
    if (output_pydantic or output_schema) and supports_structured:
        if "gpt-5" in model_name: # Hypothetical Responses API
             completion_kwargs["response_format"] = {"type": "json_schema", "json_schema": output_schema or output_pydantic.model_json_schema()}
        else:
             completion_kwargs["response_format"] = output_pydantic or output_schema

    # 5. Invocation Loop (Retries & Auth)
    try:
        if use_batch_mode:
            response = litellm.batch_completion(**completion_kwargs)
            # Batch logic extraction...
            return {"result": response, "model_name": model_name}
        
        response = litellm.completion(**completion_kwargs)
        content = response.choices[0].message.content
        
        # Thinking extraction
        thinking = None
        if hasattr(response.choices[0].message, 'reasoning_content'):
            thinking = response.choices[0].message.reasoning_content
        elif '_hidden_params' in response and 'thinking' in response['_hidden_params']:
            thinking = response['_hidden_params']['thinking']

        # Parsing / Validation
        result = content
        if output_pydantic:
            # Handle non-structured-native models by manual parse
            if not supports_structured:
                # Regex extract JSON block
                match = re.search(r"```json\s*(.*?)\s*```", content, re.DOTALL)
                json_str = match.group(1) if match else content
                result = output_pydantic.model_validate_json(json_str)
            else:
                # LiteLLM usually returns the object in message.content or as a parsed object
                result = content # or validated

        return {
            "result": result,
            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
            "model_name": model_name,
            "thinking_output": thinking
        }

    except Exception as e:
        logger.error(f"LLM Call failed: {e}")
        if "Authentication" in str(e) and _is_wsl():
            console.print("[bold yellow]WSL detected:[/bold yellow] Ensure your API key doesn't have hidden carriage returns (\\r).")
        raise

if __name__ == "__main__":
    # Example usage
    load_dotenv()
    res = llm_invoke(prompt="Hello {{name}}", input_json={"name": "World"}, strength=0.5)
    console.print(res)