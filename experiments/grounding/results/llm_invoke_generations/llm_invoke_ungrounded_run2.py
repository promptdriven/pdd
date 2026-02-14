from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import completion, batch_completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports (as per package requirement)
from . import DEFAULT_STRENGTH, DEFAULT_TIME

if TYPE_CHECKING:
    from .path_resolution import PathResolver

# --- Global Configuration & Constants ---
CONSOLE = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
_NEWLY_ACQUIRED_KEYS: set[str] = set()

LLM_CALL_TIMEOUT = 120

# --- Exceptions ---
class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic/JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable errors that trigger fallback from cloud to local."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable errors during cloud execution."""
    pass

class InsufficientCreditsError(Exception):
    """Raised when the user has 402 Payment Required."""
    pass

# --- Logging Setup ---
def setup_logging():
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = "DEBUG"

    logging.basicConfig(level=logging.WARNING)
    logger.setLevel(log_level)
    litellm_logger.setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- Path Resolution Logic ---
def get_project_root() -> Path:
    """Detect project root using markers."""
    cwd = Path.cwd()
    # Simplified version of resolve_project_root logic
    for parent in [cwd] + list(cwd.parents):
        if any((parent / marker).exists() for marker in [".git", "pyproject.toml", ".env", "data"]):
            return parent
    return cwd

def load_models_csv() -> pd.DataFrame:
    root = get_project_root()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    "input": row.get('input_cost', 0),
                    "output": row.get('output_cost', 0)
                }
            return df
    return pd.DataFrame()

# --- Utility Functions ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for sub_schema in props.values():
            _ensure_all_properties_required(sub_schema)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for sub in schema.get("properties", {}).values():
            _add_additional_properties_false(sub)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _add_additional_properties_false(sub)

def _smart_unescape_code(text: str) -> str:
    """Fixes double escaped newlines in code fields."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _repair_truncated_json(text: str) -> str:
    text = text.strip()
    if not text: return text
    # Simple brackets closure
    open_braces = text.count('{') - text.count('}')
    open_brackets = text.count('[') - text.count(']')
    text += '}' * open_braces
    text += ']' * open_brackets
    return text

def _parse_llm_json(content: str) -> Any:
    # 1. Try fenced code block
    match = re.search(r"```json\s*(.*?)\s*```", content, re.DOTALL)
    if match:
        content = match.group(1)
    
    # 2. Try to find the first '{' and last '}'
    start = content.find('{')
    end = content.rfind('}')
    if start != -1 and end != -1:
        content = content[start:end+1]
    
    try:
        return json.loads(content)
    except json.JSONDecodeError:
        try:
            return json.loads(_repair_truncated_json(content))
        except:
            raise SchemaValidationError("Could not parse LLM output as JSON")

# --- API Key Management ---
def handle_missing_key(key_name: str, provider: str) -> None:
    if os.getenv("PDD_FORCE"):
        return

    CONSOLE.print(f"[bold yellow]Missing API Key for {provider}: {key_name}[/bold yellow]")
    key_val = input(f"Enter {key_name}: ").strip()
    if not key_val:
        return

    # WSL Check
    if Path("/proc/version").exists() or os.getenv("WSL_DISTRO_NAME"):
        key_val = key_val.strip("\r\n\t ")

    os.environ[key_name] = key_val
    _NEWLY_ACQUIRED_KEYS.add(key_name)

    # Save to .env
    root = get_project_root()
    env_path = root / ".env"
    set_key(str(env_path), key_name, key_val)
    CONSOLE.print(f"[bold green]Key saved to {env_path}[/bold green]")

# --- Cloud Execution ---
def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No cloud token found")
    
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    try:
        response = requests.post(
            url, 
            json=payload, 
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits on PDD Cloud")
        if response.status_code in [401, 403]:
            # Clear cache logic here if applicable
            raise CloudFallbackError(f"Cloud Auth Error: {response.status_code}")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {str(e)}")

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
    load_dotenv(get_project_root() / ".env")
    setup_logging()

    # Cloud Check
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
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
            if output_pydantic and cloud_res.get("result"):
                cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            return cloud_res
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # Model Selection
    df = load_models_csv()
    if df.empty:
        raise RuntimeError("Model CSV not found or empty")

    # Filter by API Key presence in environment
    df['has_key'] = df['api_key'].apply(lambda k: bool(os.getenv(k)) or k in ["EXISTING_KEY", ""])
    available_df = df[df['has_key']].sort_values('coding_arena_elo')

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_model_row = df[df['model'] == base_model_name].iloc[0] if base_model_name in df['model'].values else available_df.iloc[0]

    # Interpolation logic
    if strength == 0.5:
        candidates = [base_model_row['model']] + available_df[available_df['model'] != base_model_row['model']].sort_values('coding_arena_elo', ascending=False)['model'].tolist()
    elif strength < 0.5:
        cheaper = available_df[available_df['input_cost'] <= base_model_row['input_cost']].sort_values('input_cost')
        candidates = cheaper['model'].tolist()
    else:
        better = available_df[available_df['coding_arena_elo'] >= base_model_row['coding_arena_elo']].sort_values('coding_arena_elo', ascending=False)
        candidates = better['model'].tolist()

    # Preparation
    if not messages:
        # Prompt templating would happen here
        messages = [{"role": "user", "content": prompt or str(input_json)}]

    last_error = None
    for model_name in candidates:
        row = df[df['model'] == model_name].iloc[0]
        api_key_name = row['api_key']
        
        # Verify Auth
        if api_key_name and not os.getenv(api_key_name) and api_key_name != "EXISTING_KEY":
            handle_missing_key(api_key_name, row['provider'])
            if not os.getenv(api_key_name): continue

        try:
            # Reasoning Prep
            reasoning_type = row.get('reasoning_type', 'none')
            kwargs = {
                "model": model_name,
                "messages": messages,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT,
            }

            # Reasoning Logic
            if reasoning_type == 'budget':
                max_t = int(row.get('max_reasoning_tokens', 1024))
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_t)}
                kwargs["temperature"] = 1.0 # Anthropic requirement
            elif reasoning_type == 'effort':
                effort = "medium"
                if time < 0.33: effort = "low"
                elif time > 0.66: effort = "high"
                kwargs["reasoning_effort"] = effort

            # Structured Output
            if output_pydantic or output_schema:
                if row.get('structured_output'):
                    schema = output_schema or _pydantic_to_json_schema(output_pydantic)
                    kwargs["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "strict": True, "schema": schema}}

            # Call
            response = completion(**kwargs)
            
            # Post Process
            content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, 'reasoning_content', None) or response._hidden_params.get('thinking')

            result = content
            if output_pydantic or output_schema:
                data = _parse_llm_json(content)
                if output_pydantic:
                    result = output_pydantic.model_validate(data)
                else:
                    result = data

            cost = completion_cost(response)
            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.warning(f"Model {model_name} failed: {e}")
            if "authentication" in str(e).lower() and api_key_name in _NEWLY_ACQUIRED_KEYS:
                handle_missing_key(api_key_name, row['provider'])
            last_error = e
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_error}")

if __name__ == "__main__":
    # Quick CLI test
    res = llm_invoke(prompt="Hello, who are you?", strength=0.5)
    CONSOLE.print(res)