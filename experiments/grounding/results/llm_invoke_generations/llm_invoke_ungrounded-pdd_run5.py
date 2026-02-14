from __future__ import annotations

import ast
import json
import logging
import os
import re
import time as time_module
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports (as per requirement)
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
CONSOLE = Console()
LOGGER = logging.getLogger("pdd.llm_invoke")
LITELLM_LOGGER = logging.getLogger("litellm")
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Custom Exceptions ---
class SchemaValidationError(Exception):
    """Raised when structured output fails validation, triggering model fallback."""
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

# --- Logging Setup ---
def setup_logging() -> None:
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO")
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"
    
    env = os.getenv("PDD_ENVIRONMENT", "production")
    litellm_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING" if env == "production" else "INFO")
    
    logging.basicConfig(level=logging.WARNING)
    LOGGER.setLevel(pdd_level)
    LITELLM_LOGGER.setLevel(litellm_level)

def setup_file_logging(log_dir: Path) -> None:
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(log_dir / "pdd.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    LOGGER.addHandler(handler)

# --- Path & Env Resolution ---
def initialize_environment() -> Path:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    env_path = project_root / ".env"
    if env_path.exists():
        load_dotenv(env_path)
    
    # LiteLLM Globals
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # Caching Setup
    cache_disabled = os.getenv("LITELLM_CACHE_DISABLE") == "1"
    if not cache_disabled:
        if os.getenv("GCS_BUCKET_NAME") and os.getenv("GCS_HMAC_ACCESS_KEY_ID"):
            litellm.cache = litellm.Cache(type="s3", s3_bucket=os.getenv("GCS_BUCKET_NAME"), 
                                         s3_region_name="auto", s3_endpoint_url="https://storage.googleapis.com")
        else:
            cache_path = project_root / "litellm_cache.sqlite"
            litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(cache_path))
    
    return project_root

def load_models_csv(project_root: Path) -> pd.DataFrame:
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {'input': row['input'], 'output': row['output']}
            return df
    raise FileNotFoundError("Could not find llm_model.csv in any expected location.")

# --- API Key Management ---
def _get_api_key_interactively(key_name: str, model_name: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
    
    CONSOLE.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name} for model {model_name}")
    key = input(f"Enter API key for {key_name}: ").strip()
    # WSL Sanitization
    key = key.replace('\r', '').replace('\n', '')
    
    if key:
        os.environ[key_name] = key
        resolver = get_default_resolver()
        project_root = resolver.resolve_project_root()
        env_path = project_root / ".env"
        # Update .env in place
        set_key(str(env_path), key_name, key)
        LOGGER.warning(f"Security: API key {key_name} saved to {env_path}")
    return key

# --- Helper Logic: Model Selection ---
def _select_model_candidates(df: pd.DataFrame, strength: float) -> List[pd.Series]:
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available = df[df['api_key'].apply(lambda k: os.getenv(k) is not None or k in ["EXISTING_KEY", ""])]
    
    if available.empty:
        # If none have keys, we still look at the whole list to prompt for one
        available = df
        
    if base_model_name and base_model_name in available['model'].values:
        base_model = available[available['model'] == base_model_name].iloc[0]
    else:
        base_model = available.iloc[0]

    if strength == 0.5:
        candidates = [base_model]
        # Fallback to next highest ELO
        others = available[available['model'] != base_model['model']].sort_values('coding_arena_elo', ascending=False)
        return candidates + [row for _, row in others.iterrows()]

    if strength < 0.5:
        # Interpolate by cost (cheapest to base)
        subset = available[available['input'] <= base_model['input']].sort_values('input', ascending=True)
    else:
        # Interpolate by ELO (base to highest)
        subset = available[available['coding_arena_elo'] >= base_model['coding_arena_elo']].sort_values('coding_arena_elo', ascending=False)
    
    return [row for _, row in subset.iterrows()]

# --- Helper Logic: Reasoning & Params ---
def _get_reasoning_params(row: pd.Series, time: float) -> Dict[str, Any]:
    r_type = row.get('reasoning_type', 'none')
    max_tokens = int(row.get('max_reasoning_tokens', 0))
    
    if r_type == 'budget' and max_tokens > 0:
        budget = int(time * max_tokens)
        if "claude" in row['model']:
            return {"thinking": {"type": "enabled", "budget_tokens": budget}}
        return {"max_completion_tokens": budget}
    
    if r_type == 'effort':
        effort = "low" if time < 0.33 else "medium" if time < 0.66 else "high"
        if "gpt-5" in row['model']:
            return {"reasoning": {"effort": effort, "summary": "auto"}}
        return {"reasoning_effort": effort}
        
    return {}

# --- Structured Output Cleaning ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        schema["required"] = list(props.keys())
        for p in props.values():
            _ensure_all_properties_required(p)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for p in schema.get("properties", {}).values():
            _add_additional_properties_false(p)
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for item in schema[key]:
                _add_additional_properties_false(item)

# --- Python Code Repair ---
def _repair_python_syntax(code: str) -> str:
    # Remove trailing unclosed quotes/triples
    code = code.strip()
    if code.count('"""') % 2 != 0: code += '"""'
    if code.count("'''") % 2 != 0: code += "'''"
    return code

def _smart_unescape_code(content: str) -> str:
    return content.replace("\\n", "\n").replace("\\\"", "\"")

# --- Cloud Execution ---
def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

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
    language: Optional[str],
) -> Dict[str, Any]:
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No cloud token available.")

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
        if resp.status_code == 401 or resp.status_code == 403:
            raise CloudFallbackError("Cloud auth failed.")
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {resp.status_code}")
        
        data = resp.json()
        if "error" in data:
            raise CloudInvocationError(data["error"])
        return data
    except requests.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

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
    """
    Invokes an LLM via LiteLLM or PDD Cloud. Handles model selection, reasoning,
    structured output, and fallback logic.
    """
    setup_logging()
    root = initialize_environment()
    
    # Cloud Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is True or (use_cloud is None and not force_local and os.getenv("PDD_CLOUD_TOKEN")):
        try:
            schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
            cloud_res = _llm_invoke_cloud(prompt, input_json, messages, strength, temperature, time, verbose, schema, use_batch_mode, language)
            
            if output_pydantic:
                cloud_res['result'] = output_pydantic.model_validate(cloud_res['result'])
            return cloud_res
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud Warning:[/yellow] {e}. Falling back to local.")
        except InsufficientCreditsError:
            raise

    # Local Path
    df = load_models_csv(root)
    candidates = _select_model_candidates(df, strength)
    
    # Callback to track cost
    def success_callback(kwargs, response_obj, start_time, end_time):
        global _LAST_CALLBACK_DATA
        _LAST_CALLBACK_DATA = {
            'cost': completion_cost(response_obj),
            'usage': response_obj.usage,
            'model': response_obj.model
        }
    litellm.success_callback = [success_callback]

    # Prepare Messages
    if not messages:
        if not prompt: raise ValueError("Prompt or Messages required.")
        formatted_prompt = prompt.format(**(input_json if isinstance(input_json, dict) else {}))
        current_messages = [{"role": "user", "content": formatted_prompt}]
    else:
        current_messages = messages

    for attempt_idx, model_row in enumerate(candidates):
        model_name = model_row['model']
        provider = model_row['provider']
        key_name = model_row['api_key']
        
        # Check API Key
        api_key = os.getenv(key_name)
        if not api_key and key_name not in ["", "EXISTING_KEY"]:
            api_key = _get_api_key_interactively(key_name, model_name)
            if not api_key: continue

        # Build Params
        params = {
            "model": model_name,
            "messages": current_messages,
            "temperature": temperature,
            "timeout": LLM_CALL_TIMEOUT,
            "num_retries": 2,
            "api_key": api_key
        }
        
        # Reasoning
        reasoning_params = _get_reasoning_params(model_row, time)
        params.update(reasoning_params)
        if "thinking" in reasoning_params:
            params["temperature"] = 1.0 # Anthropic requirement

        # Structured Output
        effective_schema = output_schema or (output_pydantic.model_json_schema() if output_pydantic else None)
        if effective_schema and model_row.get('structured_output'):
            _ensure_all_properties_required(effective_schema)
            _add_additional_properties_false(effective_schema)
            params["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": effective_schema, "strict": True}}
        
        # LM Studio Overrides
        if provider.lower() == "lm_studio":
            params["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
            if effective_schema:
                params["extra_body"] = {"response_format": params.pop("response_format")}

        try:
            # Invocation
            if use_batch_mode:
                resp = batch_completion(**params)
            elif "gpt-5" in model_name:
                # Mock responses() call logic as litellm.responses isn't always in standard stubs
                resp = completion(**params) 
            else:
                resp = completion(**params)

            # Response Parsing
            content = resp.choices[0].message.content
            thinking = getattr(resp.choices[0].message, 'reasoning_content', None) or resp.get('_hidden_params', {}).get('thinking')

            result = content
            if output_pydantic or output_schema:
                try:
                    # JSON Extraction
                    json_match = re.search(r"```json\s*(.*?)\s*```", content, re.DOTALL)
                    json_str = json_match.group(1) if json_match else content
                    parsed = json.loads(json_str)
                    
                    if output_pydantic:
                        result = output_pydantic.model_validate(parsed)
                    else:
                        result = parsed
                except Exception as je:
                    LOGGER.error(f"JSON/Schema error on {model_name}: {je}")
                    raise SchemaValidationError(f"Model {model_name} failed schema.")

            # Success return
            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get('cost', 0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            LOGGER.warning(f"Attempt {attempt_idx} failed with {model_name}: {e}")
            if isinstance(e, SchemaValidationError):
                continue # Try next model
            if "authentication" in str(e).lower() and api_key:
                # Potential WSL/Copy-paste issue
                CONSOLE.print("[red]Auth Error:[/red] Re-check your key (WSL users: avoid carriage returns).")
                os.environ[key_name] = "" # Clear to force re-prompt
            if attempt_idx == len(candidates) - 1:
                raise RuntimeError(f"All model candidates failed. Last error: {e}")

    return {} # Should be unreachable due to RuntimeError