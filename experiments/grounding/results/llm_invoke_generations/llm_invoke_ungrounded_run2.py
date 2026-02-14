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
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as requested
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from pydantic import BaseModel

# --- Configuration & Globals ---
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger("pdd.llm_invoke")

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (timeout, 5xx, auth) that should trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required from Cloud."""
    pass

# --- Logging Setup ---

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    log_dir = Path.cwd() / "logs"
    log_dir.mkdir(exist_ok=True)
    handler = RotatingFileHandler(log_dir / "pdd.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logging.getLogger().addHandler(handler)

def set_verbose_logging(verbose: bool = True):
    level = logging.DEBUG if verbose else logging.INFO
    logger.setLevel(level)
    logging.getLogger("pdd").setLevel(level)

def _configure_loggers():
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        pdd_level = "WARNING"
        lite_level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"
        lite_level = "DEBUG"

    logging.basicConfig(level=pdd_level)
    logger.setLevel(pdd_level)
    logging.getLogger("litellm").setLevel(lite_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- Utility Functions ---

def _is_wsl() -> bool:
    return "microsoft-standard" in Path("/proc/version").read_text().lower() if Path("/proc/version").exists() else "WSL_DISTRO_NAME" in os.environ

def _sanitize_api_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        properties = schema.get("properties", {})
        if properties:
            schema["required"] = list(properties.keys())
        for prop in properties.values():
            _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    if "$defs" in schema:
        for definition in schema["$defs"].values():
            _ensure_all_properties_required(definition)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        properties = schema.get("properties", {})
        for prop in properties.values():
            _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)

def _repair_json(text: str) -> str:
    # Basic cleanup
    text = text.strip()
    if text.startswith("```json"):
        text = text.split("```json", 1)[1].split("```", 1)[0].strip()
    elif text.startswith("```"):
        text = text.split("```", 1)[1].split("```", 1)[0].strip()

    # Balanced extraction
    try:
        start = text.find("{")
        end = text.rfind("}")
        if start != -1 and end != -1:
            return text[start:end+1]
    except Exception:
        pass
    return text

def _repair_python_syntax(code: str) -> str:
    """Fix common truncation issues in Python code strings."""
    code = code.strip()
    # Unescape double-escaped newlines
    code = code.replace("\\n", "\n")
    # Fix trailing quotes
    if code.count('"""') % 2 != 0:
        code += '"""'
    return code

# --- Model Management ---

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    
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
                _MODEL_RATE_MAP[row['model']] = {
                    'input': row.get('input_cost_per_m', 0) / 1e6,
                    'output': row.get('output_cost_per_m', 0) / 1e6
                }
            return df
    raise FileNotFoundError("Could not locate llm_model.csv")

def _manage_api_key(provider: str, key_name: str) -> bool:
    current_val = os.getenv(key_name)
    if current_val:
        return True
    
    if os.getenv("PDD_FORCE"):
        return False

    console.print(f"[bold yellow]Missing API key for {provider} ({key_name})[/bold yellow]")
    new_key = _sanitize_api_key(input(f"Enter {key_name}: "))
    
    # Save to .env
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    
    # In-place replacement logic
    lines = []
    if env_path.exists():
        with open(env_path, "r") as f:
            lines = f.readlines()
    
    new_lines = [l for l in lines if not l.strip().startswith(f"{key_name}=") and not (l.strip().startswith("#") and f"{key_name}=" in l)]
    new_lines.append(f"{key_name}={new_key}\n")
    
    with open(env_path, "w") as f:
        f.writelines(new_lines)
    
    os.environ[key_name] = new_key
    console.print(f"[bold red]Security Warning:[/bold red] Key saved to {env_path}")
    return True

# --- Cloud Execution ---

def _pydantic_to_json_schema(model: Type[BaseModel]) -> Dict[str, Any]:
    schema = model.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["title"] = model.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    endpoint = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    token = os.getenv("PDD_CLOUD_TOKEN")
    
    try:
        resp = requests.post(
            endpoint,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if resp.status_code == 402:
            raise InsufficientCreditsError("Cloud account has insufficient credits.")
        if resp.status_code in [401, 403]:
            # Simple placeholder for clearing JWT cache
            raise CloudFallbackError("Cloud auth error, falling back.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud network error: {e}")

# --- Core Logic ---

def _get_reasoning_params(row: pd.Series, time_val: float) -> Dict[str, Any]:
    rtype = str(row.get('reasoning_type', 'none')).lower()
    max_tokens = int(row.get('max_reasoning_tokens', 0))
    
    if rtype == 'budget' and max_tokens > 0:
        budget = int(time_val * max_tokens)
        return {"thinking": {"type": "enabled", "budget_tokens": budget}}
    elif rtype == 'effort':
        if time_val < 0.33: effort = "low"
        elif time_val < 0.66: effort = "medium"
        else: effort = "high"
        # Logic for OpenAI o1/o3/gpt-5 models
        if "gpt-5" in row['model'] or "o1" in row['model']:
             return {"reasoning": {"effort": effort, "summary": "auto"}}
        return {"reasoning_effort": effort}
    return {}

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
    """Execute LLM call with fallback, cost tracking, and structured output support."""
    _configure_loggers()
    if verbose: set_verbose_logging(True)

    # 1. Cloud Pre-check
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is None:
        use_cloud = not force_local # Simplified CloudConfig.is_cloud_enabled check
        
    if use_cloud and not os.getenv("PDD_IN_CLOUD"):
        try:
            payload = {
                "prompt": prompt,
                "inputJson": input_json,
                "strength": strength,
                "temperature": temperature,
                "time": time,
                "verbose": verbose,
                "outputSchema": output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None),
                "useBatchMode": use_batch_mode,
                "language": language,
                "messages": messages
            }
            cloud_res = _llm_invoke_cloud(payload)
            # Pydantic validation of cloud result
            if output_pydantic and "result" in cloud_res:
                 cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            return cloud_res
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")

    # 2. Local Setup
    df = _load_model_csv()
    base_model = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter candidates
    available_df = df[df['api_key'].apply(lambda x: x == "EXISTING_KEY" or os.getenv(str(x)) is not None or not os.getenv("PDD_FORCE"))].copy()
    if available_df.empty:
        raise RuntimeError("No models available with valid API keys.")

    # Surrogate logic
    if not base_model or base_model not in available_df['model'].values:
        base_model = available_df.iloc[0]['model']
        
    base_row = available_df[available_df['model'] == base_model].iloc[0]
    
    # Sorting candidates for interpolation
    if strength < 0.5:
        # Interpolate by cost (base down to cheapest)
        available_df['metric'] = available_df['input_cost_per_m'] + available_df['output_cost_per_m']
        candidates = available_df[available_df['metric'] <= (base_row['input_cost_per_m'] + base_row['output_cost_per_m'])]
        candidates = candidates.sort_values('metric', ascending=False)
    elif strength > 0.5:
        # Interpolate by ELO (base up to highest)
        candidates = available_df[available_df['coding_arena_elo'] >= base_row['coding_arena_elo']]
        candidates = candidates.sort_values('coding_arena_elo', ascending=True)
    else:
        # Strength 0.5: Base then fallback to higher ELO
        candidates = pd.concat([
            available_df[available_df['model'] == base_model],
            available_df[available_df['coding_arena_elo'] > base_row['coding_arena_elo']].sort_values('coding_arena_elo')
        ])

    # 3. Cache Setup
    if not os.getenv("LITELLM_CACHE_DISABLE"):
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(type="s3", s3_bucket_name=os.getenv("GCS_BUCKET_NAME"), 
                                         s3_api_version="v4", s3_region_name="auto",
                                         s3_endpoint_url=f"https://storage.googleapis.com")
        else:
            litellm.cache = litellm.Cache(type="disk", cache_filename=str(get_default_resolver().resolve_project_root() / "litellm_cache.sqlite"))

    # 4. Iterative Invocation
    last_error = None
    for _, row in candidates.iterrows():
        model_id = row['model']
        provider = row['provider']
        key_env = row['api_key']
        
        # Interactive key check
        if key_env != "EXISTING_KEY" and not _manage_api_key(provider, key_env):
            continue

        try:
            # Prepare args
            call_params = {
                "model": model_id,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT,
            }
            
            # Reasoning & Anthropic specific
            reasoning = _get_reasoning_params(row, time)
            if "thinking" in reasoning and "anthropic" in provider.lower():
                call_params["temperature"] = 1.0 # Force 1.0 for Anthropic thinking
            call_params.update(reasoning)

            # Structured Output handling
            final_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
            if final_schema and row.get('structured_output'):
                if "gpt-5" in model_id:
                    call_params["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": final_schema, "strict": True}}
                else:
                    call_params["response_format"] = {"type": "json_object"}
                    # Inject schema into prompt if not native support
                    if "groq" in provider.lower():
                        prompt = (prompt or "") + f"\nOutput MUST follow this JSON schema: {json.dumps(final_schema)}"

            # Vertex Config
            if "vertex" in provider.lower() or "google" in provider.lower():
                call_params["vertex_project"] = os.getenv("VERTEX_PROJECT")
                call_params["vertex_location"] = row.get('location') or os.getenv("VERTEX_LOCATION", "us-central1")
                call_params["vertex_credentials"] = os.getenv("VERTEX_CREDENTIALS")

            # LM Studio Base URL
            if "lm_studio" in provider.lower():
                call_params["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                call_params["api_key"] = "lm-studio"
                if final_schema:
                    call_params["extra_body"] = {"response_format": {"type": "json_object", "schema": final_schema}}

            # Message construction
            if not messages:
                user_content = prompt.replace("{{input}}", json.dumps(input_json)) if prompt else json.dumps(input_json)
                msgs = [{"role": "user", "content": user_content}]
            else:
                msgs = messages

            # Call API
            if use_batch_mode:
                resp = batch_completion(messages=msgs, **call_params)
            elif "gpt-5" in model_id:
                # Mocking Responses API usage
                resp = litellm.completion(messages=msgs, **call_params)
            else:
                resp = litellm.completion(messages=msgs, **call_params)

            # Post-processing
            content = resp.choices[0].message.content
            if not content:
                raise SchemaValidationError("Empty response from LLM")
            
            # Structured Validation
            result = content
            if output_pydantic or output_schema:
                try:
                    cleaned_json = _repair_json(content)
                    parsed = json.loads(cleaned_json)
                    if output_pydantic:
                        result = output_pydantic.model_validate(parsed)
                    else:
                        result = parsed
                except Exception as e:
                    raise SchemaValidationError(f"JSON/Pydantic validation failed: {e}")

            # Python-specific validation
            if (language == "python" or language is None) and isinstance(result, str):
                try:
                    _repair_python_syntax(result)
                except Exception as e:
                    logger.warning(f"Python syntax repair failed: {e}")

            # Cost Calculation
            cost = completion_cost(resp) or 0
            if cost == 0:
                 # Fallback to CSV rates
                 usage = resp.get('usage', {})
                 cost = (usage.get('prompt_tokens', 0) * _MODEL_RATE_MAP.get(model_id, {}).get('input', 0) +
                         usage.get('completion_tokens', 0) * _MODEL_RATE_MAP.get(model_id, {}).get('output', 0))

            return {
                "result": result,
                "cost": cost,
                "model_name": model_id,
                "thinking_output": getattr(resp.choices[0].message, "reasoning_content", None) or resp.get("_hidden_params", {}).get("thinking")
            }

        except Exception as e:
            last_error = e
            logger.error(f"Attempt with {model_id} failed: {e}")
            if "authentication" in str(e).lower() and _is_wsl():
                 console.print("[bold yellow]WSL detected: Check for carriage returns (\\r) in your API keys.[/bold yellow]")
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_error}")

if __name__ == "__main__":
    # Test call
    try:
        res = llm_invoke(prompt="Say hello in {{input}}", input_json={"lang": "Python"}, strength=0.5)
        console.print(res)
    except Exception as e:
        console.print(f"Test failed: {e}")