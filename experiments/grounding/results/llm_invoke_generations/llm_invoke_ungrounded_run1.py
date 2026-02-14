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
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Use relative imports as per package requirements
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger("pdd.llm_invoke")

# --- Exceptions ---
class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic/Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable error (auth/timeout) that triggers local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable error in cloud execution."""
    pass

class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required."""
    pass

# --- Setup ---
def setup_logging() -> None:
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    else:
        lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = "DEBUG"
        lite_level = "DEBUG"

    logging.basicConfig(level=log_level)
    logging.getLogger("pdd.llm_invoke").setLevel(log_level)
    logging.getLogger("litellm").setLevel(lite_level)

    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # Cache Configuration
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(
                type="s3",
                s3_bucket_name=os.getenv("GCS_BUCKET_NAME"),
                s3_region_name="auto",
                s3_api_base="https://storage.googleapis.com",
                s3_access_key_id=os.getenv("GCS_HMAC_ACCESS_KEY_ID"),
                s3_secret_access_key=os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
            )
        else:
            resolver = get_default_resolver()
            project_root = resolver.resolve_project_root()
            cache_path = project_root / "litellm_cache.sqlite"
            litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(cache_path))

def success_callback(kwargs: Dict, response_obj: Any) -> None:
    global _LAST_CALLBACK_DATA
    try:
        cost = completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "usage": getattr(response_obj, "usage", {}),
            "model": kwargs.get("model")
        }
    except Exception:
        pass

litellm.success_callback = [success_callback]

# --- Helpers ---
def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    paths_to_check = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    
    for p in paths_to_check:
        if p.exists():
            return pd.read_csv(p)
    
    # Fallback to packaged data
    try:
        data_path = resolver.resolve_data_file("data/llm_model.csv")
        return pd.read_csv(data_path)
    except Exception:
        return pd.DataFrame()

def _ensure_api_key(provider: str, key_name: str) -> bool:
    if not key_name or key_name == "EXISTING_KEY" or provider == "lm_studio":
        return True
    
    api_key = os.getenv(key_name)
    if api_key:
        return True
    
    if os.getenv("PDD_FORCE"):
        return False

    console.print(f"[bold yellow]Missing API Key for {provider} ({key_name})[/bold yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    if not new_key:
        return False
    
    # WSL Sanitization
    new_key = new_key.replace("\r", "").replace("\n", "")
    
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    set_key(str(env_path), key_name, new_key)
    os.environ[key_name] = new_key
    
    console.print(f"[bold green]Key saved to {env_path}. Protect this file![/bold green]")
    return True

def _repair_json(text: str) -> str:
    # Basic fence stripping
    text = text.strip()
    if text.startswith("```json"):
        text = text.split("```json", 1)[1].split("```", 1)[0]
    elif text.startswith("```"):
        text = text.split("```", 1)[1].split("```", 1)[0]
    
    text = text.strip()
    # Handle truncation by closing braces
    open_braces = text.count('{') - text.count('}')
    if open_braces > 0:
        text += '}' * open_braces
    return text

def _llm_invoke_cloud(payload: Dict) -> Dict:
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
            raise InsufficientCreditsError("PDD Cloud: Insufficient credits")
        if response.status_code in [401, 403]:
            raise CloudFallbackError("Cloud Auth Error")
        
        response.raise_for_status()
        return response.json()
    except Exception as e:
        if isinstance(e, (CloudFallbackError, InsufficientCreditsError)):
            raise
        raise CloudInvocationError(f"Cloud request failed: {str(e)}")

# --- Main Function ---
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
    
    load_dotenv(get_default_resolver().resolve_project_root() / ".env")
    setup_logging()

    # Cloud Check
    if use_cloud is None:
        use_cloud = (os.getenv("PDD_FORCE_LOCAL") != "1")
    
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
                "outputSchema": output_schema or (output_pydantic.model_json_schema() if output_pydantic else None),
                "useBatchMode": use_batch_mode,
                "language": language
            }
            res = _llm_invoke_cloud(payload)
            if output_pydantic and "result" in res:
                # Local validation of cloud result
                res["result"] = output_pydantic.model_validate(res["result"])
            return res
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud fallback: {e}[/yellow]")
        except InsufficientCreditsError:
            raise
        except Exception as e:
            console.print(f"[red]Cloud Error: {e}. Falling back to local.[/red]")

    # --- Local Selection Logic ---
    df = _load_model_csv()
    if df.empty:
        raise RuntimeError("No model CSV found")

    # Filter by API key and surrogate logic
    base_model_id = os.getenv("PDD_MODEL_DEFAULT")
    available_models = df[df.apply(lambda r: _ensure_api_key(r['provider'], r['api_key']), axis=1)]
    
    if available_models.empty:
        raise RuntimeError("No models available with valid API keys")

    # Interpolation Logic
    sorted_models = available_models.sort_values(by="coding_arena_elo")
    if strength == 0.5 and base_model_id:
        target_model = available_models[available_models['model'] == base_model_id].iloc[0]
    elif strength < 0.5:
        # Simplification: Choose cheapest subset
        target_model = sorted_models.iloc[0]
    else:
        target_model = sorted_models.iloc[-1]

    # Reasoning Config
    model_name = target_model['model']
    provider = target_model['provider']
    r_type = target_model.get('reasoning_type', 'none')
    max_r = int(target_model.get('max_reasoning_tokens', 0))
    
    completion_kwargs: Dict[str, Any] = {
        "model": f"{provider}/{model_name}" if "/" not in model_name else model_name,
        "temperature": temperature,
        "num_retries": 2,
        "timeout": LLM_CALL_TIMEOUT,
    }

    if r_type == 'budget':
        completion_kwargs['thinking'] = {"type": "enabled", "budget_tokens": int(time * max_r)}
        completion_kwargs['temperature'] = 1.0 # Anthropic requirement
    elif r_type == 'effort':
        effort = "low" if time < 0.33 else "medium" if time < 0.66 else "high"
        completion_kwargs['reasoning_effort'] = effort

    # Message Builder
    if not messages:
        # Simple template filling (simulated)
        content = prompt or ""
        if input_json:
            content = f"{content}\n\nInput: {json.dumps(input_json)}"
        msgs = [{"role": "user", "content": content}]
    else:
        msgs = messages

    # Execution
    try:
        if use_batch_mode:
            response = batch_completion(messages=msgs, **completion_kwargs)
            # Simplified result extraction
            result = [r.choices[0].message.content for r in response]
        else:
            response = completion(messages=msgs, **completion_kwargs)
            result = response.choices[0].message.content
            
        thinking = getattr(response.choices[0].message, "reasoning_content", None)

        # Structured Output Handling
        if output_pydantic and result:
            parsed = json.loads(_repair_json(result))
            result = output_pydantic.model_validate(parsed)

        return {
            "result": result,
            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
            "model_name": model_name,
            "thinking_output": thinking
        }

    except Exception as e:
        logger.error(f"LLM Call Failed: {e}")
        raise RuntimeError(f"Invocation failed: {str(e)}")

if __name__ == "__main__":
    # Quick test if run directly
    try:
        res = llm_invoke(prompt="Say hello in {{language}}", input_json={"language": "Python"}, strength=0)
        console.print(res)
    except Exception as e:
        console.print(f"[red]{e}[/red]")
