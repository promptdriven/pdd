from __future__ import annotations

import json
import logging
import os
import re
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

# Internal relative imports as per requirements
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
PDD_ENV = os.getenv("PDD_ENVIRONMENT", "production")
CONSOLE = Console()

# --- Logging Setup ---
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    log_dir = Path.home() / ".pdd" / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "llm_invoke.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(verbose: bool = False):
    level = logging.DEBUG if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1" else logging.INFO
    logger.setLevel(level)
    
    lite_level_env = os.getenv("LITELLM_LOG_LEVEL")
    if lite_level_env:
        litellm_logger.setLevel(lite_level_env)
    else:
        litellm_logger.setLevel(logging.WARNING if PDD_ENV == "production" else logging.INFO)

# --- State Management ---
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    usage = getattr(response_obj, "usage", None)
    _LAST_CALLBACK_DATA = {
        "usage": usage,
        "response": response_obj,
        "model": kwargs.get("model")
    }

litellm.success_callback = [_success_callback]
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() == "true"

# --- Exceptions ---
class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation or JSON parsing."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud errors triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Helper Functions ---

def _get_project_root() -> Path:
    resolver = get_default_resolver()
    try:
        return Path(resolver.resolve_project_root())
    except Exception:
        return Path.cwd()

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    project_root = _get_project_root()
    
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    
    try:
        packaged_csv = Path(resolver.resolve_data_file("data/llm_model.csv"))
        paths.append(packaged_csv)
    except Exception:
        pass

    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": float(row.get("input_cost_per_m", 0)),
                    "output": float(row.get("output_cost_per_m", 0))
                }
            return df
    return pd.DataFrame()

def _ensure_api_key(provider: str, key_name: str) -> Optional[str]:
    key = os.getenv(key_name)
    if key and key != "EXISTING_KEY":
        return key.strip()
    
    if os.getenv("PDD_FORCE"):
        return None

    CONSOLE.print(f"[yellow]Missing API Key for {provider} ({key_name}).[/yellow]")
    user_key = input(f"Enter {key_name}: ").strip()
    if not user_key:
        return None

    # Save to .env
    project_root = _get_project_root()
    env_path = project_root / ".env"
    set_key(str(env_path), key_name, user_key)
    os.environ[key_name] = user_key
    
    CONSOLE.print(f"[bold green]Key saved to {env_path}.[/bold green] [red](Security Warning: Do not commit .env)[/red]")
    return user_key

def _repair_json(text: str) -> str:
    # Basic fence cleaning
    if "```json" in text:
        text = text.split("```json")[-1].split("```")[0]
    elif "```" in text:
        text = text.split("```")[-1].split("```")[0]
    
    text = text.strip()
    # Try to find balanced braces if extra prose exists
    start = text.find('{')
    end = text.rfind('}')
    if start != -1 and end != -1:
        text = text[start:end+1]
    
    return text

def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines while preserving literals."""
    return text.replace("\\n", "\n")

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    return schema

def _ensure_all_properties_required(schema: Dict[str, Any]):
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])

def _add_additional_properties_false(schema: Dict[str, Any]):
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values():
                _add_additional_properties_false(prop)

# --- Core Logic ---

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
    """Execute LLM call with LiteLLM, handling cloud/local, retries, and formatting."""
    set_verbose_logging(verbose)
    load_dotenv(dotenv_path=_get_project_root() / ".env")

    # Cloud Execution Logic
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt, input_json, strength, temperature, time, verbose,
                output_pydantic, output_schema, use_batch_mode, messages, language
            )
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # Model Selection Logic
    df = _load_model_csv()
    if df.empty:
        raise RuntimeError("llm_model.csv not found.")

    available_models = df[df["api_key"].apply(lambda k: os.getenv(str(k)) is not None or k == "EXISTING_KEY")]
    if available_models.empty:
        # Filter for models where we can potentially prompt for a key
        available_models = df.copy()

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row = df[df["model"] == base_model_name].iloc[0] if base_model_name in df["model"].values else available_models.iloc[0]

    # Interpolation Logic
    if strength < 0.5:
        candidates = available_models[available_models["input_cost_per_m"] <= base_row["input_cost_per_m"]].sort_values("input_cost_per_m", ascending=False)
    elif strength > 0.5:
        candidates = available_models[available_models["coding_arena_elo"] >= base_row["coding_arena_elo"]].sort_values("coding_arena_elo", ascending=True)
    else:
        candidates = pd.DataFrame([base_row])

    # Try candidates until success
    for _, model_row in candidates.iterrows():
        model_name = model_row["model"]
        provider = model_row["provider"]
        api_key_env = model_row["api_key"]
        
        api_key = _ensure_api_key(provider, api_key_env)
        if not api_key: continue

        try:
            return _execute_local_call(
                model_row, prompt, input_json, strength, temperature, time,
                output_pydantic, output_schema, use_batch_mode, messages, language
            )
        except Exception as e:
            logger.warning(f"Model {model_name} failed: {e}")
            continue

    raise RuntimeError("All LLM candidates exhausted.")

def _execute_local_call(row, prompt, input_json, strength, temperature, time, 
                        output_pydantic, output_schema, use_batch_mode, messages, language):
    model_name = row["model"]
    
    # Message Construction
    final_messages = messages
    if not final_messages:
        content = prompt if prompt else ""
        if input_json:
            content = content.replace("{{input}}", json.dumps(input_json))
        final_messages = [{"role": "user", "content": content}]

    # Reasoning Configuration
    reasoning_type = row.get("reasoning_type", "none")
    max_reasoning = row.get("max_reasoning_tokens", 0)
    kwargs = {
        "model": model_name,
        "messages": final_messages,
        "timeout": LLM_CALL_TIMEOUT,
        "num_retries": 2,
    }

    if "gpt-5" in model_name: # Hypothetical future model using responses API
        kwargs["reasoning"] = {"effort": "high" if time > 0.7 else "medium" if time > 0.3 else "low"}
    elif reasoning_type == "budget":
        kwargs["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_reasoning)}
        kwargs["temperature"] = 1.0 # Anthropic requirement
    elif reasoning_type == "effort":
        kwargs["reasoning_effort"] = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
        kwargs["temperature"] = temperature
    else:
        kwargs["temperature"] = temperature

    # Structured Output Support
    target_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
    if target_schema:
        if row.get("structured_output") == 1:
            kwargs["response_format"] = {"type": "json_schema", "json_schema": {"name": "result", "schema": target_schema, "strict": True}}
        elif "groq" in model_name.lower():
            kwargs["response_format"] = {"type": "json_object"}
            final_messages[0]["content"] += f"\nReturn valid JSON matching: {json.dumps(target_schema)}"

    # Invoke
    if use_batch_mode:
        response = batch_completion(**kwargs)
    else:
        response = completion(**kwargs)

    # Process Response
    result_text = response.choices[0].message.content or ""
    thinking = response.choices[0].message.get("reasoning_content") or response.get("_hidden_params", {}).get("thinking")
    
    cost = completion_cost(response)
    if cost == 0 and model_name in _MODEL_RATE_MAP:
        usage = response.usage
        rates = _MODEL_RATE_MAP[model_name]
        cost = (usage.prompt_tokens * rates["input"] + usage.completion_tokens * rates["output"]) / 1_000_000

    # Validation & Parsing
    parsed_result = result_text
    if target_schema:
        try:
            parsed_result = json.loads(_repair_json(result_text))
            if output_pydantic:
                parsed_result = output_pydantic.model_validate(parsed_result)
        except Exception as e:
            raise SchemaValidationError(f"JSON/Schema validation failed: {e}")

    return {
        "result": parsed_result,
        "cost": cost,
        "model_name": model_name,
        "thinking_output": thinking
    }

def _llm_invoke_cloud(prompt, input_json, strength, temperature, time, verbose, 
                      output_pydantic, output_schema, use_batch_mode, messages, language) -> Dict[str, Any]:
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {os.getenv('PDD_CLOUD_TOKEN')}"}
    
    schema = output_schema
    if output_pydantic:
        schema = _pydantic_to_json_schema(output_pydantic)

    payload = {
        "prompt": prompt,
        "inputJson": input_json,
        "messages": messages,
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "outputSchema": schema,
        "useBatchMode": use_batch_mode,
        "language": language
    }

    try:
        resp = requests.post(url, json=payload, headers=headers, timeout=300)
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code != 200:
            raise CloudFallbackError(f"Cloud API returned {resp.status_code}: {resp.text}")
        
        data = resp.json()
        result = data["result"]
        
        if output_pydantic:
            if isinstance(result, str):
                result = json.loads(result)
            result = output_pydantic.model_validate(result)

        return {
            "result": result,
            "cost": data.get("totalCost", 0),
            "model_name": data.get("modelName", "cloud"),
            "thinking_output": data.get("thinkingOutput")
        }
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(str(e))

if __name__ == "__main__":
    # Self-test logic
    setup_file_logging()
    try:
        res = llm_invoke(prompt="Say hello in {{input}}", input_json="Python", strength=0.5)
        CONSOLE.print(res)
    except Exception as e:
        logger.exception("Failed llm_invoke test")