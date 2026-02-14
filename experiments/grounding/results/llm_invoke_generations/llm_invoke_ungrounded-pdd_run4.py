from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from dataclasses import dataclass
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key

# Use Pydantic v2
from pydantic import BaseModel
from rich.console import Console

if TYPE_CHECKING:
    from pydantic import ConfigDict

# Package-level constants (simulating .pdd internal structure)
try:
    from . import (
        DEFAULT_STRENGTH,
        DEFAULT_TIME,
        EXTRACTION_STRENGTH,
    )
except ImportError:
    # Fallbacks if relative import fails outside of package context
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = 0.25
    EXTRACTION_STRENGTH = 0.5

# Configuration & Globals
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
console = Console()

# --- Exception Definitions ---

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
    """402 Payment Required."""
    pass

# --- Path Resolution & Environment ---

class PathResolver:
    @staticmethod
    def resolve_project_root() -> Path:
        """Finds project root using markers or falls back to CWD."""
        cwd = Path.cwd()
        markers = [".git", "pyproject.toml", "data", ".env"]
        
        # Search upward
        for parent in [cwd, *cwd.parents]:
            if any((parent / marker).exists() for marker in markers):
                return parent
        return cwd

    @staticmethod
    def resolve_model_csv() -> Path:
        """Priority: ~/.pdd, <root>/.pdd, <cwd>/.pdd, package data."""
        root = PathResolver.resolve_project_root()
        paths = [
            Path.home() / ".pdd" / "llm_model.csv",
            root / ".pdd" / "llm_model.csv",
            Path.cwd() / ".pdd" / "llm_model.csv",
            Path(__file__).parent / "data" / "llm_model.csv"
        ]
        for p in paths:
            if p.exists():
                return p
        raise FileNotFoundError("llm_model.csv not found.")

def _init_env():
    root = PathResolver.resolve_project_root()
    env_path = root / ".env"
    load_dotenv(dotenv_path=env_path)
    
    # LiteLLM Basic Config
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    litellm.telemetry = False

# --- Logging Configuration ---

def setup_file_logging():
    log_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        log_level = "DEBUG"
    if os.getenv("PDD_ENVIRONMENT") == "production" and log_level == "DEBUG":
        log_level = "INFO"

    logger = logging.getLogger("pdd.llm_invoke")
    logger.setLevel(log_level)
    
    root = PathResolver.resolve_project_root()
    log_dir = root / "logs"
    log_dir.mkdir(exist_ok=True)
    
    handler = RotatingFileHandler(log_dir / "llm_invoke.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

    lt_logger = logging.getLogger("litellm")
    lt_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    lt_logger.setLevel(lt_level)

# --- LiteLLM Callbacks & Cost Tracking ---

def _completion_success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        model = kwargs.get("model", "unknown")
        usage = getattr(response_obj, "usage", None)
        cost = litellm.completion_cost(completion_response=response_obj) or 0.0
        
        _LAST_CALLBACK_DATA = {
            "model": model,
            "usage": usage,
            "cost": cost,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception:
        pass

litellm.success_callback = [_completion_success_callback]

# --- Helper Functions for Model Selection & API Keys ---

def _get_api_key_interactively(key_name: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
    
    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name}")
    key_val = input(f"Please enter value for {key_name}: ").strip()
    
    # WSL Sanitization
    key_val = key_val.replace("\r", "").replace("\n", "")
    
    if key_val:
        os.environ[key_name] = key_val
        root = PathResolver.resolve_project_root()
        env_path = root / ".env"
        # Update .env file
        set_key(str(env_path), key_name, key_val)
        console.print(f"[bold green]Key saved to {env_path}[/bold green]")
        return key_val
    return ""

def _select_models(strength: float, csv_path: Path) -> List[Dict[str, Any]]:
    df = pd.read_csv(csv_path)
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter for models with available keys or keys we can prompt for
    available_models = []
    for _, row in df.iterrows():
        key_name = str(row['api_key'])
        if key_name == "EXISTING_KEY" or key_name == "nan" or not key_name:
             available_models.append(row.to_dict())
             continue
        
        val = os.getenv(key_name)
        if val:
            available_models.append(row.to_dict())
        elif not os.getenv("PDD_FORCE"):
            # Potential candidate if user provides key
            available_models.append(row.to_dict())

    if not available_models:
        return []

    # Sort logic
    if strength == 0.5:
        # Find base or first available
        target = next((m for m in available_models if m['model'] == base_model_name), available_models[0])
        others = [m for m in available_models if m != target]
        others.sort(key=lambda x: x.get('coding_arena_elo', 0), reverse=True)
        return [target] + others
    
    if strength < 0.5:
        # Interpolate by cost (cheaper is better)
        available_models.sort(key=lambda x: (x.get('input', 0) + x.get('output', 0)))
    else:
        # Interpolate by ELO
        available_models.sort(key=lambda x: x.get('coding_arena_elo', 0), reverse=True)
        
    return available_models

# --- JSON & Python Parsing Helpers ---

def _repair_python_syntax(code: str) -> str:
    # Basic repairs for common LLM truncation/escaping issues
    code = code.strip()
    if code.startswith("```python"):
        code = code.split("```python", 1)[1]
    if "```" in code:
        code = code.split("```", 1)[0]
    return code.strip()

def _smart_unescape_code(text: str) -> str:
    """Unescapes double backslashes for newlines in code strings."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _extract_json(text: str) -> Any:
    """Robust JSON extraction from text."""
    # Try fenced code blocks
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match:
        try: return json.loads(match.group(1))
        except: pass
    
    # Try finding balanced braces
    try:
        start = text.find('{')
        end = text.rfind('}')
        if start != -1 and end != -1:
            return json.loads(text[start:end+1])
    except:
        pass
        
    return text # Fallback to raw

# --- Cloud Execution ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            if isinstance(prop, dict):
                _ensure_all_properties_required(prop)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if "type" in schema and schema["type"] == "object":
        schema["additionalProperties"] = False
    for k, v in schema.items():
        if isinstance(v, dict):
            _add_additional_properties_false(v)
        elif isinstance(v, list):
            for item in v:
                if isinstance(item, dict):
                    _add_additional_properties_false(item)

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
    try:
        response = requests.post(url, json=payload, timeout=300)
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if response.status_code in [401, 403]:
            # Possible token expiry
            raise CloudFallbackError(f"Cloud Auth Error: {response.status_code}")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

# --- Main Invocation Function ---

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
    """Expert LLM invocation with selection, reasoning, and validation."""
    
    _init_env()
    setup_file_logging()
    logger = logging.getLogger("pdd.llm_invoke")

    # Cloud logic
    if use_cloud is None:
        use_cloud = (os.getenv("PDD_FORCE_LOCAL") != "1")
    
    if use_cloud:
        try:
            cloud_schema = output_schema
            if output_pydantic:
                cloud_schema = _pydantic_to_json_schema(output_pydantic)
            
            payload = {
                "prompt": prompt,
                "inputJson": input_json,
                "messages": messages,
                "strength": strength,
                "temperature": temperature,
                "time": time,
                "verbose": verbose,
                "outputSchema": cloud_schema,
                "useBatchMode": use_batch_mode,
                "language": language
            }
            cloud_res = _llm_invoke_cloud(payload)
            
            # Pydantic validation of cloud result
            if output_pydantic and "result" in cloud_res:
                if isinstance(cloud_res["result"], dict):
                    cloud_res["result"] = output_pydantic.model_validate(cloud_res["result"])
            
            return {
                "result": cloud_res.get("result"),
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
            logger.warning(f"Cloud fallback: {e}")

    # Local execution
    csv_path = PathResolver.resolve_model_csv()
    candidates = _select_models(strength, csv_path)
    
    if not candidates:
        raise RuntimeError("No models found in CSV.")

    for model_row in candidates:
        model_name = model_row['model']
        provider = model_row['provider']
        key_name = model_row['api_key']
        
        # API Key Handling
        api_key = os.getenv(key_name)
        newly_acquired = False
        if not api_key and key_name not in ["nan", "", "EXISTING_KEY"]:
            api_key = _get_api_key_interactively(key_name)
            newly_acquired = True
            if not api_key: continue

        # Format Messages
        if not messages:
            content = prompt.format(**input_json) if input_json and prompt else (prompt or "")
            call_messages = [{"role": "user", "content": content}]
        else:
            call_messages = messages

        # Reasoning Logic
        completion_kwargs: Dict[str, Any] = {
            "model": model_name,
            "messages": call_messages,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        r_type = model_row.get('reasoning_type', 'none')
        max_r_tokens = int(model_row.get('max_reasoning_tokens', 0))
        
        if r_type == 'budget' and max_r_tokens > 0:
            budget = int(time * max_r_tokens)
            completion_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
            completion_kwargs["temperature"] = 1.0 # Anthropic requirement
        elif r_type == 'effort':
            effort = "low" if time < 0.3 else ("medium" if time < 0.7 else "high")
            if "gpt-5" in model_name: # Hypothetical Responses API
                completion_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                completion_kwargs["reasoning_effort"] = effort

        # Structured Output Setup
        if output_pydantic or output_schema:
            if model_row.get('structured_output'):
                schema = output_schema or output_pydantic.model_json_schema()
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)
                completion_kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "output", "schema": schema, "strict": True}
                }
            elif "groq" in provider.lower():
                completion_kwargs["response_format"] = {"type": "json_object"}
                call_messages[0]["content"] += "\nReturn valid JSON matching the required schema."

        try:
            # Execution
            if "gpt-5" in model_name and r_type == 'effort':
                # Fake Responses API call as requested
                response = litellm.completion(**completion_kwargs) 
            elif use_batch_mode:
                response = litellm.batch_completion(**completion_kwargs)
            else:
                response = litellm.completion(**completion_kwargs)

            # Extract result
            result_raw = response.choices[0].message.content
            thinking = response.choices[0].message.get('reasoning_content') or \
                       response.get('_hidden_params', {}).get('thinking')

            # Validation & Parsing
            final_result = result_raw
            if output_pydantic or output_schema:
                parsed_json = _extract_json(result_raw)
                if output_pydantic:
                    final_result = output_pydantic.model_validate(parsed_json)
                else:
                    final_result = parsed_json

            # Cleanup
            cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
            if cost == 0.0:
                 # Fallback to CSV rates
                 in_tokens = response.usage.prompt_tokens
                 out_tokens = response.usage.completion_tokens
                 cost = (in_tokens * model_row['input'] + out_tokens * model_row['output']) / 1_000_000

            return {
                "result": final_result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.error(f"Error invoking {model_name}: {e}")
            if newly_acquired and "auth" in str(e).lower():
                 # Retry key acquisition once
                 os.environ.pop(key_name, None)
                 return llm_invoke(prompt, input_json, strength, temperature, verbose, 
                                   output_pydantic, output_schema, time, use_batch_mode, 
                                   messages, language, use_cloud)
            continue # Try next candidate

    raise RuntimeError("All LLM candidates exhausted or failed.")

if __name__ == "__main__":
    # Quick test
    res = llm_invoke(prompt="Say hello world", strength=0.5, use_cloud=False)
    console.print(res)