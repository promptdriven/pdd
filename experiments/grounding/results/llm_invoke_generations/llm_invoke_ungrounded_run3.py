from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union

import litellm
import pandas as pd
import requests
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as per requirements
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

# Constants
LLM_CALL_TIMEOUT = 120
PDD_LOG_NAME = "pdd.llm_invoke"

# Global state for callback tracking
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger(PDD_LOG_NAME)

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic or Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required."""
    pass

def setup_file_logging():
    """Configures rotating file handlers if needed."""
    from logging.handlers import RotatingFileHandler
    log_dir = Path.home() / ".pdd" / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "llm_invoke.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(enable: bool = True):
    """Toggles DEBUG level for PDD and LiteLLM."""
    level = logging.DEBUG if enable else logging.INFO
    logger.setLevel(level)
    if enable:
        logging.getLogger("litellm").setLevel(logging.DEBUG)

def _is_wsl() -> bool:
    """Detects if running inside Windows Subsystem for Linux."""
    if "WSL_DISTRO_NAME" in os.environ:
        return True
    try:
        with open("/proc/version", "r") as f:
            return "microsoft" in f.read().lower()
    except FileNotFoundError:
        return False

def _success_callback(kwargs, response_obj, start_time, end_time):
    """LiteLLM success callback to capture usage and cost."""
    global _LAST_CALLBACK_DATA
    try:
        cost = completion_cost(completion_response=response_obj)
        usage = response_obj.get("usage", {})
        _LAST_CALLBACK_DATA = {
            "cost": cost or 0.0,
            "usage": usage,
            "model": response_obj.get("model", ""),
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.warning(f"Callback error: {e}")

litellm.success_callback = [_success_callback]

def _load_model_csv() -> pd.DataFrame:
    """Resolves and loads the llm_model.csv file in priority order."""
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
            # Build global rate map for fallback cost calc
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row['model']] = {
                    "input": row.get('input_cost_per_m', 0.0) / 1_000_000,
                    "output": row.get('output_cost_per_m', 0.0) / 1_000_000
                }
            return df
    return pd.DataFrame()

def _manage_api_key(key_name: str, provider: str) -> bool:
    """Interactively fetches and saves missing API keys."""
    val = os.getenv(key_name)
    if val and val != "EXISTING_KEY":
        return True
    
    if os.getenv("PDD_FORCE"):
        return False

    console.print(f"[bold yellow]Missing API key for {provider} ({key_name}).[/bold yellow]")
    user_key = input(f"Enter {key_name}: ").strip()
    if not user_key:
        return False

    # Sanitize for WSL
    user_key = user_key.replace('\r', '').replace('\n', '')
    
    os.environ[key_name] = user_key
    
    resolver = get_default_resolver()
    env_path = resolver.resolve_project_root() / ".env"
    
    # Save to .env
    set_key(str(env_path), key_name, user_key)
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")
    logger.warning(f"Security: API Key {key_name} saved to local .env file.")
    
    # Mark as newly acquired for retry logic
    os.environ[f"{key_name}_NEW"] = "1"
    return True

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively ensures all properties in a JSON schema are marked as required."""
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for p in props.values():
            _ensure_all_properties_required(p)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    # Handle combinators
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    """Enforces strict=True style schemas by adding additionalProperties: false."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for p in props.values():
            _add_additional_properties_false(p)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _add_additional_properties_false(d)

def _repair_json(content: str) -> str:
    """Attempts to repair truncated or malformed JSON responses."""
    content = content.strip()
    # Try to find code block
    json_match = re.search(r"```json\s*(.*?)\s*```", content, re.DOTALL)
    if json_match:
        content = json_match.group(1)
    
    # Simple brace balance check
    open_b = content.count('{')
    close_b = content.count('}')
    if open_b > close_b:
        content += '}' * (open_b - close_b)
    
    return content

def _repair_python_syntax(code: str) -> str:
    """Basic repair for common LLM Python syntax errors."""
    code = code.strip()
    # Remove trailing quotes if it looks like a truncation error
    if (code.count('"""') % 2 != 0):
        code += '"""'
    return code

def _smart_unescape_code(content: str) -> str:
    """Unescapes double-escaped newlines while preserving literals."""
    return content.replace("\\n", "\n")

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Any,
    messages: Optional[List[Dict]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str]
) -> Dict[str, Any]:
    """Transports invocation to the PDD Cloud endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN") or os.getenv("FIREBASE_ID_TOKEN")
    if not token:
        raise CloudFallbackError("No cloud token available")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
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
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in [401, 403]:
            # Trigger token refresh logic if we had one
            raise CloudFallbackError(f"Cloud Auth Error: {resp.text}")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud connection failed: {e}")

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
    Main entry point for LLM invocation with LiteLLM, reasoning support, 
    and hybrid cloud/local execution.
    """
    # 1. Startup & Env
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    load_dotenv(root / ".env")
    
    # Configure Logging
    setup_file_logging()
    if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1":
        set_verbose_logging(True)
    
    env_log_level = os.getenv("PDD_LOG_LEVEL", "INFO")
    logger.setLevel(env_log_level)
    
    # LiteLLM Globals
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # 2. Cloud Execution Path
    if use_cloud is None:
        use_cloud = (os.getenv("PDD_FORCE_LOCAL") != "1" and os.getenv("PDD_CLOUD_ENABLED") == "1")

    if use_cloud:
        try:
            # Pydantic -> Schema conversion
            effective_schema = output_schema
            if output_pydantic:
                effective_schema = output_pydantic.model_json_schema()
                _ensure_all_properties_required(effective_schema)

            cloud_res = _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, 
                time, verbose, effective_schema, use_batch_mode, language
            )
            
            # Post-validate cloud result if pydantic provided
            if output_pydantic and "result" in cloud_res:
                try:
                    res_obj = cloud_res["result"]
                    if isinstance(res_obj, str):
                        res_obj = json.loads(res_obj)
                    cloud_res["result"] = output_pydantic.model_validate(res_obj)
                except Exception as ve:
                    logger.error(f"Cloud output validation failed: {ve}")
            
            return {
                "result": cloud_res.get("result"),
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName", "cloud-unknown"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
            logger.warning(f"Cloud fallback triggered: {e}")

    # 3. Local Execution Selection
    df = _load_model_csv()
    if df.empty:
        raise RuntimeError("llm_model.csv not found or empty.")

    # Filter by API key availability
    available_models = []
    for _, row in df.iterrows():
        key_name = row['api_key']
        if _manage_api_key(key_name, row['provider']):
            available_models.append(row)
    
    if not available_models:
        raise RuntimeError("No models available with valid API keys.")

    # Select base model
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_model = next((m for m in available_models if m['model'] == default_model_name), available_models[0])
    
    # Interpolation Logic
    candidates = pd.DataFrame(available_models)
    if strength < 0.5:
        # Interpolate by cost (cheapest to base)
        # Scale: 0.0 -> cheapest, 0.5 -> base
        cheapest = candidates.loc[candidates['input_cost_per_m'].idxmin()]
        # Simple selection for now: strength=0 is cheapest
        target = cheapest if strength == 0 else base_model
    elif strength > 0.5:
        # Interpolate by ELO (base to highest)
        highest_elo = candidates.loc[candidates['coding_arena_elo'].idxmax()]
        target = highest_elo if strength == 1.0 else base_model
    else:
        target = base_model

    # 4. Prepare Invocation Params
    model_id = target['model']
    provider = target['provider']
    
    # Build Messages
    if not messages:
        if not prompt:
            raise ValueError("Prompt or messages must be provided.")
        processed_prompt = prompt
        if input_json:
            # Simple placeholder replacement
            if isinstance(input_json, dict):
                for k, v in input_json.items():
                    processed_prompt = processed_prompt.replace(f"{{{{{k}}}}}", str(v))
        messages = [{"role": "user", "content": processed_prompt}]

    # Reasoning parameters
    reasoning_type = target.get('reasoning_type', 'none')
    extra_params = {}
    
    if reasoning_type == 'budget':
        max_t = int(target.get('max_reasoning_tokens', 1024))
        budget = int(time * max_t)
        if "anthropic" in provider.lower():
            extra_params["thinking"] = {"type": "enabled", "budget_tokens": budget}
            temperature = 1.0 # Required for Anthropic thinking
    elif reasoning_type == 'effort':
        effort = "medium"
        if time < 0.33: effort = "low"
        elif time > 0.66: effort = "high"
        
        if "gpt-5" in model_id or "o1" in model_id: # Responses API logic
            extra_params["reasoning"] = {"effort": effort, "summary": "auto"}
        else:
            extra_params["reasoning_effort"] = effort

    # Structured Output logic
    if output_pydantic or output_schema:
        schema = output_schema or output_pydantic.model_json_schema()
        _ensure_all_properties_required(schema)
        _add_additional_properties_false(schema)
        
        if target.get('structured_output') == 1:
            extra_params["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "pdd_output", "schema": schema, "strict": True}
            }
        elif "groq" in provider.lower():
            messages.insert(0, {"role": "system", "content": f"Output must be valid JSON matching: {json.dumps(schema)}"})
            extra_params["response_format"] = {"type": "json_object"}

    # 5. Execute with Retries
    attempts = 0
    max_attempts = 2
    while attempts < max_attempts:
        try:
            # Handle Vertex AI specifics
            if "vertex" in provider.lower():
                extra_params["vertex_project"] = os.getenv("VERTEX_PROJECT")
                extra_params["vertex_location"] = target.get("location", os.getenv("VERTEX_LOCATION", "us-central1"))
                creds_path = os.getenv("VERTEX_CREDENTIALS")
                if creds_path:
                    with open(creds_path, 'r') as f:
                        extra_params["vertex_credentials"] = f.read()

            if use_batch_mode:
                # LiteLLM batch expects list of lists of messages
                batch_msgs = messages if isinstance(messages[0], list) else [messages]
                response = batch_completion(
                    model=model_id,
                    messages=batch_msgs,
                    temperature=temperature,
                    timeout=LLM_CALL_TIMEOUT,
                    **extra_params
                )
                # For brevity, returning first in batch result format
                raw_response = response[0]
            else:
                response = completion(
                    model=model_id,
                    messages=messages,
                    temperature=temperature,
                    timeout=LLM_CALL_TIMEOUT,
                    **extra_params
                )
                raw_response = response

            # 6. Post-Process Response
            content = raw_response.choices[0].message.content
            if not content:
                raise SchemaValidationError("Empty response from LLM")

            # Extract thinking
            thinking = ""
            if hasattr(raw_response.choices[0].message, "reasoning_content"):
                thinking = raw_response.choices[0].message.reasoning_content
            elif hasattr(raw_response, "_hidden_params"):
                thinking = raw_response._hidden_params.get("thinking", "")

            # Validation
            result = content
            if output_pydantic or output_schema:
                repaired = _repair_json(content)
                parsed = json.loads(repaired)
                
                if output_pydantic:
                    # Logic for Python validation repair
                    if language in ["python", None]:
                        for k, v in parsed.items():
                            if k not in ["reasoning", "explanation", "analysis"] and isinstance(v, str):
                                parsed[k] = _repair_python_syntax(v)
                    result = output_pydantic.model_validate(parsed)
                else:
                    result = parsed

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_id,
                "thinking_output": thinking
            }

        except Exception as e:
            attempts += 1
            err_str = str(e).lower()
            
            # Auth error handling
            if any(x in err_str for x in ["401", "unauthorized", "auth", "api_key"]):
                key_name = target['api_key']
                if os.getenv(f"{key_name}_NEW"):
                    console.print(f"[red]New key for {key_name} failed. Re-prompting...[/red]")
                    os.environ.pop(f"{key_name}_NEW", None)
                    _manage_api_key(key_name, provider)
                    continue
                if _is_wsl():
                    console.print("[yellow]WSL Detected: Check for carriage returns in your API keys.[/yellow]")

            # Fallback to next model on schema errors
            if isinstance(e, (SchemaValidationError, json.JSONDecodeError)) or "validation" in err_str:
                logger.warning(f"Model {model_id} failed validation. Trying fallback.")
                # Shift to next model in available list
                idx = next((i for i, m in enumerate(available_models) if m['model'] == model_id), 0)
                if idx + 1 < len(available_models):
                    target = available_models[idx + 1]
                    model_id = target['model']
                    provider = target['provider']
                    attempts = 0 # Reset for new model
                    continue
            
            if attempts >= max_attempts:
                raise RuntimeError(f"LLM invocation failed after {max_attempts} attempts: {e}")
            
            # Tiny jitter/wait before retry
            time_module.sleep(1)

    raise RuntimeError("Exhausted all model candidates.")

if __name__ == "__main__":
    # Example usage
    try:
        res = llm_invoke(prompt="Hello, who are you?", strength=0.5)
        print(res)
    except Exception as e:
        print(f"Error: {e}")