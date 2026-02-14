from __future__ import annotations

import os
import json
import logging
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

# Internal relative imports as required
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
PDD_MODEL_CSV_NAME = "llm_model.csv"
CONSOLE = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or JSON schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (network, auth, 5xx) - trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required - do not fall back."""
    pass

# --- Logging Setup ---

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    log_dir = Path.cwd() / "logs"
    log_dir.mkdir(exist_ok=True)
    handler = RotatingFileHandler(log_dir / "pdd.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(verbose: bool):
    level = logging.DEBUG if verbose else logging.INFO
    logger.setLevel(level)
    if verbose:
        litellm.set_verbose = True

# --- Path & Env Resolution ---

def _get_project_root() -> Path:
    resolver = get_default_resolver()
    try:
        return Path(resolver.resolve_project_root())
    except Exception:
        return Path.cwd()

def _load_env():
    root = _get_project_root()
    env_path = root / ".env"
    load_dotenv(dotenv_path=env_path)

def _resolve_model_csv() -> Path:
    resolver = get_default_resolver()
    # Priority: ~/.pdd -> <ROOT>/.pdd -> <CWD>/.pdd -> package data
    paths = [
        Path.home() / ".pdd" / PDD_MODEL_CSV_NAME,
        _get_project_root() / ".pdd" / PDD_MODEL_CSV_NAME,
        Path.cwd() / ".pdd" / PDD_MODEL_CSV_NAME
    ]
    for p in paths:
        if p.exists():
            return p
    try:
        return Path(resolver.resolve_data_file(f"data/{PDD_MODEL_CSV_NAME}"))
    except Exception:
        raise FileNotFoundError(f"Could not locate {PDD_MODEL_CSV_NAME}")

# --- Helper Utilities ---

def _is_wsl() -> bool:
    return "microsoft-standard" in Path("/proc/version").read_text().lower() if Path("/proc/version").exists() else False

def _sanitize_api_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for p_val in props.values():
            _ensure_all_properties_required(p_val)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for prop in schema.get("properties", {}).values():
            _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

def _smart_unescape_code(text: str) -> str:
    # Fix double escaped newlines in code fields while preserving them in prose
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _repair_python_syntax(code: str) -> str:
    # Basic repair for common LLM truncation/syntax errors
    code = code.strip()
    if code.count('"""') % 2 != 0:
        code += '"""'
    if code.count("'''") % 2 != 0:
        code += "'''"
    return code

def _extract_json(text: str) -> str:
    # Try fenced blocks
    json_match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if json_match:
        return json_match.group(1)
    # Try balanced braces
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end != -1:
        return text[start:end+1]
    return text

# --- LiteLLM Callback ---

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        model = kwargs.get("model", "unknown")
        usage = response_obj.get("usage", {})
        cost = completion_cost(completion_response=response_obj) or 0.0
        
        # Fallback to CSV if LiteLLM returns 0 cost
        if cost == 0 and model in _MODEL_RATE_MAP:
            in_tokens = usage.get("prompt_tokens", 0)
            out_tokens = usage.get("completion_tokens", 0)
            rates = _MODEL_RATE_MAP[model]
            cost = (in_tokens * rates['input'] / 1_000_000) + (out_tokens * rates['output'] / 1_000_000)

        _LAST_CALLBACK_DATA = {
            "cost": cost,
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.error(f"Callback error: {e}")

litellm.success_callback = [_success_callback]

# --- API Key Mgmt ---

def _handle_missing_key(key_name: str, provider: str) -> bool:
    if os.getenv("PDD_FORCE"):
        return False
    
    CONSOLE.print(f"[bold yellow]Missing API key for {provider}: {key_name}[/bold yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    if not new_key:
        return False
    
    new_key = _sanitize_api_key(new_key)
    os.environ[key_name] = new_key
    
    env_path = _get_project_root() / ".env"
    # Manual update of .env to handle clean replacement
    lines = []
    if env_path.exists():
        lines = env_path.read_text().splitlines()
    
    # Remove existing/commented versions
    new_lines = [l for l in lines if not l.strip().startswith(f"{key_name}=") and not l.strip().startswith(f"#{key_name}=")]
    new_lines.append(f"{key_name}={new_key}")
    env_path.write_text("\n".join(new_lines) + "\n")
    
    CONSOLE.print(f"[bold green]Key saved to {env_path}. Protect this file![/bold green]")
    return True

# --- Model Logic ---

def _select_models(strength: float) -> List[Dict]:
    csv_path = _resolve_model_csv()
    df = pd.read_csv(csv_path)
    
    # Build global rate map for callback fallback
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row['model']] = {
            'input': row.get('input_cost_per_m', 0),
            'output': row.get('output_cost_per_m', 0)
        }

    # Filter by API key availability (env)
    valid_models = []
    for _, row in df.iterrows():
        key_name = str(row.get('api_key', ''))
        if not key_name or key_name == "EXISTING_KEY" or os.getenv(key_name):
            valid_models.append(row.to_dict())
    
    if not valid_models:
        return []

    # Get Base Model
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_model = next((m for m in valid_models if m['model'] == default_model_name), valid_models[0])
    
    # Interpolation
    if strength == 0.5:
        # Preferred base model, then others by ELO
        sorted_models = sorted(valid_models, key=lambda x: x.get('coding_arena_elo', 0), reverse=True)
        if base_model in sorted_models:
            sorted_models.remove(base_model)
            sorted_models.insert(0, base_model)
        return sorted_models
    
    if strength < 0.5:
        # Base down to cheapest
        candidates = [m for m in valid_models if m.get('input_cost_per_m', 0) <= base_model.get('input_cost_per_m', 999)]
        return sorted(candidates, key=lambda x: x.get('input_cost_per_m', 0))
    else:
        # Base up to highest ELO
        candidates = [m for m in valid_models if m.get('coding_arena_elo', 0) >= base_model.get('coding_arena_elo', 0)]
        return sorted(candidates, key=lambda x: x.get('coding_arena_elo', 0), reverse=True)

# --- Cloud Invocation ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict:
    schema = pydantic_class.model_json_schema()
    schema["title"] = pydantic_class.__name__
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    return schema

def _llm_invoke_cloud(payload: Dict) -> Dict:
    # Implementation of cloud transport via requests
    cloud_url = os.getenv("PDD_CLOUD_URL", "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke")
    token = os.getenv("PDD_CLOUD_TOKEN")
    
    if not token:
        raise CloudFallbackError("No cloud token found.")

    try:
        resp = requests.post(
            cloud_url,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in [401, 403]:
            # Clear cache if implemented, for now raise fallback
            raise CloudFallbackError("Cloud auth error.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

# --- Core Function ---

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
    Executes an LLM call using LiteLLM with fallback, cloud, and structured output logic.
    """
    _load_env()
    set_verbose_logging(verbose)
    
    # Cloud Logic
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is None:
        use_cloud = not force_local # Simplified for this snippet

    if use_cloud:
        try:
            schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
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
            cloud_res = _llm_invoke_cloud(payload)
            # Result validation
            result = cloud_res["result"]
            if output_pydantic and isinstance(result, (dict, str)):
                if isinstance(result, str): result = json.loads(_extract_json(result))
                result = output_pydantic.model_validate(result)
            
            return {
                "result": result,
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName", "cloud-proxy"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except CloudFallbackError as e:
            CONSOLE.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise
        except Exception as e:
            CONSOLE.print(f"[red]Cloud error: {e}[/red]")

    # Local Logic
    candidates = _select_models(strength)
    if not candidates:
        raise RuntimeError("No models available. Check your .env for API keys or llm_model.csv.")

    # Prep messages
    if not messages:
        if not prompt: raise ValueError("Prompt or Messages must be provided.")
        processed_prompt = prompt
        if input_json:
            # Simple template replacement
            if isinstance(input_json, dict):
                for k, v in input_json.items():
                    processed_prompt = processed_prompt.replace(f"{{{{{k}}}}}", str(v))
        
        system_msg = "You are a helpful coding assistant."
        if output_pydantic or output_schema:
            schema_str = json.dumps(output_schema or output_pydantic.model_json_schema(), indent=2)
            system_msg += f"\nRespond strictly in valid JSON matching this schema:\n{schema_str}"
        
        messages = [
            {"role": "system", "content": system_msg},
            {"role": "user", "content": processed_prompt}
        ]

    # Caching Setup
    litellm.cache = None
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(type="s3", s3_bucket_name=os.getenv("GCS_BUCKET_NAME"))
        else:
            litellm.cache = litellm.Cache(type="disk", cache_filename=str(_get_project_root() / "litellm_cache.sqlite"))

    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

    last_error = None
    for model_row in candidates:
        model_name = model_row['model']
        provider = model_row['provider']
        
        # Check Auth
        key_env = model_row.get('api_key')
        if key_env and key_env != "EXISTING_KEY" and not os.getenv(key_env):
            if not _handle_missing_key(key_env, provider):
                continue

        # Reasoning Params
        call_params = {
            "model": model_name,
            "messages": messages,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        r_type = model_row.get('reasoning_type', 'none')
        max_r_tokens = int(model_row.get('max_reasoning_tokens', 0))
        
        if r_type == 'budget' and max_r_tokens > 0:
            budget = int(time * max_r_tokens)
            if "anthropic" in provider.lower():
                call_params["thinking"] = {"type": "enabled", "budget_tokens": budget}
                call_params["temperature"] = 1.0 # Anthropic requirement
        elif r_type == 'effort':
            effort = "medium"
            if time < 0.33: effort = "low"
            elif time > 0.66: effort = "high"
            call_params["reasoning_effort"] = effort

        # Structured Output
        if (output_pydantic or output_schema) and model_row.get('structured_output') == 1:
            schema = output_schema or _pydantic_to_json_schema(output_pydantic)
            call_params["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "result_schema", "schema": schema, "strict": True}
            }

        try:
            if "gpt-5" in model_name: # Placeholder for Responses API logic
                # responses() logic
                response = completion(**call_params)
            elif use_batch_mode:
                response = batch_completion(**call_params)
            else:
                response = completion(**call_params)

            content = response.choices[0].message.content
            if not content:
                raise ValueError("Empty response from model.")

            # Parse & Validate
            result = content
            if output_pydantic or output_schema:
                try:
                    raw_json = _extract_json(content)
                    parsed = json.loads(raw_json)
                    if output_pydantic:
                        # Smart unescape for code
                        for k, v in parsed.items():
                            if isinstance(v, str) and k not in ["reasoning", "explanation"]:
                                parsed[k] = _smart_unescape_code(v)
                        result = output_pydantic.model_validate(parsed)
                    else:
                        result = parsed
                except Exception as e:
                    raise SchemaValidationError(f"Schema fail: {e}")

            # Extract Thinking
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            if not thinking and hasattr(response, "_hidden_params"):
                thinking = response._hidden_params.get("thinking")

            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            last_error = e
            logger.warning(f"Model {model_name} failed: {e}")
            if "Authentication" in str(e) and _is_wsl():
                CONSOLE.print("[yellow]WSL Detected: Check your API key for hidden \\r characters.[/yellow]")
            continue

    raise RuntimeError(f"All models exhausted. Last error: {last_error}")

if __name__ == "__main__":
    # Quick test if run directly
    try:
        res = llm_invoke(prompt="Say hello in {{language}}", input_json={"language": "Python"}, strength=0.5)
        print(res)
    except Exception as e:
        print(f"Main Error: {e}")
