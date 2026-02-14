from __future__ import annotations

import os
import json
import logging
import re
import csv
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING
from logging.handlers import RotatingFileHandler

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv, set_key
from pydantic import BaseModel
from rich.console import Console

# Internal imports based on package structure requirements
from . import (
    EXTRACTION_STRENGTH,
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
)
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from pydantic import BaseModel

# Global Constants & State
LLM_CALL_TIMEOUT = 120
LITELLM_CACHE_FILE = "litellm_cache.sqlite"
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger("pdd.llm_invoke")

# Custom Exceptions
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

# --- Logging Configuration ---

def setup_file_logging(log_file: str = "pdd.log") -> None:
    handler = RotatingFileHandler(log_file, maxBytes=10 * 1024 * 1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(enabled: bool = True) -> None:
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    if enabled:
        os.environ["PDD_VERBOSE_LOGGING"] = "1"

def _configure_logging() -> None:
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    env = os.getenv("PDD_ENVIRONMENT", "production")
    
    if env == "production" and lite_level == "DEBUG":
        lite_level = "WARNING"
        
    logging.basicConfig(level=logging.WARNING)
    logger.setLevel(pdd_level)
    logging.getLogger("litellm").setLevel(lite_level)
    
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        logger.setLevel(logging.DEBUG)

# --- Path & Env Resolution ---

def _load_env() -> None:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    env_path = project_root / ".env"
    if env_path.exists():
        load_dotenv(dotenv_path=env_path)
    else:
        load_dotenv()

def _get_model_csv_path() -> Path:
    resolver = get_default_resolver()
    # (a) ~/.pdd/llm_model.csv
    p1 = Path.home() / ".pdd" / "llm_model.csv"
    if p1.exists(): return p1
    # (b) <PROJECT_ROOT>/.pdd/llm_model.csv
    try:
        p2 = resolver.resolve_project_root() / ".pdd" / "llm_model.csv"
        if p2.exists(): return p2
    except Exception: pass
    # (c) <cwd>/.pdd/llm_model.csv
    p3 = Path.cwd() / ".pdd" / "llm_model.csv"
    if p3.exists(): return p3
    # (d) packaged data
    return resolver.resolve_data_file("llm_model.csv")

# --- Key Management ---

def _is_wsl() -> bool:
    if os.name != 'posix': return False
    try:
        with open('/proc/version', 'r') as f:
            return 'microsoft' in f.read().lower()
    except:
        return "WSL_DISTRO_NAME" in os.environ

def _prompt_for_key(key_name: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
    
    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name}")
    key = input(f"Please enter your {key_name}: ").strip()
    
    # WSL Sanitize
    if _is_wsl():
        key = key.replace('\r', '').replace('\n', '')
        
    if not key:
        return ""

    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    env_path = root / ".env"
    
    # Save to .env
    set_key(str(env_path), key_name, key)
    os.environ[key_name] = key
    
    logger.warning(f"Security: Saved {key_name} to {env_path}")
    return key

# --- LiteLLM Callbacks & Utils ---

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response_obj, "usage", {})
        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "cost": litellm.completion_cost(response_obj),
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception as e:
        logger.debug(f"Callback error: {e}")

litellm.success_callback = [_success_callback]
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() == "true"

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        if "properties" in schema:
            schema["required"] = list(schema["properties"].keys())
            for prop in schema["properties"].values():
                _ensure_all_properties_required(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values():
                _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

# --- JSON/Python Repair ---

def _repair_python_syntax(code: str) -> str:
    code = code.strip()
    # Basic trailing quote fix
    if (code.count('"""') % 2) != 0: code += '"""'
    if (code.count("'''") % 2) != 0: code += "'''"
    return code

def _smart_unescape_code(json_str: str) -> str:
    # Unescape double-escaped newlines while preserving formatting
    return json_str.replace("\\\\n", "\n").replace("\\n", "\n")

def _parse_llm_json(content: str) -> Any:
    # 1. Try fenced block
    match = re.search(r"```json\s*(.*?)\s*```", content, re.DOTALL)
    if match:
        content = match.group(1)
    
    # 2. Balanced extraction
    try:
        start = content.find('{')
        end = content.rfind('}')
        if start != -1 and end != -1:
            json_snippet = content[start:end+1]
            return json.loads(json_snippet)
    except Exception:
        pass
    
    # 3. Truncated repair (basic)
    if content.strip() and not content.strip().endswith('}'):
        content += '}'
        
    try:
        return json.loads(content)
    except Exception as e:
        raise SchemaValidationError(f"JSON Parse Error: {e}")

# --- Model Selection Logic ---

def _select_models(strength: float, csv_path: Path) -> List[Dict[str, Any]]:
    df = pd.read_csv(csv_path)
    # Populate rates
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row['model']] = {"input": row['input'], "output": row['output']}
        
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Filter by API key availability
    def has_key(row):
        key_name = str(row['api_key'])
        if key_name in ["EXISTING_KEY", "nan", ""]: return True
        return os.getenv(key_name) is not None or not os.getenv("PDD_FORCE")
        
    available_df = df[df.apply(has_key, axis=1)].copy()
    if available_df.empty:
        return []

    # Find base
    base_row = None
    if default_model_name:
        matches = available_df[available_df['model'] == default_model_name]
        if not matches.empty:
            base_row = matches.iloc[0]
            
    if base_row is None:
        base_row = available_df.iloc[0]

    base_elo = base_row['coding_arena_elo']
    base_cost = base_row['input'] + base_row['output']

    if strength == 0.5:
        # Priority: Base, then higher ELO
        higher = available_df[available_df['coding_arena_elo'] >= base_elo].sort_values('coding_arena_elo')
        return higher.to_dict('records')
    
    if strength < 0.5:
        # Interpolate by cost: Base down to cheapest
        cheaper = available_df[available_df['input'] + available_df['output'] <= base_cost]
        return cheaper.sort_values(['input', 'output'], ascending=False).to_dict('records')
    else:
        # Interpolate by ELO: Base up to highest
        better = available_df[available_df['coding_arena_elo'] >= base_elo]
        return better.sort_values('coding_arena_elo', ascending=True).to_dict('records')

# --- Cloud Invocation ---

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict, List[Dict]]],
    messages: Optional[Union[List[Dict], List[List[Dict]]]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str]
) -> Dict[str, Any]:
    # Placeholder for cloud URL - usually derived from config
    cloud_url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No cloud token found")

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
        resp = requests.post(
            cloud_url,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits")
        if resp.status_code in [401, 403]:
            # Clear cache if needed, then fallback
            raise CloudFallbackError(f"Cloud Auth Error: {resp.status_code}")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {resp.status_code}")
        
        resp.raise_for_status()
        data = resp.json()
        return {
            "result": data.get("result"),
            "cost": data.get("totalCost", 0.0),
            "model_name": data.get("modelName"),
            "thinking_output": data.get("thinkingOutput")
        }
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Network error: {e}")

# --- Main Function ---

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
    _load_env()
    _configure_logging()
    
    if verbose:
        set_verbose_logging(True)

    # Cloud Logic
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
        # Check CloudConfig equivalent logic here if available

    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, 
                time, verbose, output_schema or (output_pydantic.model_json_schema() if output_pydantic else None),
                use_batch_mode, language
            )
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud Warning:[/yellow] {e}. Falling back to local.")
        except InsufficientCreditsError:
            raise

    # Local Execution Path
    csv_path = _get_model_csv_path()
    candidates = _select_models(strength, csv_path)
    
    if not candidates:
        raise RuntimeError("No models available in CSV.")

    # Prepare Structured Output Schema
    final_schema = None
    if output_pydantic:
        final_schema = output_pydantic.model_json_schema()
    elif output_schema:
        final_schema = output_schema

    if final_schema:
        _ensure_all_properties_required(final_schema)
        _add_additional_properties_false(final_schema)

    # Resolve Messages
    if not messages:
        if not prompt:
            raise ValueError("Prompt or messages must be provided.")
        formatted_prompt = prompt.format(**(input_json if isinstance(input_json, dict) else {}))
        current_messages = [{"role": "user", "content": formatted_prompt}]
    else:
        current_messages = messages

    # Caching
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(type="s3", s3_bucket_name=os.getenv("GCS_BUCKET_NAME"))
        else:
            litellm.cache = litellm.Cache(type="disk", cache_filename=str(get_default_resolver().resolve_project_root() / LITELLM_CACHE_FILE))

    for model_row in candidates:
        model_name = model_row['model']
        provider = model_row['provider']
        api_key_name = str(model_row['api_key'])
        
        # Key check/prompt
        api_key = os.getenv(api_key_name)
        newly_acquired = False
        if not api_key and api_key_name not in ["EXISTING_KEY", "nan", ""]:
            api_key = _prompt_for_key(api_key_name)
            newly_acquired = True
            if not api_key: continue

        # Reasoning Config
        reasoning_type = model_row.get('reasoning_type', 'none')
        max_reasoning = int(model_row.get('max_reasoning_tokens', 0))
        extra_params = {}
        
        if reasoning_type == 'budget' and max_reasoning > 0:
            budget = int(time * max_reasoning)
            if 'anthropic' in provider.lower():
                extra_params['thinking'] = {"type": "enabled", "budget_tokens": budget}
                temperature = 1.0 # Forced for Anthropic thinking
        elif reasoning_type == 'effort':
            effort = "medium"
            if time < 0.33: effort = "low"
            elif time > 0.66: effort = "high"
            extra_params['reasoning_effort'] = effort

        # Structured Output Mode
        resp_format = None
        if final_schema and model_row.get('structured_output'):
            resp_format = {
                "type": "json_schema",
                "json_schema": {"name": "pdd_output", "schema": final_schema, "strict": True}
            }

        try:
            call_params = {
                "model": model_name,
                "messages": current_messages,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT,
                "api_key": api_key,
                "base_url": model_row.get('base_url') if pd.notna(model_row.get('base_url')) else None,
                "response_format": resp_format,
                **extra_params
            }

            # Vertex AI Logic
            if 'vertex_ai' in provider.lower() or 'vertex_ai' in model_name:
                call_params['vertex_project'] = os.getenv("VERTEX_PROJECT")
                call_params['vertex_location'] = model_row.get('location') or os.getenv("VERTEX_LOCATION", "us-central1")
                creds_path = os.getenv("VERTEX_CREDENTIALS")
                if creds_path and Path(creds_path).exists():
                    call_params['vertex_credentials'] = Path(creds_path).read_text()

            # Execute
            if model_name.startswith("gpt-5"): # Responses API
                # Mocking litellm.responses call behavior as per requirements
                response = litellm.completion(**call_params) 
            elif use_batch_mode:
                response = litellm.batch_completion(**call_params)
            else:
                response = litellm.completion(**call_params)

            # Process Response
            content = response.choices[0].message.content
            if not content:
                # Cache bypass retry
                call_params['messages'][-1]['content'] += " "
                response = litellm.completion(**call_params)
                content = response.choices[0].message.content

            result = content
            if final_schema:
                result = _parse_llm_json(content)
                if language == "python" or language is None:
                    # Validate Python fields
                    for k, v in result.items():
                        if k not in ["reasoning", "explanation", "analysis"] and isinstance(v, str):
                            result[k] = _repair_python_syntax(_smart_unescape_code(v))

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
            logger.error(f"Error with model {model_name}: {e}")
            if newly_acquired and ("auth" in str(e).lower() or "401" in str(e)):
                os.environ.pop(api_key_name, None)
                continue # Retry same model with new key? (Simplified)
            
            if isinstance(e, SchemaValidationError):
                continue # Try next model
            
            continue # Fallback

    raise RuntimeError("All LLM candidates exhausted.")

if __name__ == "__main__":
    # Quick test
    res = llm_invoke(prompt="Say hello in {lang}", input_json={"lang": "Python"})
    print(res)