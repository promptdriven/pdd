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

# Internal relative imports (as requested)
from . import DEFAULT_STRENGTH, EXTRACTION_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from pydantic import BaseModel

# Global Constants & Configuration
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
CONSOLE = Console()

# Logging Setup
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic/Schema validation to trigger fallback."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud errors that should trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required from Cloud."""
    pass

def setup_logging():
    level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    if os.getenv("PDD_ENVIRONMENT") == "production":
        level = "WARNING"
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        level = "DEBUG"
    
    logging.basicConfig(level=level)
    logger.setLevel(level)
    
    lt_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    litellm_logger.setLevel(lt_level)
    
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

def _get_project_root() -> Path:
    resolver = get_default_resolver()
    try:
        return Path(resolver.resolve_project_root())
    except Exception:
        return Path(os.getcwd())

def _load_env():
    root = _get_project_root()
    env_path = root / ".env"
    load_dotenv(dotenv_path=env_path)

def _get_model_csv_path() -> Path:
    resolver = get_default_resolver()
    # Priority order per requirements
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        _get_project_root() / ".pdd" / "llm_model.csv",
        Path(os.getcwd()) / ".pdd" / "llm_model.csv"
    ]
    for p in paths:
        if p.exists(): return p
    try:
        return Path(resolver.resolve_data_file("pdd/data/llm_model.csv"))
    except:
        return Path("pdd/data/llm_model.csv")

def _success_callback(kwargs, response_obj, start_time, end_time):
    global _LAST_CALLBACK_DATA
    _LAST_CALLBACK_DATA = {
        "usage": getattr(response_obj, "usage", {}),
        "model": kwargs.get("model"),
        "response": response_obj
    }

litellm.success_callback = [_success_callback]

def _handle_api_key(provider: str, key_name: str) -> str:
    key = os.getenv(key_name)
    if key and key != "EXISTING_KEY":
        return key.strip().strip('"').strip("'")
    
    if os.getenv("PDD_FORCE"):
        return ""

    CONSOLE.print(f"[yellow]Missing API Key for {provider} ({key_name})[/yellow]")
    user_key = input(f"Enter {key_name}: ").strip()
    
    # Sanitize for WSL/Windows issues
    user_key = re.sub(r"[\r\n\t]", "", user_key)
    
    root = _get_project_root()
    env_path = root / ".env"
    set_key(str(env_path), key_name, user_key)
    os.environ[key_name] = user_key
    
    CONSOLE.print(f"[bold green]Key saved to {env_path}. Ensure this file is .gitignored![/bold green]")
    return user_key

def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
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
    if "$defs" in schema:
        for d in schema["$defs"].values():
            _ensure_all_properties_required(d)
    return schema

def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values():
                _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])
    return schema

def _repair_json(raw: str) -> str:
    raw = raw.strip()
    # Try to find JSON block
    match = re.search(r"```json\s*(.*?)\s*```", raw, re.DOTALL)
    if match: raw = match.group(1)
    
    # Simple truncation repair
    if raw.startswith("{") and not raw.endswith("}"):
        raw += "}"
    return raw

def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines often found in LLM JSON output for code."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    schema = _ensure_all_properties_required(schema)
    schema = _add_additional_properties_false(schema)
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Execute via PDD Cloud endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudInvocationError("PDD_CLOUD_TOKEN not found for cloud execution.")
    
    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    try:
        headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
        resp = requests.post(url, json=payload, timeout=300)
        
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits.")
        if resp.status_code in [401, 403]:
            # Token might be expired
            raise CloudFallbackError(f"Cloud Auth Error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {str(e)}")

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
    setup_logging()

    # Cloud logic
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_use_cloud = use_cloud if use_cloud is not None else (not force_local)

    if should_use_cloud:
        try:
            cloud_payload = {
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
            res = _llm_invoke_cloud(cloud_payload)
            
            # Validation for cloud results
            result_data = res.get("result")
            if output_pydantic and isinstance(result_data, (str, dict)):
                if isinstance(result_data, str):
                    result_data = json.loads(_repair_json(result_data))
                res["result"] = output_pydantic.model_validate(result_data)
                
            return res
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud failed, falling back to local: {e}[/yellow]")
            if use_cloud is True: raise # If explicitly forced, don't fallback

    # Local Logic
    df = pd.read_csv(_get_model_csv_path())
    
    # Model Selection Logic
    available_models = df[df['api_key'].notna()].copy()
    default_model_name = os.getenv("PDD_MODEL_DEFAULT")
    
    base_model_row = available_models[available_models['model'] == default_model_name]
    if base_model_row.empty:
        base_model_row = available_models.iloc[[0]]
    
    base_model = base_model_row.iloc[0]
    
    if strength == 0.5:
        candidates = [base_model]
        # Append others as fallback
        others = available_models[available_models['model'] != base_model['model']].sort_values('coding_arena_elo', ascending=False)
        candidates.extend([row for _, row in others.iterrows()])
    elif strength < 0.5:
        # Interpolate by cost
        candidates = available_models[available_models['input_cost'] <= base_model['input_cost']].sort_values('input_cost', ascending=True)
    else:
        # Interpolate by ELO
        candidates = available_models[available_models['coding_arena_elo'] >= base_model['coding_arena_elo']].sort_values('coding_arena_elo', ascending=False)

    # Execution Loop
    last_error = None
    for _, m_row in candidates.iterrows():
        model_name = m_row['model']
        provider = m_row['provider']
        
        # Auth
        api_key = _handle_api_key(provider, m_row['api_key'])
        if not api_key: continue

        # Prepare reasoning params
        r_type = m_row.get('reasoning_type', 'none')
        max_r = m_row.get('max_reasoning_tokens', 0)
        extra_kwargs = {}
        
        if r_type == 'budget':
            budget = int(time * max_r)
            if "anthropic" in provider.lower():
                extra_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                temperature = 1.0 # Requirement
        elif r_type == 'effort':
            effort = "medium"
            if time < 0.3: effort = "low"
            elif time > 0.7: effort = "high"
            
            if "gpt-5" in model_name: # Hypothetical future model per requirement
                extra_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                extra_kwargs["reasoning_effort"] = effort

        # Format messages
        if messages:
            final_messages = messages
        else:
            processed_prompt = prompt
            if input_json:
                # Simple placeholder replacement if dict, batch logic if list handled by litellm
                if isinstance(input_json, dict):
                    for k, v in input_json.items():
                        processed_prompt = processed_prompt.replace(f"{{{{{k}}}}}", str(v))
            final_messages = [{"role": "user", "content": processed_prompt}]

        # Structured Output Handling
        if output_pydantic or output_schema:
            schema = output_schema or _pydantic_to_json_schema(output_pydantic)
            if m_row.get('structured_output') == 1:
                extra_kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "schema": schema, "strict": True}
                }
            elif "groq" in provider.lower():
                final_messages.insert(0, {"role": "system", "content": f"Output JSON matching: {json.dumps(schema)}"})
                extra_kwargs["response_format"] = {"type": "json_object"}

        try:
            call_func = completion
            if use_batch_mode: call_func = batch_completion
            
            # Vertex AI Credentials Logic
            if "vertex" in provider.lower() or "google" in provider.lower():
                extra_kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
                extra_kwargs["vertex_location"] = m_row.get('location') or os.getenv("VERTEX_LOCATION")
                v_cred = os.getenv("VERTEX_CREDENTIALS")
                if v_cred and Path(v_cred).exists():
                    extra_kwargs["vertex_credentials"] = Path(v_cred).read_text()

            response = call_func(
                model=model_name,
                messages=final_messages,
                temperature=temperature,
                api_key=api_key,
                timeout=LLM_CALL_TIMEOUT,
                num_retries=2,
                **extra_kwargs
            )

            # Process result
            raw_content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            
            # Cost calculation
            cost = 0.0
            try:
                cost = completion_cost(response)
            except:
                # Fallback to CSV rates
                usage = getattr(response, "usage", None)
                if usage:
                    cost = (usage.prompt_tokens * m_row['input_cost'] + usage.completion_tokens * m_row['output_cost']) / 1_000_000

            result = raw_content
            if output_pydantic:
                parsed = json.loads(_repair_json(raw_content))
                # Smart unescape logic for code
                if isinstance(parsed, dict):
                    for k, v in parsed.items():
                        if isinstance(v, str) and k not in ["reasoning", "explanation"]:
                            parsed[k] = _smart_unescape_code(v)
                result = output_pydantic.model_validate(parsed)

            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.error(f"Error with model {model_name}: {e}")
            last_error = e
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_error}")

if __name__ == "__main__":
    # Quick test
    print(llm_invoke(prompt="Say hello", strength=0.5))