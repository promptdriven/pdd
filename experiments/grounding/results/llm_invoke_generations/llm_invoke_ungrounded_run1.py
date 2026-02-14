from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from datetime import datetime
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
from . import DEFAULT_STRENGTH, EXTRACTION_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

# --- Constants & Global State ---
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic/Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable errors that trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Logging Setup ---

def setup_file_logging():
    from logging.handlers import RotatingFileHandler
    log_dir = Path("logs")
    log_dir.mkdir(exist_ok=True)
    handler = RotatingFileHandler(log_dir / "llm_invoke.log", maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(enabled: bool = True):
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    if enabled:
        litellm.set_verbose = True

# --- Utilities ---

def _detect_wsl() -> bool:
    return "WSL_DISTRO_NAME" in os.environ or (Path("/proc/version").exists() and "microsoft" in Path("/proc/version").read_text().lower())

def _sanitize_key(key: str) -> str:
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
            for item in schema[key]:
                _ensure_all_properties_required(item)
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
            for item in schema[key]:
                _add_additional_properties_false(item)

def _smart_unescape_code(text: str) -> str:
    """Unescape double-escaped newlines while preserving formatting."""
    return text.replace("\\n", "\n").replace("\\\"", "\"")

def _repair_python_syntax(code: str) -> str:
    code = code.strip()
    if code.count('"""') % 2 != 0: code += '"""'
    if code.count("'''") % 2 != 0: code += "'''"
    return code

def _extract_json(text: str) -> str:
    # Try fenced blocks first
    match = re.search(r"```json\s*(.*?)\s*```", text, re.DOTALL)
    if match: return match.group(1)
    
    # Try finding balanced braces
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end != -1:
        return text[start:end+1]
    return text

# --- Core Logic ---

def _get_api_key_interactively(provider: str, key_name: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
    
    console.print(f"[bold yellow]Missing API Key for {provider} ({key_name})[/bold yellow]")
    key = _sanitize_key(input(f"Enter {key_name}: "))
    
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    env_path = root / ".env"
    
    set_key(str(env_path), key_name, key)
    os.environ[key_name] = key
    
    console.print(f"[bold green]Key saved to {env_path}[/bold green]")
    logger.warning(f"Security: API key for {provider} saved to local .env file.")
    return key

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _llm_invoke_cloud(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Client for the cloud llmInvoke endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found.")

    endpoint = os.getenv("PDD_CLOUD_URL", "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke")
    
    try:
        response = requests.post(
            endpoint,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits in PDD Cloud.")
        if response.status_code in [401, 403]:
            # Clear cache logic here if needed
            raise CloudFallbackError(f"Cloud Auth Error: {response.text}")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {response.status_code}")
            
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudInvocationError(f"Cloud request failed: {e}")

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
    
    # 1. Environment & Config
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    load_dotenv(root / ".env")
    
    if verbose: set_verbose_logging(True)
    
    # 2. Cloud Execution Logic
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
        
    if use_cloud:
        try:
            cloud_payload = {
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
            res = _llm_invoke_cloud(cloud_payload)
            
            # Re-validate result if pydantic model provided
            if output_pydantic and res.get("result"):
                res["result"] = output_pydantic.model_validate(res["result"])
            return res
            
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
            logger.warning(f"Cloud Fallback: {e}")
        except InsufficientCreditsError:
            raise

    # 3. Model Selection (Local)
    csv_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    
    df = None
    for p in csv_paths:
        if p.exists():
            df = pd.read_csv(p)
            break
            
    if df is None:
        raise RuntimeError("llm_model.csv not found.")

    # Populate cost map
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row['model']] = {
            'input': row.get('input_cost_per_m', 0) / 1_000_000,
            'output': row.get('output_cost_per_m', 0) / 1_000_000
        }

    # Model interpolation logic
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available_models = df[df['api_key'].notna() | (df['provider'] == 'lm_studio')].copy()
    
    if base_model_name and base_model_name in available_models['model'].values:
        base_row = available_models[available_models['model'] == base_model_name].iloc[0]
    else:
        base_row = available_models.iloc[0] # Surrogate

    if strength == 0.5:
        candidates = [base_row['model']]
        # Append others sorted by ELO for fallback
        others = available_models[available_models['model'] != base_row['model']].sort_values('coding_arena_elo', ascending=False)
        candidates.extend(others['model'].tolist())
    elif strength < 0.5:
        # Interpolate cost base -> cheapest
        available_models['cost_rank'] = available_models['input_cost_per_m'] + available_models['output_cost_per_m']
        candidates = available_models.sort_values('cost_rank')['model'].tolist()
    else:
        # Interpolate ELO base -> highest
        candidates = available_models.sort_values('coding_arena_elo', ascending=False)['model'].tolist()

    # 4. LiteLLM Setup
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # Caching
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(type="s3", s3_bucket_name=os.getenv("GCS_BUCKET_NAME"), 
                                         s3_api_base="https://storage.googleapis.com",
                                         s3_access_key_id=os.getenv("GCS_HMAC_ACCESS_KEY_ID"),
                                         s3_secret_access_key=os.getenv("GCS_HMAC_SECRET_ACCESS_KEY"))
        else:
            litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(root / "litellm_cache.sqlite"))

    def success_callback(kwargs, response_obj, start_time, end_time):
        global _LAST_CALLBACK_DATA
        _LAST_CALLBACK_DATA = {
            "usage": getattr(response_obj, "usage", {}),
            "model": kwargs.get("model"),
            "cost": completion_cost(completion_response=response_obj)
        }
    litellm.success_callback = [success_callback]

    # 5. Invocation Loop
    last_exception = None
    for model_name in candidates:
        row = available_models[available_models['model'] == model_name].iloc[0]
        provider = row['provider']
        key_name = row['api_key']
        
        # Key management
        api_key = os.getenv(key_name) if pd.notna(key_name) else None
        if not api_key and provider != 'lm_studio':
            api_key = _get_api_key_interactively(provider, key_name)
            if not api_key: continue

        # Construct Messages
        current_messages = messages
        if not current_messages:
            processed_prompt = prompt
            if input_json:
                # Basic jinja-style or string.format replacement simplified here
                if isinstance(input_json, dict):
                    for k, v in input_json.items():
                        processed_prompt = processed_prompt.replace(f"{{{{{k}}}}}", str(v))
            current_messages = [{"role": "user", "content": processed_prompt}]

        # Reasoning & Params
        kwargs: Dict[str, Any] = {
            "model": model_name,
            "messages": current_messages,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
            "api_key": api_key
        }

        # Provider specific tweaks
        if provider == "vertex_ai":
            kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
            kwargs["vertex_location"] = row.get("location") or os.getenv("VERTEX_LOCATION")
            creds_path = os.getenv("VERTEX_CREDENTIALS")
            if creds_path: kwargs["vertex_credentials"] = Path(creds_path).read_text()
        
        if provider == "lm_studio":
            kwargs["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
            kwargs["api_key"] = "lm-studio"

        # Reasoning logic
        r_type = row.get('reasoning_type', 'none')
        max_r_tokens = row.get('max_reasoning_tokens', 0)
        if r_type == 'budget' and max_r_tokens > 0:
            budget = int(time * max_r_tokens)
            if "anthropic" in model_name:
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                kwargs["temperature"] = 1.0 # Required for Anthropic thinking
        elif r_type == 'effort':
            effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
            kwargs["reasoning_effort"] = effort

        # Structured Output
        if output_pydantic or output_schema:
            schema = output_schema or _pydantic_to_json_schema(output_pydantic)
            if row.get('structured_output') == True:
                kwargs["response_format"] = {"type": "json_schema", "json_schema": {"name": "output", "schema": schema, "strict": True}}
            elif "groq" in provider:
                kwargs["response_format"] = {"type": "json_object"}
                current_messages[0]["content"] += f"\nReturn valid JSON matching: {json.dumps(schema)}"

        try:
            # Handle OpenAI gpt-5 (o1/o3) Responses API via LiteLLM
            if "gpt-5" in model_name or model_name.startswith("o1") or model_name.startswith("o3"):
                # Use litellm.completion but adjust for reasoning if LiteLLM maps it correctly, 
                # or use specific Responses API if supported.
                pass 

            if use_batch_mode and isinstance(messages, list) and isinstance(messages[0], list):
                response = batch_completion(**kwargs)
            else:
                response = completion(**kwargs)

            # Process Response
            raw_content = response.choices[0].message.content
            thinking = getattr(response.choices[0].message, "reasoning_content", None) or response._hidden_params.get("thinking")
            
            # JSON parsing / Repair
            result = raw_content
            if output_pydantic or output_schema:
                json_str = _extract_json(raw_content)
                try:
                    data = json.loads(json_str)
                    if output_pydantic:
                        result = output_pydantic.model_validate(data)
                    else:
                        result = data
                except Exception as je:
                    # Truncated JSON repair attempt
                    if not json_str.endswith("}"): json_str += "}"
                    try: 
                        data = json.loads(json_str)
                        result = output_pydantic.model_validate(data) if output_pydantic else data
                    except:
                        raise SchemaValidationError(f"JSON Parse Error: {je}")

            # Cost Calculation
            cost = _LAST_CALLBACK_DATA.get("cost")
            if cost is None:
                usage = _LAST_CALLBACK_DATA.get("usage", {})
                rates = _MODEL_RATE_MAP.get(model_name, {'input': 0, 'output': 0})
                cost = (usage.get('prompt_tokens', 0) * rates['input']) + (usage.get('completion_tokens', 0) * rates['output'])

            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            last_exception = e
            logger.error(f"Error with model {model_name}: {e}")
            if "authentication" in str(e).lower() and _detect_wsl():
                console.print("[red]WSL Detected: Check your API keys for trailing carriage returns (\r).[/red]")
            continue

    raise last_exception or RuntimeError("All model candidates failed.")

if __name__ == "__main__":
    # Example usage
    setup_file_logging()
    try:
        res = llm_invoke(prompt="Say hello in {{lang}}", input_json={"lang": "Python"})
        console.print(res)
    except Exception as e:
        console.print(f"Failed: {e}")