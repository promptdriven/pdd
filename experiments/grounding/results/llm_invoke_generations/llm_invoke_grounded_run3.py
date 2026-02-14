from __future__ import annotations

import os
import re
import json
import logging
import warnings
import time as time_module
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console
from litellm.caching.caching import Cache

# Internal module imports
from .path_resolution import get_default_resolver

# Standard logger setup
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")
console = Console()

# Constants
LLM_CALL_TIMEOUT = 120

# Module-level storage for success callback data
_LAST_CALLBACK_DATA = {
    "input_tokens": 0,
    "output_tokens": 0,
    "finish_reason": None,
    "cost": 0.0,
}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

# --- Custom Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM response fails Pydantic/JSON schema validation."""
    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0):
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index

class CloudFallbackError(Exception):
    """Recoverable cloud error triggering fallback to local."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """Raised for 402 Payment Required."""
    pass

# --- Configuration & Initialization ---

def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    if not log_file_path:
        return
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    litellm_logger.addHandler(handler)

def set_verbose_logging(verbose: bool = False) -> None:
    level = logging.DEBUG if (verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1") else logging.INFO
    logger.setLevel(level)
    if hasattr(litellm, "set_verbose"):
        litellm.set_verbose = (level == logging.DEBUG)

# Initial Logging Config
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION = os.getenv("PDD_ENVIRONMENT") == "production"
logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))
litellm_logger.setLevel(logging.WARNING if PRODUCTION else logging.INFO)

# LiteLLM drop unsupported params
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() in ("true", "1", "yes")

# Path Resolution
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
ENV_PATH = PROJECT_ROOT / ".env"
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

def _get_csv_path() -> Optional[Path]:
    candidates = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for path in candidates:
        if path.is_file():
            return path
    return None

LLM_MODEL_CSV_PATH = _get_csv_path()
DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT")

# Caching Setup
def _setup_cache() -> Optional[Cache]:
    if os.getenv("LITELLM_CACHE_DISABLE") == "1":
        return None
    
    bucket = os.getenv("GCS_BUCKET_NAME")
    hmac_id = os.getenv("GCS_HMAC_ACCESS_KEY_ID")
    hmac_secret = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
    
    if all([bucket, hmac_id, hmac_secret]):
        try:
            # S3-compatible GCS cache
            os.environ['AWS_ACCESS_KEY_ID'] = hmac_id.strip()
            os.environ['AWS_SECRET_ACCESS_KEY'] = hmac_secret.strip()
            return Cache(
                type="s3",
                s3_bucket_name=bucket,
                s3_endpoint_url="https://storage.googleapis.com",
                s3_region_name="auto"
            )
        except Exception as e:
            logger.warning(f"GCS cache init failed: {e}")
            
    try:
        return Cache(type="disk", disk_cache_dir=str(PROJECT_ROOT / "litellm_cache.sqlite"))
    except Exception:
        return None

litellm.cache = _setup_cache()

# Success Callback
def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, 'usage', None)
    _LAST_CALLBACK_DATA["input_tokens"] = getattr(usage, 'prompt_tokens', 0)
    _LAST_CALLBACK_DATA["output_tokens"] = getattr(usage, 'completion_tokens', 0)
    _LAST_CALLBACK_DATA["finish_reason"] = completion_response.choices[0].finish_reason
    
    try:
        cost = litellm.completion_cost(completion_response=completion_response)
        if cost is None:
            # CSV Fallback
            model = kwargs.get("model")
            rates = _MODEL_RATE_MAP.get(model, (0.0, 0.0))
            cost = (_LAST_CALLBACK_DATA["input_tokens"] * rates[0] + 
                    _LAST_CALLBACK_DATA["output_tokens"] * rates[1]) / 1_000_000
        _LAST_CALLBACK_DATA["cost"] = cost
    except Exception:
        _LAST_CALLBACK_DATA["cost"] = 0.0

litellm.success_callback = [_litellm_success_callback]

# --- Internal Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for prop in schema["properties"].values():
            _ensure_all_properties_required(prop)
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]: _ensure_all_properties_required(sub)
    if "items" in schema: _ensure_all_properties_required(schema["items"])
    if "$defs" in schema:
        for d in schema["$defs"].values(): _ensure_all_properties_required(d)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if not isinstance(schema, dict): return
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values(): _add_additional_properties_false(prop)
    if "items" in schema: _add_additional_properties_false(schema["items"])
    for key in ("anyOf", "oneOf", "allOf"):
        if key in schema:
            for sub in schema[key]: _add_additional_properties_false(sub)
    if "$defs" in schema:
        for d in schema["$defs"].values(): _add_additional_properties_false(d)

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, dict): return pydantic_class.model_validate(result)
    if isinstance(result, str): return pydantic_class.model_validate_json(result)
    return result

def _sanitize_key(key: str) -> str:
    return "".join(c for c in key.strip() if ord(c) >= 32)

def _is_prose_field(field: str) -> bool:
    prose_terms = {"reasoning", "explanation", "analysis", "thought", "summary", "description"}
    return any(t in field.lower() for t in prose_terms)

def _repair_python_syntax(code: str) -> str:
    import ast
    code = code.strip()
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        # Try stripping leading/trailing quotes
        for q in ('"', "'"):
            if code.startswith(q) and code.endswith(q):
                candidate = code[1:-1]
                try:
                    ast.parse(candidate)
                    return candidate
                except SyntaxError: continue
        return code

def _smart_unescape_code(code: str) -> str:
    # Logic to unescape structural \\n while preserving them in literals
    if '\\n' not in code or '\n' in code: return code
    return code.encode().decode('unicode_escape')

def _is_wsl() -> bool:
    return os.path.exists('/proc/version') and 'microsoft' in open('/proc/version').read().lower()

# --- Model Selection & API Keys ---

def _load_model_df() -> pd.DataFrame:
    if LLM_MODEL_CSV_PATH:
        df = pd.read_csv(LLM_MODEL_CSV_PATH)
    else:
        csv_text = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()
        import io
        df = pd.read_csv(io.StringIO(csv_text))
    
    global _MODEL_RATE_MAP
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[row['model']] = (row['input'], row['output'])
    return df

def _get_api_key(key_name: str, model_name: str) -> Optional[str]:
    if not key_name or key_name == "EXISTING_KEY":
        return "dummy"
    
    val = os.getenv(key_name)
    if val: return _sanitize_key(val)
    
    if os.getenv("PDD_FORCE"): return None
    
    try:
        val = input(f"Enter API Key for {model_name} ({key_name}): ").strip()
        if not val: return None
        val = _sanitize_key(val)
        os.environ[key_name] = val
        
        # Save to .env
        lines = []
        if ENV_PATH.exists():
            lines = ENV_PATH.read_text().splitlines()
        
        new_lines = [l for l in lines if not l.strip().startswith(f"{key_name}=") and not l.strip().startswith(f"# {key_name}=")]
        new_lines.append(f'{key_name}="{val}"')
        ENV_PATH.write_text("\n".join(new_lines) + "\n")
        console.print(f"[yellow]Security: Key saved to {ENV_PATH}[/yellow]")
        return val
    except EOFError:
        return None

# --- Cloud Execution ---

def _llm_invoke_cloud(
    prompt, input_json, messages, strength, temperature, time, verbose, 
    output_schema, use_batch_mode, language
) -> Dict[str, Any]:
    from pdd.core.cloud import CloudConfig # Lazy
    jwt = CloudConfig.get_jwt_token()
    if not jwt: raise CloudFallbackError("No cloud token")
    
    url = CloudConfig.get_endpoint_url("llmInvoke")
    payload = {
        "prompt": prompt, "inputJson": input_json, "messages": messages,
        "strength": strength, "temperature": temperature, "time": time,
        "verbose": verbose, "outputSchema": output_schema,
        "useBatchMode": use_batch_mode, "language": language
    }
    
    try:
        resp = requests.post(url, json=payload, headers={"Authorization": f"Bearer {jwt}"}, timeout=300)
        if resp.status_code == 402: raise InsufficientCreditsError("Insufficient credits")
        if resp.status_code in (401, 403):
            # Clear JWT cache logic
            raise CloudFallbackError("Cloud Auth Failed")
        resp.raise_for_status()
        data = resp.json()
        return {
            "result": data["result"],
            "cost": data["totalCost"],
            "model_name": data["modelName"],
            "thinking_output": data.get("thinkingOutput")
        }
    except requests.RequestException as e:
        raise CloudFallbackError(str(e))

# --- Public Interface ---

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
    
    set_verbose_logging(verbose)
    
    # 1. Cloud routing
    if use_cloud is None:
        use_cloud = (os.getenv("PDD_FORCE_LOCAL") != "1")
        try:
            from pdd.core.cloud import CloudConfig
            use_cloud = use_cloud and CloudConfig.is_cloud_enabled()
        except ImportError: use_cloud = False

    if use_cloud:
        try:
            effective_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
            res = _llm_invoke_cloud(prompt, input_json, messages, strength, temperature, time, verbose, 
                                    effective_schema, use_batch_mode, language)
            if output_pydantic:
                res["result"] = _validate_with_pydantic(res["result"], output_pydantic)
            return res
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed: {e}. Falling back to local.[/yellow]")
        except InsufficientCreditsError: raise

    # 2. Local Setup
    df = _load_model_df()
    base_name = DEFAULT_BASE_MODEL or df.iloc[0]['model']
    
    # Filtering and sorting candidates
    candidates = df.copy()
    # Simplified interpolation logic
    if strength == 0.5:
        candidates = candidates.sort_values("coding_arena_elo", ascending=False)
        # Put base model first
        is_base = (candidates["model"] == base_name)
        candidates = pd.concat([candidates[is_base], candidates[~is_base]])
    elif strength < 0.5:
        candidates = candidates.sort_values("input", ascending=True)
    else:
        candidates = candidates.sort_values("coding_arena_elo", ascending=False)

    # 3. Message Formatting
    if not messages:
        if isinstance(input_json, list): use_batch_mode = True
        if use_batch_mode:
            msgs = [[{"role": "user", "content": prompt.format(**item)}] for item in input_json] # type: ignore
        else:
            msgs = [{"role": "user", "content": prompt.format(**input_json)}] # type: ignore
    else:
        msgs = messages

    # 4. Try models
    last_err = None
    for _, row in candidates.iterrows():
        key = _get_api_key(row['api_key'], row['model'])
        if not key: continue
        
        try:
            call_kwargs: Dict[str, Any] = {
                "model": row['model'],
                "messages": msgs,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT,
                "api_key": os.getenv(row['api_key']) if row['api_key'] != "EXISTING_KEY" else None
            }
            
            # Reasoning Params
            rtype = row['reasoning_type']
            if rtype == 'budget':
                limit = int(time * row['max_reasoning_tokens'])
                if "anthropic" in row['provider'].lower():
                    call_kwargs["thinking"] = {"type": "enabled", "budget_tokens": limit}
                    call_kwargs["temperature"] = 1.0
            elif rtype == 'effort':
                effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
                if "gpt-5" in row['model']:
                    call_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                else:
                    call_kwargs["reasoning_effort"] = effort

            # Structured Output
            if (output_pydantic or output_schema) and row['structured_output']:
                s = output_schema or output_pydantic.model_json_schema() # type: ignore
                _ensure_all_properties_required(s)
                _add_additional_properties_false(s)
                fmt = {"type": "json_schema", "json_schema": {"name": "resp", "strict": True, "schema": s}}
                
                if "lm_studio" in row['model'].lower():
                    call_kwargs["extra_body"] = {"response_format": fmt}
                elif "groq" in row['model'].lower():
                    call_kwargs["response_format"] = {"type": "json_object"}
                    # Inject schema into system prompt...
                else:
                    call_kwargs["response_format"] = fmt

            # Execution
            if use_batch_mode:
                responses = litellm.batch_completion(**call_kwargs)
            else:
                if "gpt-5" in row['model']:
                    # Note: Responses API simplified implementation
                    responses = [litellm.completion(**call_kwargs)]
                else:
                    responses = [litellm.completion(**call_kwargs)]

            # 5. Result Processing
            final_results = []
            final_thinking = []
            for resp in responses:
                content = resp.choices[0].message.content
                if content is None: raise ValueError("None content")
                
                # Parsing logic
                if output_pydantic or output_schema:
                    try:
                        # Scan for JSON
                        json_str = content
                        if "```json" in content:
                            json_str = re.search(r"```json\s*(.*?)\s*```", content, re.S).group(1) # type: ignore
                        
                        parsed = json.loads(json_str)
                        if output_pydantic:
                            obj = output_pydantic.model_validate(parsed)
                            # Post-process code fields
                            for f_name in obj.model_fields:
                                val = getattr(obj, f_name)
                                if isinstance(val, str) and not _is_prose_field(f_name):
                                    processed = _smart_unescape_code(val)
                                    processed = _repair_python_syntax(processed)
                                    setattr(obj, f_name, processed)
                            final_results.append(obj)
                        else:
                            final_results.append(parsed)
                    except Exception as e:
                        raise SchemaValidationError(str(e), content)
                else:
                    final_results.append(content)
                
                think = getattr(resp.choices[0].message, "reasoning_content", None) or resp._hidden_params.get("thinking")
                final_thinking.append(think)

            return {
                "result": final_results if use_batch_mode else final_results[0],
                "cost": _LAST_CALLBACK_DATA["cost"],
                "model_name": row["model"],
                "thinking_output": final_thinking if use_batch_mode else final_thinking[0]
            }

        except (Exception) as e:
            # Simplified exception handling for extraction
            if _is_wsl() and "\r" in str(e):
                console.print("[red]WSL Error: CRLF detected in API Key. Check .env[/red]")
            last_err = e
            continue

    raise RuntimeError(f"All models failed. Last error: {last_err}")