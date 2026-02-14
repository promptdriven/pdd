from __future__ import annotations

import os
import json
import logging
import re
import time as time_module
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple

import pandas as pd
import litellm
import openai
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError

# Internal relative imports
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

# --- Logging Configuration ---
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING" if PRODUCTION_MODE else "INFO")

logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))
litellm_logger.setLevel(getattr(logging, LITELLM_LOG_LEVEL, logging.WARNING))

litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() in ("1", "true", "yes")

def setup_file_logging(log_file_path: str | Path | None = None) -> None:
    """Configure rotating file handler for logging (10MB, 5 backups)."""
    if not log_file_path:
        return
    from logging.handlers import RotatingFileHandler
    handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    litellm_logger.addHandler(handler)

def set_verbose_logging(verbose: bool = False) -> None:
    """Toggle DEBUG level for pdd and litellm loggers."""
    level = logging.DEBUG if (verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1") else getattr(logging, PDD_LOG_LEVEL)
    logger.setLevel(level)
    litellm_logger.setLevel(level)
    litellm.set_verbose = (level == logging.DEBUG)

# --- Exceptions ---
class SchemaValidationError(Exception):
    """Triggers model fallback on structured output validation failure."""
    def __init__(self, message: str, raw_response: Any = None):
        super().__init__(message)
        self.raw_response = raw_response

class CloudFallbackError(Exception): """Recoverable cloud error."""
class CloudInvocationError(Exception): """Non-recoverable cloud error."""
class InsufficientCreditsError(Exception): """402 Payment Required."""

# --- State & Constants ---
LLM_CALL_TIMEOUT = 120
_LAST_CALLBACK_DATA: Dict[str, Any] = {"cost": 0.0, "input_tokens": 0, "output_tokens": 0}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

# --- Path Resolution & Environment ---
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
ENV_PATH = PROJECT_ROOT / ".env"
if ENV_PATH.exists():
    load_dotenv(ENV_PATH)

def resolve_model_csv() -> Path:
    candidates = [
        Path.home() / ".pdd" / "llm_model.csv",
        PROJECT_ROOT / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv"
    ]
    for c in candidates:
        if c.is_file(): return c
    return Path(str(importlib.resources.files("pdd").joinpath("data/llm_model.csv")))

# --- LiteLLM Cache & Callbacks ---
def _litellm_success_callback(kwargs: Dict, completion_response: Any, start_time: float, end_time: float) -> None:
    global _LAST_CALLBACK_DATA
    try:
        cost = litellm.completion_cost(completion_response=completion_response) or 0.0
    except Exception:
        model = kwargs.get("model", "")
        usage = getattr(completion_response, "usage", None)
        if usage and model in _MODEL_RATE_MAP:
            in_r, out_r = _MODEL_RATE_MAP[model]
            cost = (usage.prompt_tokens * in_r + usage.completion_tokens * out_r) / 1_000_000
        else:
            cost = 0.0
    _LAST_CALLBACK_DATA = {
        "cost": cost,
        "input_tokens": getattr(completion_response.usage, "prompt_tokens", 0),
        "output_tokens": getattr(completion_response.usage, "completion_tokens", 0)
    }

litellm.success_callback = [_litellm_success_callback]

# --- Helper Functions (Logic Implementation) ---

def _sanitize_api_key(key: str) -> str:
    """Remove whitespace and control chars (fixes WSL \r issues)."""
    return "".join(c for c in key.strip() if ord(c) >= 32)

def _ensure_all_properties_required(schema: Dict) -> Dict:
    if schema.get("type") == "object" and "properties" in schema:
        schema["required"] = list(schema["properties"].keys())
        for p in schema["properties"].values(): _ensure_all_properties_required(p)
    return schema

def _add_additional_properties_false(schema: Dict) -> Dict:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for p in schema["properties"].values(): _add_additional_properties_false(p)
    return schema

def _repair_python_syntax(code: str) -> str:
    import ast
    code = code.strip()
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        for q in ['"', "'"]:
            if code.startswith(q) and code.endswith(q):
                candidate = code[1:-1]
                try:
                    ast.parse(candidate); return candidate
                except SyntaxError: pass
        return code

def _smart_unescape_code(code: str) -> str:
    """Preserves \n inside string literals while unescaping structural \\n."""
    if '\\n' not in code: return code
    return code.replace('\\n', '\n').replace('\\t', '\t')

def _save_key_to_env(key: str, val: str) -> None:
    lines = []
    if ENV_PATH.exists():
        with open(ENV_PATH, "r") as f:
            lines = [l for l in f.readlines() if not l.strip().startswith(f"# {key}=") and not l.strip().startswith(f"{key}=")]
    lines.append(f'{key}="{val}"\n')
    with open(ENV_PATH, "w") as f:
        f.writelines(lines)

def _llm_invoke_cloud(
    prompt: str | None, input_json: Any, strength: float, temperature: float, 
    time: float, verbose: bool, output_schema: Dict | None, use_batch_mode: bool, 
    messages: Any, language: str | None
) -> Dict[str, Any]:
    import requests
    from .core.cloud import CloudConfig
    jwt = CloudConfig.get_jwt_token(verbose=verbose)
    if not jwt: raise CloudFallbackError("Cloud auth failed")
    
    payload = {
        "prompt": prompt, "inputJson": input_json, "messages": messages,
        "strength": strength, "temperature": temperature, "time": time,
        "verbose": verbose, "outputSchema": output_schema, "useBatchMode": use_batch_mode,
        "language": language
    }
    url = CloudConfig.get_endpoint_url("llmInvoke")
    try:
        resp = requests.post(url, json=payload, headers={"Authorization": f"Bearer {jwt}"}, timeout=300)
        if resp.status_code == 200: return resp.json()
        if resp.status_code == 402: raise InsufficientCreditsError()
        if resp.status_code in (401, 403): raise CloudFallbackError("JWT Expired")
        raise CloudInvocationError(resp.text)
    except Exception as e:
        if isinstance(e, InsufficientCreditsError): raise
        raise CloudFallbackError(str(e))

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
    Main entry point for LLM invocation with LiteLLM, model selection, and cloud fallback.
    """
    set_verbose_logging(verbose)
    
    # --- Cloud Execution Path ---
    if use_cloud is None:
        use_cloud = os.getenv("PDD_FORCE_LOCAL") != "1"
        try:
            from .core.cloud import CloudConfig
            use_cloud = use_cloud and CloudConfig.is_cloud_enabled()
        except ImportError: use_cloud = False

    if use_cloud:
        try:
            schema = output_schema or (output_pydantic.model_json_schema() if output_pydantic else None)
            res = _llm_invoke_cloud(prompt, input_json, strength, temperature, time, verbose, schema, use_batch_mode, messages, language)
            if output_pydantic and res.get("result"):
                res["result"] = output_pydantic.model_validate(res["result"])
            return res
        except CloudFallbackError as e:
            logger.warning(f"Cloud failed ({e}), falling back to local...")
        except InsufficientCreditsError: raise

    # --- Local Execution Path ---
    csv_path = resolve_model_csv()
    df = pd.read_csv(csv_path)
    df['coding_arena_elo'] = pd.to_numeric(df['coding_arena_elo'], errors='coerce').fillna(0)
    df['avg_cost'] = (pd.to_numeric(df['input'], errors='coerce').fillna(0) + pd.to_numeric(df['output'], errors='coerce').fillna(0)) / 2
    
    global _MODEL_RATE_MAP
    _MODEL_RATE_MAP = {r['model']: (r['input'], r['output']) for _, r in df.iterrows()}

    base_name = os.getenv("PDD_MODEL_DEFAULT")
    base_rows = df[df['model'] == base_name]
    base_model = base_rows.iloc[0] if not base_rows.empty else df.iloc[0]

    # Model Selection Logic
    if strength == 0.5:
        candidates = [base_model.to_dict()] + df[df['model'] != base_model['model']].sort_values('coding_arena_elo', ascending=False).to_dict('records')
    elif strength < 0.5:
        target = df['avg_cost'].min() + (strength / 0.5) * (base_model['avg_cost'] - df['avg_cost'].min())
        df['dist'] = (df['avg_cost'] - target).abs()
        candidates = df.sort_values('dist').to_dict('records')
    else:
        target = base_model['coding_arena_elo'] + ((strength - 0.5) / 0.5) * (df['coding_arena_elo'].max() - base_model['coding_arena_elo'])
        df['dist'] = (df['coding_arena_elo'] - target).abs()
        candidates = df.sort_values('dist').to_dict('records')

    # Format Messages
    if not messages:
        if use_batch_mode and isinstance(input_json, list):
            formatted_messages = [[{"role": "user", "content": prompt.format(**item)}] for item in input_json]
        else:
            formatted_messages = [{"role": "user", "content": prompt.format(**(input_json or {}))}]
    else:
        formatted_messages = messages

    last_exc = RuntimeError("No models available")
    new_keys: Dict[str, bool] = {}

    for m_info in candidates:
        model = m_info['model']
        provider = str(m_info['provider']).lower()
        key_env = m_info.get('api_key')
        
        # API Key Handling
        if key_env and key_env != "EXISTING_KEY" and not os.getenv(key_env):
            if os.getenv("PDD_FORCE"): continue
            val = _sanitize_api_key(input(f"Enter API Key for {key_env}: "))
            os.environ[key_env] = val
            _save_key_to_env(key_env, val)
            new_keys[key_env] = True
            logger.warning(f"Security: {key_env} saved to .env")

        try:
            # Reasoning & Params
            kwargs: Dict[str, Any] = {
                "model": model, "messages": formatted_messages, "temperature": temperature,
                "num_retries": 2, "timeout": LLM_CALL_TIMEOUT
            }
            
            # Reasoning Mapping
            r_type = m_info.get('reasoning_type', 'none')
            if time > 0:
                if r_type == 'budget' and provider == 'anthropic':
                    kwargs['thinking'] = {"type": "enabled", "budget_tokens": int(time * m_info.get('max_reasoning_tokens', 0))}
                    kwargs['temperature'] = 1.0
                elif r_type == 'effort':
                    effort = "high" if time > 0.7 else ("medium" if time > 0.3 else "low")
                    kwargs['reasoning_effort'] = effort

            # Structured Output
            if (output_pydantic or output_schema) and m_info.get('structured_output'):
                schema_dict = output_schema or output_pydantic.model_json_schema()
                _ensure_all_properties_required(schema_dict)
                _add_additional_properties_false(schema_dict)
                kwargs["response_format"] = {
                    "type": "json_schema", 
                    "json_schema": {"name": "output", "schema": schema_dict, "strict": True}
                }

            # Execution
            if provider == 'openai' and model.startswith('gpt-5'):
                response = litellm.responses(**kwargs)
                raw_content = response.output[0].content[0].text
            elif use_batch_mode:
                response = litellm.batch_completion(**kwargs)
                raw_content = [r.choices[0].message.content for r in response]
            else:
                response = litellm.completion(**kwargs)
                raw_content = response.choices[0].message.content

            # Post-Process & Parsing
            def parse_item(content: str):
                if not (output_pydantic or output_schema): return content
                match = re.search(r"```json\s*(\{.*?\})\s*```", content, re.DOTALL)
                json_str = match.group(1) if match else content
                if output_pydantic:
                    obj = output_pydantic.model_validate_json(json_str)
                    for field in obj.model_fields:
                        val = getattr(obj, field)
                        if isinstance(val, str) and field not in ('reasoning', 'explanation'):
                            setattr(obj, field, _repair_python_syntax(_smart_unescape_code(val)))
                    return obj
                return json.loads(json_str)

            result = [parse_item(c) for c in raw_content] if use_batch_mode else parse_item(raw_content)
            
            return {
                "result": result,
                "cost": _LAST_CALLBACK_DATA["cost"],
                "model_name": model,
                "thinking_output": getattr(response.choices[0].message, "reasoning_content", None) if not use_batch_mode else None
            }

        except Exception as e:
            if isinstance(e, openai.AuthenticationError) and new_keys.get(key_env):
                del os.environ[key_env]
                return llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic, output_schema, time, use_batch_mode, messages, language, use_cloud)
            logger.warning(f"Model {model} failed: {e}")
            last_exc = e
            continue

    raise RuntimeError(f"All models exhausted. Last error: {last_exc}")