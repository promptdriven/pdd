from __future__ import annotations

import os
import json
import logging
import warnings
import time as time_module
import importlib.resources
import re
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple

import pandas as pd
import litellm
from litellm.caching.caching import Cache
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
import openai
import requests
from rich.console import Console

# Relative imports for internal modules
try:
    from .path_resolution import get_default_resolver
except ImportError:
    from pdd.path_resolution import get_default_resolver

# --- Configure Logging ---
logger = logging.getLogger("pdd.llm_invoke")

PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"

if PRODUCTION_MODE:
    logger.setLevel(logging.WARNING)
else:
    logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))

litellm_logger = logging.getLogger("litellm")
litellm_log_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING" if PRODUCTION_MODE else "INFO")
litellm_logger.setLevel(getattr(logging, litellm_log_level, logging.WARNING))

# Suppress LiteLLM debug messages
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# Set litellm.drop_params
try:
    _drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_params_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

if not logger.handlers:
    console_handler = logging.StreamHandler()
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(console_handler)

def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    if not log_file_path:
        return
    try:
        from logging.handlers import RotatingFileHandler
        file_handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
        file_handler.setFormatter(logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s'))
        logger.addHandler(file_handler)
        litellm_logger.addHandler(file_handler)
        logger.info(f"File logging configured to: {log_file_path}")
    except Exception as e:
        logger.warning(f"Failed to set up file logging: {e}")

def set_verbose_logging(verbose: bool = False) -> None:
    want_verbose = bool(verbose) or os.getenv("PDD_VERBOSE_LOGGING") == "1"
    if want_verbose:
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)
    else:
        if PRODUCTION_MODE:
            logger.setLevel(logging.WARNING)
        else:
            logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))
        litellm_logger.setLevel(getattr(logging, litellm_log_level, logging.WARNING))
    
    try:
        if hasattr(litellm, "set_verbose"):
            litellm.set_verbose = want_verbose
        if hasattr(litellm, "suppress_debug_info"):
            litellm.suppress_debug_info = not want_verbose
    except Exception:
        pass

# --- Custom Exceptions ---
class SchemaValidationError(Exception):
    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0):
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index

class CloudFallbackError(Exception):
    pass

class CloudInvocationError(Exception):
    pass

class InsufficientCreditsError(Exception):
    pass

# --- Configuration & Path Resolution ---
PDD_PATH_ENV = os.getenv("PDD_PATH")
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env

user_pdd_dir = Path.home() / ".pdd"
user_model_csv_path = user_pdd_dir / "llm_model.csv"

def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    try:
        current_dir = Path.cwd().resolve()
        for _ in range(max_levels):
            if ((current_dir / ".git").exists() or 
                (current_dir / "pyproject.toml").exists() or 
                (current_dir / "data").is_dir() or 
                (current_dir / ".env").exists()):
                return current_dir
            parent = current_dir.parent
            if parent == current_dir:
                break
            current_dir = parent
    except Exception:
        pass
    return Path.cwd().resolve()

project_root_from_cwd = _detect_project_root_from_cwd()
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"

try:
    _installed_pkg_root = importlib.resources.files('pdd')
    try:
        _installed_pkg_root_path = Path(str(_installed_pkg_root))
    except Exception:
        _installed_pkg_root_path = None
except Exception:
    _installed_pkg_root_path = None

def _is_env_path_package_dir(env_path: Path) -> bool:
    try:
        if _installed_pkg_root_path is None:
            return False
        env_path = env_path.resolve()
        pkg_path = _installed_pkg_root_path.resolve()
        return env_path == pkg_path or str(env_path).startswith(str(pkg_path))
    except Exception:
        return False

if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
else:
    ENV_PATH = PROJECT_ROOT / ".env"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH = user_model_csv_path
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
else:
    LLM_MODEL_CSV_PATH = None

if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", None)

# --- LiteLLM Cache Setup ---
GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID")
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
GCS_ENDPOINT_URL = "https://storage.googleapis.com"
GCS_REGION_NAME = os.getenv("GCS_REGION_NAME", "auto")

if GCS_HMAC_ACCESS_KEY_ID: GCS_HMAC_ACCESS_KEY_ID = GCS_HMAC_ACCESS_KEY_ID.strip()
if GCS_HMAC_SECRET_ACCESS_KEY: GCS_HMAC_SECRET_ACCESS_KEY = GCS_HMAC_SECRET_ACCESS_KEY.strip()

cache_configured = False
configured_cache = None

if GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    original_aws_keys = {
        'AWS_ACCESS_KEY_ID': os.environ.get('AWS_ACCESS_KEY_ID'),
        'AWS_SECRET_ACCESS_KEY': os.environ.get('AWS_SECRET_ACCESS_KEY'),
        'AWS_REGION_NAME': os.environ.get('AWS_REGION_NAME')
    }
    try:
        os.environ['AWS_ACCESS_KEY_ID'] = GCS_HMAC_ACCESS_KEY_ID
        os.environ['AWS_SECRET_ACCESS_KEY'] = GCS_HMAC_SECRET_ACCESS_KEY
        configured_cache = Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_region_name=GCS_REGION_NAME,
            s3_endpoint_url=GCS_ENDPOINT_URL,
        )
        litellm.cache = configured_cache
        cache_configured = True
    except Exception as e:
        warnings.warn(f"Failed to configure LiteLLM S3/GCS cache: {e}")
        litellm.cache = None
    finally:
        for k, v in original_aws_keys.items():
            if v is not None: os.environ[k] = v
            elif k in os.environ: del os.environ[k]

if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    litellm.cache = None
    cache_configured = True

if not cache_configured:
    try:
        sqlite_cache_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_cache_path))
        litellm.cache = configured_cache
        cache_configured = True
    except Exception:
        litellm.cache = None

# --- LiteLLM Callback ---
_LAST_CALLBACK_DATA = {"input_tokens": 0, "output_tokens": 0, "finish_reason": None, "cost": 0.0}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, 'usage', None)
    input_tokens = getattr(usage, 'prompt_tokens', 0) or 0
    output_tokens = getattr(usage, 'completion_tokens', 0) or 0
    finish_reason = getattr(completion_response.choices[0], 'finish_reason', None)
    
    calculated_cost = 0.0
    try:
        cost_val = litellm.completion_cost(completion_response=completion_response)
        calculated_cost = cost_val if cost_val is not None else 0.0
    except Exception:
        try:
            model_name = kwargs.get("model")
            if model_name:
                rates = _MODEL_RATE_MAP.get(str(model_name))
                if rates:
                    calculated_cost = (float(input_tokens) * rates[0] + float(output_tokens) * rates[1]) / 1_000_000.0
        except Exception:
            pass
            
    _LAST_CALLBACK_DATA["input_tokens"] = input_tokens
    _LAST_CALLBACK_DATA["output_tokens"] = output_tokens
    _LAST_CALLBACK_DATA["finish_reason"] = finish_reason
    _LAST_CALLBACK_DATA["cost"] = calculated_cost

litellm.success_callback = [_litellm_success_callback]

def _set_model_rate_map(df: pd.DataFrame) -> None:
    global _MODEL_RATE_MAP
    try:
        _MODEL_RATE_MAP = {
            str(row['model']): (
                float(row['input']) if pd.notna(row['input']) else 0.0,
                float(row['output']) if pd.notna(row['output']) else 0.0,
            )
            for _, row in df.iterrows()
        }
    except Exception:
        _MODEL_RATE_MAP = {}

# --- Cloud Helpers ---
def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(schema, dict): return schema
    if schema.get('type') == 'object' and 'properties' in schema:
        schema['required'] = list(schema['properties'].keys())
        for prop_schema in schema['properties'].values():
            _ensure_all_properties_required(prop_schema)
    if schema.get('type') == 'array' and 'items' in schema:
        _ensure_all_properties_required(schema['items'])
    for key in ('anyOf', 'oneOf', 'allOf'):
        if key in schema:
            for sub_schema in schema[key]: _ensure_all_properties_required(sub_schema)
    if '$defs' in schema:
        for def_schema in schema['$defs'].values(): _ensure_all_properties_required(def_schema)
    return schema

def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(schema, dict): return schema
    if schema.get('type') == 'object':
        schema['additionalProperties'] = False
        if 'properties' in schema:
            for prop_schema in schema['properties'].values(): _add_additional_properties_false(prop_schema)
    if schema.get('type') == 'array' and 'items' in schema:
        _add_additional_properties_false(schema['items'])
    for key in ('anyOf', 'oneOf', 'allOf'):
        if key in schema:
            for sub_schema in schema[key]: _add_additional_properties_false(sub_schema)
    if '$defs' in schema:
        for def_schema in schema['$defs'].values(): _add_additional_properties_false(def_schema)
    return schema

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema['__pydantic_class_name__'] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    elif isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    elif isinstance(result, pydantic_class):
        return result
    raise ValueError(f"Cannot validate result type {type(result)} with Pydantic model")

def _llm_invoke_cloud(
    prompt: Optional[str], input_json: Any, strength: float, temperature: float,
    verbose: bool, output_pydantic: Any, output_schema: Any, time: float,
    use_batch_mode: bool, messages: Any, language: Any
) -> Dict[str, Any]:
    try:
        from pdd.core.cloud import CloudConfig
        from pdd.auth_service import clear_jwt_cache
    except ImportError:
        raise CloudFallbackError("Cloud modules not available")

    console = Console()
    jwt_token = CloudConfig.get_jwt_token(verbose=verbose)
    if not jwt_token: raise CloudFallbackError("Could not authenticate with cloud")

    payload = {
        "strength": strength, "temperature": temperature, "time": time,
        "verbose": verbose, "useBatchMode": use_batch_mode
    }
    if language: payload["language"] = language
    if messages: payload["messages"] = messages
    else:
        payload["prompt"] = prompt
        payload["inputJson"] = input_json
    
    if output_pydantic: payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema: payload["outputSchema"] = output_schema

    try:
        response = requests.post(
            CloudConfig.get_endpoint_url("llmInvoke"),
            json=payload,
            headers={"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"},
            timeout=300
        )
        if response.status_code == 200:
            data = response.json()
            result = data.get("result")
            if output_pydantic and result:
                try: result = _validate_with_pydantic(result, output_pydantic)
                except Exception as e:
                    logger.warning(f"Cloud response validation failed: {e}")
            return {
                "result": result, "cost": data.get("totalCost", 0.0),
                "model_name": data.get("modelName", "cloud_model"),
                "thinking_output": data.get("thinkingOutput")
            }
        elif response.status_code == 402:
            raise InsufficientCreditsError(response.json().get("error", "Insufficient credits"))
        elif response.status_code in (401, 403):
            try: clear_jwt_cache()
            except Exception: pass
            raise CloudFallbackError(f"Auth expired: {response.json().get('error', '')}")
        elif response.status_code >= 500:
            raise CloudFallbackError(f"Server error: {response.json().get('error', '')}")
        else:
            raise CloudInvocationError(f"Cloud failed: {response.json().get('error', '')}")
    except (requests.exceptions.ConnectionError, requests.exceptions.Timeout, requests.exceptions.RequestException) as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

# --- Environment & API Key Helpers ---
def _is_wsl_environment() -> bool:
    try:
        if os.path.exists('/proc/version'):
            with open('/proc/version', 'r') as f:
                if 'microsoft' in f.read().lower(): return True
        return bool(os.getenv('WSL_DISTRO_NAME'))
    except Exception:
        return False

def _sanitize_api_key(key: str) -> str:
    if not key: return key
    sanitized = key.strip()
    if any(ord(c) < 32 for c in sanitized):
        sanitized = ''.join(c for c in sanitized if ord(c) >= 32)
    return sanitized

def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    lines = []
    if env_path.exists():
        with open(env_path, 'r') as f: lines = f.readlines()
    
    new_lines = []
    replaced = False
    prefix = f"{key_name}="
    
    for line in lines:
        stripped = line.strip()
        if stripped.startswith(f"# {prefix}") or stripped.startswith(f"# {key_name} ="):
            continue
        elif stripped.startswith(prefix) or stripped.startswith(f"{key_name} ="):
            new_lines.append(f'{key_name}="{value}"\n')
            replaced = True
        else:
            new_lines.append(line)
    
    if not replaced:
        if new_lines and not new_lines[-1].endswith('\n'): new_lines.append('\n')
        new_lines.append(f'{key_name}="{value}"\n')
        
    with open(env_path, 'w') as f: f.writelines(new_lines)

def _ensure_api_key(model_info: Dict[str, Any], newly_acquired: Dict[str, bool], verbose: bool) -> bool:
    key_name = model_info.get('api_key')
    if not key_name or key_name == "EXISTING_KEY": return True
    
    val = os.getenv(key_name)
    if val:
        os.environ[key_name] = _sanitize_api_key(val)
        newly_acquired[key_name] = False
        return True
        
    if os.getenv('PDD_FORCE'):
        logger.error(f"API key {key_name} missing in force mode")
        return False
        
    try:
        val = input(f"Please enter API key for {key_name}: ").strip()
        if not val: return False
        val = _sanitize_api_key(val)
        os.environ[key_name] = val
        newly_acquired[key_name] = True
        try:
            _save_key_to_env_file(key_name, val, ENV_PATH)
            logger.warning(f"Key {key_name} saved to .env")
        except Exception as e:
            logger.error(f"Failed to save key: {e}")
        return True
    except Exception:
        return False

# --- Data Loading & Model Selection ---
def _load_model_data(path: Optional[Path]) -> pd.DataFrame:
    if path and path.exists():
        try:
            df = pd.read_csv(path)
        except Exception:
            path = None
    if not path:
        try:
            data = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()
            import io
            df = pd.read_csv(io.StringIO(data))
        except Exception as e:
            raise FileNotFoundError(f"Could not load models: {e}")
            
    cols = ['input', 'output', 'coding_arena_elo', 'max_reasoning_tokens']
    for c in cols: 
        if c in df.columns: df[c] = pd.to_numeric(df[c], errors='coerce').fillna(0)
    
    df['avg_cost'] = (df['input'] + df['output']) / 2
    if 'structured_output' in df.columns:
        df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
    else:
        df['structured_output'] = False
    
    df['reasoning_type'] = df['reasoning_type'].fillna('none').astype(str).str.lower()
    df['api_key'] = df['api_key'].fillna('').astype(str)
    return df

def _select_model_candidates(strength: float, base_model: Optional[str], df: pd.DataFrame) -> List[Dict]:
    available = df[df['api_key'].notna()].copy()
    if available.empty: raise ValueError("No models available in CSV")
    
    base_row = available[available['model'] == base_model]
    if base_row.empty:
        # Fallback to first available model silently per prompt requirements
        base_rec = available.iloc[0]
        base_cost = base_rec['avg_cost']
        base_elo = base_rec['coding_arena_elo']
        base_name = base_rec['model']
    else:
        base_rec = base_row.iloc[0]
        base_cost = base_rec['avg_cost']
        base_elo = base_rec['coding_arena_elo']
        base_name = base_model

    if strength == 0.5:
        available['sort_metric'] = -available['coding_arena_elo']
        candidates = available.sort_values('sort_metric').to_dict('records')
        candidates.sort(key=lambda x: 0 if x['model'] == base_name else 1)
    elif strength < 0.5:
        min_cost = available['avg_cost'].min()
        target = min_cost + (strength / 0.5) * (base_cost - min_cost)
        available['sort_metric'] = abs(available['avg_cost'] - target)
        candidates = available.sort_values('sort_metric').to_dict('records')
    else:
        max_elo = available['coding_arena_elo'].max()
        target = base_elo + ((strength - 0.5) / 0.5) * (max_elo - base_elo)
        available['sort_metric'] = abs(available['coding_arena_elo'] - target)
        candidates = available.sort_values('sort_metric').to_dict('records')
        
    return candidates

# --- Processing Helpers ---
def _format_messages(prompt: str, input_data: Any, batch: bool) -> Any:
    if batch:
        if not isinstance(input_data, list): raise ValueError("Batch requires list input")
        return [[{"role": "user", "content": prompt.format(**item)}] for item in input_data]
    else:
        if not isinstance(input_data, dict): raise ValueError("Non-batch requires dict input")
        return [{"role": "user", "content": prompt.format(**input_data)}]

def _extract_fenced_json_block(text: str) -> Optional[str]:
    m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, re.IGNORECASE)
    return m.group(1) if m else None

def _extract_balanced_json_objects(text: str) -> List[str]:
    results, stack, start = [], 0, -1
    in_str, escape = False, False
    for i, ch in enumerate(text):
        if in_str:
            if escape: escape = False
            elif ch == '\\': escape = True
            elif ch == '"': in_str = False
        else:
            if ch == '"': in_str = True
            elif ch == '{':
                if stack == 0: start = i
                stack += 1
            elif ch == '}':
                if stack > 0:
                    stack -= 1
                    if stack == 0 and start != -1:
                        results.append(text[start:i+1])
                        start = -1
    return results

def _repair_python_syntax(code: str) -> str:
    import ast
    if not code or not code.strip(): return code
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        pass
        
    for q in ['"', "'"]:
        if code.rstrip().endswith(q):
            try:
                candidate = code.rstrip()[:-1]
                ast.parse(candidate)
                return candidate
            except SyntaxError: pass
            
    return code

def _smart_unescape_code(code: str) -> str:
    if '\\n' not in code: return code
    if '\n' in code: return code # Mixed state, preserve
    
    # Placeholder strategy for preserving escaped newlines in strings
    ph = '\x00N\x00'
    parts = []
    i, length = 0, len(code)
    in_str, str_char = False, None
    
    while i < length:
        if i+1 < length and code[i] == '\\':
            nxt = code[i+1]
            if in_str:
                if nxt == 'n':
                    parts.append(ph)
                    i += 2
                    continue
                elif nxt in ('"', "'", '\\'):
                    parts.append(code[i:i+2])
                    i += 2
                    continue
        
        if not in_str:
            if i+2 < length and code[i:i+3] in ('"""', "'''"):
                in_str, str_char = True, code[i:i+3]
                parts.append(code[i:i+3])
                i += 3
                continue
            elif code[i] in ('"', "'"):
                in_str, str_char = True, code[i]
                parts.append(code[i])
                i += 1
                continue
        else:
            if len(str_char) == 3:
                if i+2 < length and code[i:i+3] == str_char:
                    in_str = False
                    parts.append(code[i:i+3])
                    i += 3
                    continue
            elif code[i] == str_char:
                in_str = False
                parts.append(code[i])
                i += 1
                continue
                
        parts.append(code[i])
        i += 1
        
    res = "".join(parts)
    res = res.replace('\\r\\n', '\r\n').replace('\\n', '\n').replace('\\t', '\t')
    return res.replace(ph, '\\n')

def _unescape_code_newlines(obj: Any) -> Any:
    if isinstance(obj, BaseModel):
        for f in obj.model_fields:
            val = getattr(obj, f)
            if isinstance(val, str) and ("def " in val or "import " in val):
                processed = _repair_python_syntax(_smart_unescape_code(val))
                if processed != val: setattr(obj, f, processed)
            elif isinstance(val, (dict, list, BaseModel)):
                _unescape_code_newlines(val)
        return obj
    elif isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str) and ("def " in v or "import " in v):
                obj[k] = _repair_python_syntax(_smart_unescape_code(v))
            elif isinstance(v, (dict, list)):
                _unescape_code_newlines(v)
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            if isinstance(v, str) and ("def " in v or "import " in v):
                obj[i] = _repair_python_syntax(_smart_unescape_code(v))
            elif isinstance(v, (dict, list, BaseModel)):
                _unescape_code_newlines(v)
    return obj

def _has_invalid_python_code(obj: Any) -> bool:
    import ast
    if isinstance(obj, str):
        # Skip prose fields
        if any(x in obj.lower() for x in ('reasoning', 'explanation', 'analysis')): return False
        if len(obj) > 10 and ('def ' in obj or 'import ' in obj):
            try:
                ast.parse(obj)
            except SyntaxError:
                return True
    elif isinstance(obj, BaseModel):
        for f in obj.model_fields:
            if _has_invalid_python_code(getattr(obj, f)): return True
    elif isinstance(obj, dict):
        for v in obj.values():
            if _has_invalid_python_code(v): return True
    elif isinstance(obj, list):
        for v in obj:
            if _has_invalid_python_code(v): return True
    return False

def _is_malformed_json(s: str) -> bool:
    if not isinstance(s, str): return False
    s = s.strip()
    if not s.startswith('{'): return False
    # Check for excessive trailing newlines often seen in truncated JSON
    trailing_nl = 0
    temp = s
    while temp.endswith('\\n'):
        trailing_nl += 1
        temp = temp[:-2]
    return trailing_nl > 50 or (s.endswith('\\') and not s.endswith('\\\\'))

# --- Main Invocation Function ---
def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = 0.5,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    time: float = 0.25,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    
    set_verbose_logging(verbose)
    console = Console()

    # Cloud Check
    if use_cloud is None:
        force_local = os.getenv("PDD_FORCE_LOCAL", "").lower() in ("1", "true", "yes")
        if not force_local:
            try:
                from pdd.core.cloud import CloudConfig
                use_cloud = CloudConfig.is_cloud_enabled()
            except ImportError:
                use_cloud = False
    
    if use_cloud:
        try:
            return _llm_invoke_cloud(prompt, input_json, strength, temperature, verbose, 
                                   output_pydantic, output_schema, time, use_batch_mode, messages, language)
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed ({e}), falling back local...[/yellow]")
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as e:
            console.print(f"[yellow]Cloud error ({e}), falling back local...[/yellow]")

    # Input Validation
    if messages:
        fmt_msgs = messages
    elif prompt and input_json is not None:
        fmt_msgs = _format_messages(prompt, input_json, use_batch_mode)
    else:
        raise ValueError("Either 'messages' or both 'prompt' and 'input_json' must be provided.")

    if time is None: time = 0.0
    if not (0.0 <= strength <= 1.0): raise ValueError("Strength must be 0-1")
    
    # Model Selection
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)
    _set_model_rate_map(model_df)
    candidates = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    
    if verbose:
        logger.info(f"Candidates: {[c['model'] for c in candidates]}")

    last_error = None
    new_keys = {}
    
    for model in candidates:
        model_name = model['model']
        provider = model.get('provider', '').lower()
        api_key_name = model.get('api_key')
        
        # API Key
        if not _ensure_api_key(model, new_keys, verbose):
            continue
            
        # Prep Args
        llm_args = {
            "model": model_name,
            "messages": fmt_msgs,
            "temperature": temperature,
            "num_retries": 2
        }
        
        # Auth override
        if provider == 'vertex_ai' or model_name.startswith('vertex_ai/'):
            if api_key_name == 'VERTEX_CREDENTIALS':
                p = os.getenv('VERTEX_CREDENTIALS')
                if p: 
                    try: 
                        with open(p) as f: llm_args['vertex_credentials'] = json.dumps(json.load(f))
                    except Exception: pass
                llm_args['vertex_project'] = os.getenv('VERTEX_PROJECT')
                llm_args['vertex_location'] = model.get('location') or os.getenv('VERTEX_LOCATION')
        elif api_key_name:
            k = os.getenv(api_key_name)
            if k: llm_args['api_key'] = _sanitize_api_key(k)
            
        if model.get('base_url'): llm_args['base_url'] = model['base_url']
        
        # LM Studio / Groq specifics
        is_lm_studio = 'lm_studio' in provider or 'lm_studio' in model_name
        if is_lm_studio:
            if not llm_args.get('base_url'): 
                llm_args['base_url'] = os.getenv('LM_STUDIO_API_BASE', 'http://localhost:1234/v1')
            if not llm_args.get('api_key'): llm_args['api_key'] = 'lm-studio'
            
        is_groq = 'groq' in provider
        
        # Structured Output
        is_pydantic = output_pydantic is not None
        if output_pydantic or output_schema:
            if model.get('structured_output'):
                if is_pydantic:
                    s = output_pydantic.model_json_schema()
                    _ensure_all_properties_required(s)
                    _add_additional_properties_false(s)
                    rf = {"type": "json_schema", "json_schema": {"name": output_pydantic.__name__, "strict": True, "schema": s}}
                else:
                    s = output_schema.copy()
                    _ensure_all_properties_required(s)
                    _add_additional_properties_false(s)
                    rf = {"type": "json_schema", "json_schema": {"name": "resp", "strict": False, "schema": s}}
                
                if is_lm_studio:
                    llm_args['extra_body'] = {"response_format": rf}
                elif is_groq:
                    llm_args['response_format'] = {"type": "json_object"}
                    inst = f"Respond with valid JSON matching:\n```json\n{json.dumps(s)}\n```"
                    if isinstance(llm_args['messages'], list) and isinstance(llm_args['messages'][0], dict):
                        llm_args['messages'].insert(0, {"role": "system", "content": inst})
                else:
                    llm_args['response_format'] = rf

        # Reasoning
        rtype = model.get('reasoning_type', 'none')
        rmax = model.get('max_reasoning_tokens', 0)
        if time > 0:
            if rtype == 'budget' and rmax > 0:
                b = int(time * rmax)
                if provider == 'anthropic':
                    llm_args['thinking'] = {"type": "enabled", "budget_tokens": b}
                    llm_args['temperature'] = 1.0
            elif rtype == 'effort':
                eff = "high" if time > 0.7 else ("medium" if time > 0.3 else "low")
                if 'gpt-5' in model_name.lower():
                    llm_args['reasoning'] = {"effort": eff, "summary": "auto"}
                else:
                    llm_args['reasoning_effort'] = eff

        # Invocation
        try:
            is_gpt5 = 'gpt-5' in model_name.lower() and provider == 'openai'
            if is_gpt5 and not use_batch_mode:
                if 'temperature' in llm_args: del llm_args['temperature']
                
                text_block = {"format": {"type": "text"}}
                if 'response_format' in llm_args:
                    rf = llm_args.pop('response_format')
                    if rf['type'] == 'json_schema':
                        text_block = {"format": rf}
                
                resp_kwargs = {
                    "model": model_name,
                    "input": str(fmt_msgs),
                    "text": text_block
                }
                if 'reasoning' in llm_args: resp_kwargs['reasoning'] = llm_args['reasoning']
                
                # Call Responses API
                resp = litellm.responses(**resp_kwargs)
                
            if use_batch_mode:
                response = litellm.batch_completion(**llm_args)
            else:
                response = litellm.completion(**llm_args, timeout=120)
                
            # Process Response
            res_list = response if use_batch_mode else [response]
            results = []
            thinkings = []
            
            for i, r in enumerate(res_list):
                # Thinking
                th = None
                try: 
                    if hasattr(r, '_hidden_params'): th = r._hidden_params.get('thinking')
                    if not th: th = r.choices[0].message.get('reasoning_content')
                except: pass
                thinkings.append(th)
                
                content = r.choices[0].message.content
                
                # None/Malformed Retry Logic
                retry_needed = False
                if content is None: retry_needed = True
                if isinstance(content, str) and _is_malformed_json(content): retry_needed = True
                
                if retry_needed and not use_batch_mode:
                    # Retry logic (cache bypass)
                    llm_args['messages'] = _format_messages(prompt + " ", input_json, False)
                    orig_cache = litellm.cache
                    litellm.cache = None
                    try:
                        retry_r = litellm.completion(**llm_args)
                        content = retry_r.choices[0].message.content
                    finally:
                        litellm.cache = orig_cache

                # Parsing
                parsed = content
                if output_pydantic or output_schema:
                    try:
                        if isinstance(content, str):
                            # Try fenced
                            cand = _extract_fenced_json_block(content)
                            if not cand: 
                                objs = _extract_balanced_json_objects(content)
                                cand = objs[0] if objs else content
                            
                            # Clean fences
                            cand = cand.strip().replace("```json", "").replace("```", "").strip()
                            
                            # Repair if truncated
                            if not cand.endswith("}") and not cand.endswith("]"):
                                cand += "}" # simplified repair
                                
                            if output_pydantic:
                                parsed = output_pydantic.model_validate_json(cand)
                            else:
                                parsed = json.loads(cand)
                        elif isinstance(content, dict):
                            if output_pydantic: parsed = output_pydantic.model_validate(content)
                            else: parsed = content
                            
                        _unescape_code_newlines(parsed)
                        
                        # Python Syntax Retry
                        if (language is None or language == 'python') and _has_invalid_python_code(parsed) and not use_batch_mode:
                             pass
                             
                    except Exception as e:
                        raise SchemaValidationError(f"Parse failed: {e}", raw_response=content)
                
                results.append(parsed)
                
            return {
                'result': results if use_batch_mode else results[0],
                'cost': _LAST_CALLBACK_DATA.get('cost', 0),
                'model_name': model_name,
                'thinking_output': thinkings if use_batch_mode else thinkings[0]
            }

        except (openai.AuthenticationError, openai.RateLimitError) as e:
            if 'thinking' in llm_args and 'temperature' in str(e):
                continue 
            last_error = e
            continue
        except SchemaValidationError:
            last_error = "Schema validation failed"
            continue
        except Exception as e:
            last_error = e
            continue
            
    raise RuntimeError(f"All candidates failed. Last error: {last_error}")