from __future__ import annotations

import os
import json
import logging
import time as time_module
import warnings
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple

import pandas as pd
import requests
import litellm
from litellm.caching.caching import Cache
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

import openai  # For exception mapping

# Relative import for path resolution
from .path_resolution import get_default_resolver

# --- Configure Standard Python Logging ---
logger = logging.getLogger("pdd.llm_invoke")

# Environment variable to control log level
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"

# Set default level based on environment
if PRODUCTION_MODE:
    logger.setLevel(logging.WARNING)
else:
    logger.setLevel(getattr(logging, PDD_LOG_LEVEL, logging.INFO))

# Configure LiteLLM logger separately
litellm_logger = logging.getLogger("litellm")
litellm_log_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING" if PRODUCTION_MODE else "INFO")
litellm_logger.setLevel(getattr(logging, litellm_log_level, logging.WARNING))

# Suppress LiteLLM debug messages and error info that includes "Give Feedback / Get Help"
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# Ensure LiteLLM drops provider-unsupported params instead of erroring
try:
    _drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_params_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

# Add a console handler if none exists
if not logger.handlers:
    console_handler = logging.StreamHandler()
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    
    if not litellm_logger.handlers:
        litellm_logger.addHandler(console_handler)

def setup_file_logging(log_file_path: Optional[str] = None) -> None:    """Configure rotating file handler for logging."""
    if not log_file_path:
        return
        
    try:
        from logging.handlers import RotatingFileHandler
        file_handler = RotatingFileHandler(
            log_file_path, maxBytes=10*1024*1024, backupCount=5
        )
        file_handler.setFormatter(logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        ))
        logger.addHandler(file_handler)
        litellm_logger.addHandler(file_handler)
        logger.info(f"File logging configured to: {log_file_path}")
    except Exception as e:
        logger.warning(f"Failed to set up file logging: {e}")

def set_verbose_logging(verbose: bool = False) -> None:    """Set verbose logging based on flag or environment variable."""
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
    """Raised when LLM response fails Pydantic/JSON schema validation to trigger model fallback."""
    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0):
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index

class CloudFallbackError(Exception):
    """Raised when cloud execution fails and should fall back to local."""
    pass

class CloudInvocationError(Exception):
    """Raised when cloud invocation fails with a non-recoverable error."""
    pass

class InsufficientCreditsError(Exception):
    """Raised when user has insufficient credits for cloud execution (402)."""
    pass

# --- Cloud Execution Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:    """Recursively ensure ALL properties are in the required array (OpenAI strict mode)."""
    if not isinstance(schema, dict):
        return schema

    if schema.get('type') == 'object' and 'properties' in schema:
        schema['required'] = list(schema['properties'].keys())
        for prop_schema in schema['properties'].values():
            _ensure_all_properties_required(prop_schema)

    if schema.get('type') == 'array' and 'items' in schema:
        _ensure_all_properties_required(schema['items'])

    for key in ('anyOf', 'oneOf', 'allOf'):
        if key in schema:
            for sub_schema in schema[key]:
                _ensure_all_properties_required(sub_schema)

    if '$defs' in schema:
        for def_schema in schema['$defs'].values():
            _ensure_all_properties_required(def_schema)

    return schema

def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:    """Recursively add additionalProperties: false to all object schemas (OpenAI strict mode)."""
    if not isinstance(schema, dict):
        return schema

    if schema.get('type') == 'object':
        schema['additionalProperties'] = False
        if 'properties' in schema:
            for prop_schema in schema['properties'].values():
                _add_additional_properties_false(prop_schema)

    if schema.get('type') == 'array' and 'items' in schema:
        _add_additional_properties_false(schema['items'])

    for key in ('anyOf', 'oneOf', 'allOf'):
        if key in schema:
            for sub_schema in schema[key]:
                _add_additional_properties_false(sub_schema)

    if '$defs' in schema:
        for def_schema in schema['$defs'].values():
            _add_additional_properties_false(def_schema)

    return schema

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:    """Convert Pydantic model to strict JSON Schema for cloud transport."""
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema['__pydantic_class_name__'] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:    """Validate result against Pydantic class."""
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    elif isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    elif isinstance(result, pydantic_class):
        return result
    raise ValueError(f"Cannot validate result type {type(result)} with Pydantic model")

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    strength: float,
    temperature: float,
    verbose: bool,
    output_pydantic: Optional[Type[BaseModel]],
    output_schema: Optional[Dict[str, Any]],
    time: float,
    use_batch_mode: bool,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]],
    language: Optional[str],
) -> Dict[str, Any]:    """Execute llm_invoke via cloud endpoint."""
    from pdd.core.cloud import CloudConfig
    
    CLOUD_TIMEOUT = 300
    jwt_token = CloudConfig.get_jwt_token(verbose=verbose)
    if not jwt_token:
        raise CloudFallbackError("Could not authenticate with cloud")

    payload: Dict[str, Any] = {
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "useBatchMode": use_batch_mode,
    }
    if language:
        payload["language"] = language
    if messages:
        payload["messages"] = messages
    else:
        payload["prompt"] = prompt
        payload["inputJson"] = input_json

    if output_pydantic:
        payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema:
        payload["outputSchema"] = output_schema

    headers = {
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/json"
    }
    cloud_url = CloudConfig.get_endpoint_url("llmInvoke")

    if verbose:
        logger.debug(f"Cloud request to: {cloud_url}")

    try:
        response = requests.post(cloud_url, json=payload, headers=headers, timeout=CLOUD_TIMEOUT)
        
        if response.status_code == 200:
            data = response.json()
            result = data.get("result")
            if output_pydantic and result:
                try:
                    result = _validate_with_pydantic(result, output_pydantic)
                except (ValidationError, ValueError) as e:
                    logger.warning(f"Cloud response validation failed: {e}")
            
            return {
                "result": result,
                "cost": data.get("totalCost", 0.0),
                "model_name": data.get("modelName", "cloud_model summertime"),
                "thinking_output": data.get("thinkingOutput"),
            }
        
        elif response.status_code == 402:
            raise InsufficientCreditsError(response.json().get("error", "Insufficient credits"))
        
        elif response.status_code in (401, 403):
            try:
                from pdd.auth_service import clear_jwt_cache
                clear_jwt_cache()
            except Exception:
                pass
            raise CloudFallbackError(f"Authentication expired ({response.status_code}).")
            
        elif response.status_code >= 500:
            raise CloudFallbackError(response.json().get("error", f"Server error {response.status_code}"))
        
        else:
            raise CloudInvocationError(response.json().get("error", f"HTTP {response.status_code}"))

    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud request failed: {e}")

# --- Environment & Path Helpers ---

def _is_wsl_environment() -> bool:
    try:
        if os.path.exists('/proc/version'):
            with open('/proc/version', 'r') as f:
                if 'microsoft' in f.read().lower(): return True
        return bool(os.getenv('WSL_DISTRO_NAME'))
    except Exception:
        return False

def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    try:
        current_dir = Path.cwd().resolve()
        for _ in range(max_levels):
            if any((current_dir / m).exists() for m in [".git", "pyproject.toml", "data", ".env"]):
                return current_dir
            if current_dir.parent == current_dir: break
            current_dir = current_dir.parent
    except Exception:
        pass
    return Path.cwd().resolve()

# --- Configuration & Startup ---

resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env

user_model_csv_path = Path.home() / ".pdd" / "llm_model.csv"
project_root_from_cwd = _detect_project_root_from_cwd()
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"

# Check if PDD_PATH points to package
try:
    _installed_pkg_root = Path(str(importlib.resources.files('pdd')))
except Exception:
    _installed_pkg_root = None

def _is_env_path_package_dir(env_path: Path) -> bool:
    try:
        if _installed_pkg_root is None: return False
        return str(env_path.resolve()).startswith(str(_installed_pkg_root.resolve()))
    except Exception:
        return False

# Determine ENV_PATH
if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
else:
    ENV_PATH = PROJECT_ROOT / ".env"

if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

# Determine CSV Path
if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH = user_model_csv_path
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
else:
    LLM_MODEL_CSV_PATH = None  # Will trigger package default

DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", None)
LLM_CALL_TIMEOUT = 120

# --- LiteLLM Caching ---
GCS_BUCKET = os.getenv("GCS_BUCKET_NAME")
if GCS_BUCKET and os.getenv("GCS_HMAC_ACCESS_KEY_ID") and os.getenv("GCS_HMAC_SECRET_ACCESS_KEY"):
    try:
        # Swap vars for S3 compat
        orig_id = os.environ.get('AWS_ACCESS_KEY_ID')
        orig_secret = os.environ.get('AWS_SECRET_ACCESS_KEY')
        os.environ['AWS_ACCESS_KEY_ID'] = os.getenv("GCS_HMAC_ACCESS_KEY_ID", "").strip()
        os.environ['AWS_SECRET_ACCESS_KEY'] = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY", "").strip()
        
        configured_cache = Cache(
            type="s3", 
            s3_bucket_name=GCS_BUCKET, 
            s3_endpoint_url="https://storage.googleapis.com",
            s3_region_name=os.getenv("GCS_REGION_NAME", "auto")
        )
        litellm.cache = configured_cache
        
        # Restore
        if orig_id: os.environ['AWS_ACCESS_KEY_ID'] = orig_id
        else: del os.environ['AWS_ACCESS_KEY_ID']
        if orig_secret: os.environ['AWS_SECRET_ACCESS_KEY'] = orig_secret
        else: del os.environ['AWS_SECRET_ACCESS_KEY']
    except Exception:
        litellm.cache = None
else:
    try:
        sqlite_path = PROJECT_ROOT / "litellm_cache.sqlite"
        litellm.cache = Cache(type="disk", disk_cache_dir=str(sqlite_path))
    except Exception:
        litellm.cache = None

if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    litellm.cache = None
configured_cache = litellm.cache

# --- Callback ---
_LAST_CALLBACK_DATA = {"input_tokens": 0, "output_tokens": 0, "cost": 0.0}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, 'usage', None)
    _LAST_CALLBACK_DATA["input_tokens"] = getattr(usage, 'prompt_tokens', 0)
    _LAST_CALLBACK_DATA["output_tokens"] = getattr(usage, 'completion_tokens', 0)
    
    try:
        cost = litellm.completion_cost(completion_response=completion_response)
    except Exception:
        model = kwargs.get("model")
        rates = _MODEL_RATE_MAP.get(str(model))
        if rates:
            in_t = _LAST_CALLBACK_DATA["input_tokens"]
            out_t = _LAST_CALLBACK_DATA["output_tokens"]
            cost = (in_t * rates[0] + out_t * rates[1]) / 1_000_000.0
        else:
            cost = 0.0
    _LAST_CALLBACK_DATA["cost"] = cost if cost else 0.0

litellm.success_callback = [_litellm_success_callback]

# --- Core Logic ---

def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    try:
        if csv_path and csv_path.exists():
            df = pd.read_csv(csv_path)
        else:
            csv_str = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()
            from io import StringIO
            df = pd.read_csv(StringIO(csv_str))
        
        for col in ['input', 'output', 'coding_arena_elo']:
            df[col] = pd.to_numeric(df[col], errors='coerce').fillna(0.0)
        
        df['max_reasoning_tokens'] = pd.to_numeric(df['max_reasoning_tokens'], errors='coerce').fillna(0).astype(int)
        df['avg_cost'] = (df['input'] + df['output']) / 2
        df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
        df['reasoning_type'] = df['reasoning_type'].fillna('none').astype(str).str.lower()
        df['api_key'] = df['api_key'].fillna('').astype(str)
        return df
    except Exception as e:
        raise RuntimeError(f"Failed to load model CSV: {e}")

def _set_model_rate_map(df: pd.DataFrame) -> None:
    global _MODEL_RATE_MAP
    for _, row in df.iterrows():
        _MODEL_RATE_MAP[str(row['model'])] = (float(row['input']), float(row['output']))

def _select_model_candidates(strength: float, base_model_name: Optional[str], df: pd.DataFrame) -> List[Dict]:
    available = df[df['api_key'].notna()].copy()
    if available.empty:
        raise ValueError("No valid models found in CSV")
    
    # Handle base model
    if base_model_name and base_model_name in available['model'].values:
        base_model = available[available['model'] == base_model_name].iloc[0]
    else:
        base_model = available.iloc[0]
    
    target_cost, target_elo = None, None
    
    if strength < 0.5:
        base_cost = base_model['avg_cost']
        min_cost = available['avg_cost'].min()
        target_cost = min_cost + (strength / 0.5) * (base_cost - min_cost)
        available['metric'] = abs(available['avg_cost'] - target_cost)
    elif strength > 0.5:
        base_elo = base_model['coding_arena_elo']
        max_elo = available['coding_arena_elo'].max()
        target_elo = base_elo + ((strength - 0.5) / 0.5) * (max_elo - base_elo)
        available['metric'] = abs(available['coding_arena_elo'] - target_elo)
    else:
        # Strength 0.5: Sort by ELO desc, ensuring base is first
        available['metric'] = -available['coding_arena_elo']
        
    candidates = available.sort_values('metric').to_dict('records')
    
    # Ensure base model is first for 0.5
    if strength == 0.5:
        base_name = str(base_model['model'])
        candidates.sort(key=lambda x: 0 if x['model'] == base_name else 1)
        
    return candidates

def _sanitize_api_key(key: str) -> str:
    if not key: return key
    s = key.strip()
    return ''.join(c for c in s if ord(c) >= 32)

def _save_key_to_env_file(key: str, val: str, path: Path) -> None:
    lines = []
    if path.exists():
        with open(path, 'r') as f: lines = f.readlines()
    
    new_lines = []
    replaced = False
    for line in lines:
        if line.strip().startswith(f"{key}=") or line.strip().startswith(f"{key} ="):
            new_lines.append(f'{key}="{val}"\n')
            replaced = True
        elif not line.strip().startswith(f"# {key}"):
            new_lines.append(line)
            
    if not replaced:
        if new_lines and not new_lines[-1].endswith('\n'): new_lines.append('\n')
        new_lines.append(f'{key}="{val}"\n')
        
    with open(path, 'w') as f: f.writelines(new_lines)

def _ensure_api_key(model_info: Dict, newly_acquired: Dict, verbose: bool) -> bool:
    key_name = model_info.get('api_key')
    if not key_name or key_name == "EXISTING_KEY": return True
    
    val = os.getenv(key_name)
    if val: return True
    
    if os.getenv("PDD_FORCE"): return False
    
    try:
        val = input(f"Enter API key for {key_name}: ").strip()
        if not val: return False
        
        val = _sanitize_api_key(val)
        os.environ[key_name] = val
        newly_acquired[key_name] = True
        _save_key_to_env_file(key_name, val, ENV_PATH)
        logger.warning(f"Key {key_name} saved to {ENV_PATH}")
        return True
    except (EOFError, KeyboardInterrupt):
        return False

def _format_messages(prompt: str, input_json: Union[Dict, List], batch: bool) -> Union[List[Dict], List[List[Dict]]]:
    if batch:
        if not isinstance(input_json, list): raise ValueError("Batch mode requires list input")
        return [[{"role": "user", "content": prompt.format(**item)}] for item in input_json]
    else:
        if not isinstance(input_json, dict): raise ValueError("Single mode requires dict input")
        return [{"role": "user", "content": prompt.format(**input_json)}]

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
            try: return code.rstrip()[:-1]
            except: pass
    return code

def _smart_unescape_code(code: str) -> str:
    if '\\n' not in code: return code
    if '\n' in code: return code # Mixed state, unsafe
    
    # Placeholder strategy for strings
    placeholder = '\x00NL\x00'
    parts = []
    i = 0
    in_str = False
    quote = None
    
    while i < len(code):
        if not in_str:
            if code[i] in ('"', "'"):
                in_str = True
                quote = code[i]
                parts.append(code[i])
            elif code[i:i+2] == '\\n':
                parts.append('\n')
                i += 1
            else:
                parts.append(code[i])
        else:
            if code[i] == '\\' and i+1 < len(code):
                if code[i+1] == 'n': parts.append(placeholder)
                else: parts.append(code[i:i+2])
                i += 1
            elif code[i] == quote:
                in_str = False
                parts.append(code[i])
            else:
                parts.append(code[i])
        i += 1
    
    return ''.join(parts).replace(placeholder, '\\n')

def _is_malformed_json_response(s: str) -> bool:
    if not isinstance(s, str): return False
    s = s.strip()
    if not s.startswith('{') or s.endswith('}'): return True
    return s.count('\\n') > 100 # High threshold heuristic

def _extract_result(content: str) -> str:
    import re
    # Fenced JSON
    m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", content, re.IGNORECASE)
    if m: return m.group(1)
    
    # Balanced braces (simple)
    if content.strip().startswith('{') and content.strip().endswith('}'):
        return content.strip()
        
    return content # Fallback

def _has_invalid_python_code(obj: Any) -> bool:
    import ast
    if isinstance(obj, str):
        if "def " in obj or "import " in obj:
            try: ast.parse(obj); return False
            except: return True
    elif isinstance(obj, dict):
        return any(_has_invalid_python_code(v) for k, v in obj.items() if k not in ["reasoning", "explanation"])
    elif isinstance(obj, list):
        return any(_has_invalid_python_code(v) for v in obj)
    return False

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
    
    set_verbose_logging(verbose)
    
    # 0. Cloud Execution
    if use_cloud is None:
        force_local = os.getenv("PDD_FORCE_LOCAL", "").lower() in ("1", "true")
        if force_local: use_cloud = False
        else:
            try:
                from pdd.core.cloud import CloudConfig
                use_cloud = CloudConfig.is_cloud_enabled()
            except ImportError: use_cloud = False

    if use_cloud:
        console = Console()
        try:
            return _llm_invoke_cloud(prompt, input_json, strength, temperature, verbose, 
                                   output_pydantic, output_schema, time, use_batch_mode, messages, language)
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed ({e}), using local...[/yellow]")
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as e:
            console.print(f"[yellow]Cloud error ({e}), using local...[/yellow]")

    # 1. Validation & Setup
    if messages:
        formatted = messages
    elif prompt and input_json is not None:
        formatted = _format_messages(prompt, input_json, use_batch_mode)
    else:
        raise ValueError("Must provide messages or prompt+input_json")

    time = time or 0.0
    
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)
    _set_model_rate_map(model_df) # For fallback cost calc
    candidates = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    
    newly_acquired: Dict[str, bool] = {}
    last_error = None

    for model_info in candidates:
        model = model_info['model']
        provider = model_info.get('provider', '').lower()
        api_key_name = model_info.get('api_key')
        
        # 2. API Key
        retry_model = True
        while retry_model:
            retry_model = False
            if not _ensure_api_key(model_info, newly_acquired, verbose): break
            
            # 3. Parameters
            kwargs = {
                "model": model,
                "messages": formatted,
                "temperature": temperature,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT
            }
            
            # Vertex AI overrides
            if provider == 'google' and api_key_name == 'VERTEX_CREDENTIALS':
                creds = os.getenv("VERTEX_CREDENTIALS")
                if creds:
                    try:
                        with open(creds) as f: kwargs["vertex_credentials"] = json.dumps(json.load(f))
                    except Exception: pass
                kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
                kwargs["vertex_location"] = model_info.get('location') or os.getenv("VERTEX_LOCATION")
            elif api_key_name and api_key_name != "EXISTING_KEY":
                kwargs["api_key"] = os.getenv(api_key_name)
                
            # Base URL
            if model_info.get('base_url'): kwargs["base_url"] = model_info['base_url']
            if 'lm_studio' in model.lower() or provider == 'lm_studio':
                kwargs["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                if not kwargs.get("api_key"): kwargs["api_key"] = "lm-studio"

            # Reasoning
            reasoning_type = model_info.get('reasoning_type', 'none')
            max_tokens = int(model_info.get('max_reasoning_tokens', 0))
            if time > 0:
                if reasoning_type == 'budget' and max_tokens > 0:
                    budget = int(time * max_tokens)
                    if provider == 'anthropic':
                        kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                        kwargs["temperature"] = 1.0 # Forced
                elif reasoning_type == 'effort':
                    effort = "high" if time > 0.7 else ("medium" if time > 0.3 else "low")
                    if provider == 'openai' and 'gpt-5' in model.lower():
                        kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
                    else:
                        kwargs["reasoning_effort"] = effort

            # Structured Output
            if (output_pydantic or output_schema) and model_info.get('structured_output'):
                schema = output_pydantic.model_json_schema() if output_pydantic else output_schema
                _ensure_all_properties_required(schema)
                _add_additional_properties_false(schema)
                
                resp_fmt = {
                    "type": "json_schema", 
                    "json_schema": {
                        "name": output_pydantic.__name__ if output_pydantic else "response",
                        "strict": True,
                        "schema": schema
                    }
                }
                
                if 'lm_studio' in model.lower():
                    kwargs["extra_body"] = {"response_format": resp_fmt}
                elif 'groq' in model.lower():
                    kwargs["response_format"] = {"type": "json_object"}
                    # Inject prompt
                    instr = f"\nJSON Schema:\n{json.dumps(schema)}"
                    if kwargs["messages"][0]["role"] == "system": kwargs["messages"][0]["content"] += instr
                    else: kwargs["messages"].insert(0, {"role": "system", "content": instr})
                else:
                    kwargs["response_format"] = resp_fmt

            # 4. Invoke
            try:
                if provider == 'openai' and 'gpt-5' in model.lower() and not use_batch_mode:
                    # Specialized Responses API
                    if "temperature" in kwargs: del kwargs["temperature"]
                    text_conf = {"format": {"type": "json_schema", "json_schema": resp_fmt["json_schema"]}} if (output_pydantic or output_schema) else {"format": {"type": "text"}}
                    resp = litellm.responses(model=model, input=str(formatted), text=text_conf, **{k:v for k,v in kwargs.items() if k not in ['messages', 'response_format', 'temperature']})
                    # Transform to standard obj for processing
                    content = resp.output[0].content[0].text
                    raw_result = content
                    thinking = None
                else:
                    func = litellm.batch_completion if use_batch_mode else litellm.completion
                    resp = func(**kwargs)
                    if use_batch_mode: 
                        raw_result = [r.choices[0].message.content for r in resp]
                        thinking = [r._hidden_params.get('thinking') or r.choices[0].message.get('reasoning_content') for r in resp]
                    else:
                        raw_result = resp.choices[0].message.content
                        thinking = resp._hidden_params.get('thinking') or resp.choices[0].message.get('reasoning_content')

                # 5. Process & Repair
                final_res = []
                iter_res = raw_result if use_batch_mode else [raw_result]
                
                for i, txt in enumerate(iter_res):
                    # Handle Malformed/None
                    if txt is None or (isinstance(txt, str) and _is_malformed_json_response(txt)):
                        # Simple retry logic (modify prompt to bypass cache)
                        if not use_batch_mode:
                            litellm.cache = None # Temporary disable
                            kwargs["messages"] = _format_messages(prompt + " ", input_json, False)
                            retry_resp = litellm.completion(**kwargs)
                            txt = retry_resp.choices[0].message.content
                            litellm.cache = configured_cache # Restore

                    parsed = txt
                    if output_pydantic or output_schema:
                        try:
                            # Try parsing
                            candidates_list = [_extract_result(txt)]
                            parsed_obj = None
                            for cand in candidates_list:
                                try:
                                    if output_pydantic: parsed_obj = _validate_with_pydantic(cand, output_pydantic)
                                    else: parsed_obj = json.loads(cand)
                                    break
                                except: pass
                            
                            if parsed_obj is None: raise SchemaValidationError("Failed to parse JSON")
                            parsed = parsed_obj
                        except SchemaValidationError:
                            raise # Trigger model fallback
                    
                    # Code Repair
                    if language in [None, "python"]:
                        # Deep validation of code strings
                        if isinstance(parsed, (BaseModel, dict)):
                            # Simplified: check for syntax errors
                            if _has_invalid_python_code(parsed):
                                # Logic to retry would go here
                                pass 
                        elif isinstance(parsed, str):
                            parsed = _smart_unescape_code(parsed)
                            parsed = _repair_python_syntax(parsed)

                    final_res.append(parsed)

                return {
                    "result": final_res if use_batch_mode else final_res[0],
                    "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                    "model_name": model,
                    "thinking_output": thinking
                }

            except (openai.AuthenticationError, SchemaValidationError) as e:
                logger.warning(f"Error with model {model}: {e}")
                if isinstance(e, openai.AuthenticationError) and newly_acquired.get(api_key_name):
                    retry_model = True # Retry same model if key was just entered
                    if api_key_name in os.environ: del os.environ[api_key_name]
                    continue
                last_error = e
                break # Try next model
            except Exception as e:
                logger.warning(f"Invocation error {model}: {e}")
                if "temperature" in str(e).lower() and "thinking" in str(e).lower():
                    kwargs["temperature"] = 1.0 # Auto-fix
                last_error = e
                break

    raise RuntimeError(f"All models failed. Last error: {last_error}")