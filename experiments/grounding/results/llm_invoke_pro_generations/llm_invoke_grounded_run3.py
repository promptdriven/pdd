"""
llm_invoke.py

Core module for invoking Large Language Models (LLMs) via LiteLLM with automatic
fallback, API key management, cloud execution support, and structured output validation.
"""

from __future__ import annotations

import os
import json
import time as time_module
import logging
import warnings
import importlib.resources
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple, Set

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

# Import openai for exception handling mappings
import openai

# Internal imports
try:
    from pdd.path_resolution import get_default_resolver
except ImportError:
    # Fallback for standalone execution if path_resolution is missing
    class MockResolver:
        def resolve_project_root(self): return Path.cwd()
        @property
        def pdd_path_env(self): return None
    def get_default_resolver(): return MockResolver()

# --- Logging Configuration ---
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

# Determine logging levels from environment
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")
PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING" if PRODUCTION_MODE else "INFO")

# Configure logger levels
if PRODUCTION_MODE:
    logger.setLevel(logging.WARNING)
else:
    logger.setLevel(getattr(logging, PDD_LOG_LEVEL.upper(), logging.INFO))

litellm_logger.setLevel(getattr(logging, LITELLM_LOG_LEVEL.upper(), logging.WARNING))

# Suppress noisy LiteLLM debug output
try:
    litellm.set_verbose = False
    litellm.suppress_debug_info = True
except Exception:
    pass

# Drop unsupported params to prevent crashes on generic calls (e.g. reasoning_effort on gpt-5)
try:
    _drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_params_env).lower() in ("1", "true", "yes", "on")
except Exception:
    litellm.drop_params = True

# Initialize console handler if needed
if not logger.handlers:
    console_handler = logging.StreamHandler()
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    if not litellm_logger.handlers:
        litellm_logger.addHandler(console_handler)


def setup_file_logging(log_file_path: Optional[str] = None) -> None:
    """Configure rotating file handler for logging."""
    if not log_file_path:
        return
    try:
        from logging.handlers import RotatingFileHandler
        file_handler = RotatingFileHandler(
            log_file_path, maxBytes=10 * 1024 * 1024, backupCount=5
        )
        file_handler.setFormatter(logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        ))
        logger.addHandler(file_handler)
        litellm_logger.addHandler(file_handler)
        logger.info(f"File logging configured to: {log_file_path}")
    except Exception as e:
        logger.warning(f"Failed to set up file logging: {e}")


def set_verbose_logging(verbose: bool = False) -> None:
    """Toggle verbose DEBUG logging."""
    want_verbose = bool(verbose) or os.getenv("PDD_VERBOSE_LOGGING") == "1"
    
    if want_verbose:
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)
    else:
        if PRODUCTION_MODE:
            logger.setLevel(logging.WARNING)
        else:
            logger.setLevel(getattr(logging, PDD_LOG_LEVEL.upper(), logging.INFO))
        litellm_logger.setLevel(getattr(logging, LITELLM_LOG_LEVEL.upper(), logging.WARNING))

    # Toggle internal LiteLLM verbosity
    try:
        if hasattr(litellm, "set_verbose"):
            litellm.set_verbose = want_verbose
        if hasattr(litellm, "suppress_debug_info"):
            litellm.suppress_debug_info = not want_verbose
    except Exception:
        pass


# --- Custom Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM response fails Pydantic/JSON schema validation, triggering fallback."""
    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0):
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index


class CloudFallbackError(Exception):
    """Raised when cloud execution fails (network/auth) and should fall back to local."""
    pass


class CloudInvocationError(Exception):
    """Raised when cloud invocation fails with a non-recoverable error (validation)."""
    pass


class InsufficientCreditsError(Exception):
    """Raised when user has insufficient credits (402 Payment Required)."""
    pass


# --- Constants & Path Resolution ---

LLM_CALL_TIMEOUT = 120

# Resolve paths
resolver = get_default_resolver()
PROJECT_ROOT = resolver.resolve_project_root()
PROJECT_ROOT_FROM_ENV = resolver.pdd_path_env is not None and PROJECT_ROOT == resolver.pdd_path_env


def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    """Find project root from CWD via markers (.git, .env, etc)."""
    try:
        current_dir = Path.cwd().resolve()
        for _ in range(max_levels):
            if any((current_dir / marker).exists() for marker in [".git", "pyproject.toml", ".env", "data"]):
                return current_dir
            parent = current_dir.parent
            if parent == current_dir:
                break
            current_dir = parent
    except Exception:
        pass
    return Path.cwd().resolve()


project_root_from_cwd = _detect_project_root_from_cwd()

# Check if we are running from installed package
try:
    _installed_pkg_root = importlib.resources.files('pdd')
    _installed_pkg_root_path = Path(str(_installed_pkg_root))
except Exception:
    _installed_pkg_root_path = None


def _is_env_path_package_dir(env_path: Path) -> bool:
    try:
        if _installed_pkg_root_path is None:
            return False
        return env_path.resolve() == _installed_pkg_root_path.resolve() or \
               str(env_path.resolve()).startswith(str(_installed_pkg_root_path.resolve()))
    except Exception:
        return False


# Determine .env path
if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
else:
    ENV_PATH = PROJECT_ROOT / ".env"

if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)

# Determine CSV path
user_model_csv_path = Path.home() / ".pdd" / "llm_model.csv"
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH = user_model_csv_path
elif PROJECT_ROOT_FROM_ENV and project_csv_from_env.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_env
elif project_csv_from_cwd.is_file():
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
else:
    LLM_MODEL_CSV_PATH = None  # Fallback to package data

DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", None)


# --- LiteLLM Configuration (Cache & Callback) ---

# GCS/S3 Cache support
GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID", "").strip()
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY", "").strip()

cache_configured = False
configured_cache = None

if GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    try:
        from litellm.caching import Cache
        # Temp swap AWS env vars for LiteLLM's S3 backend to use GCS
        old_aws_id = os.environ.get('AWS_ACCESS_KEY_ID')
        old_aws_secret = os.environ.get('AWS_SECRET_ACCESS_KEY')
        os.environ['AWS_ACCESS_KEY_ID'] = GCS_HMAC_ACCESS_KEY_ID
        os.environ['AWS_SECRET_ACCESS_KEY'] = GCS_HMAC_SECRET_ACCESS_KEY
        
        configured_cache = Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_endpoint_url="https://storage.googleapis.com",
            s3_region_name=os.getenv("GCS_REGION_NAME", "auto")
        )
        litellm.cache = configured_cache
        cache_configured = True
        
        # Restore
        if old_aws_id: os.environ['AWS_ACCESS_KEY_ID'] = old_aws_id
        else: os.environ.pop('AWS_ACCESS_KEY_ID', None)
        if old_aws_secret: os.environ['AWS_SECRET_ACCESS_KEY'] = old_aws_secret
        else: os.environ.pop('AWS_SECRET_ACCESS_KEY', None)
    except Exception as e:
        logger.warning(f"Failed to configure GCS cache: {e}")

if not cache_configured and os.getenv("LITELLM_CACHE_DISABLE") != "1":
    try:
        from litellm.caching import Cache
        sqlite_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_path))
        litellm.cache = configured_cache
        cache_configured = True
    except Exception:
        litellm.cache = None

# Cost Tracking
_LAST_CALLBACK_DATA = {"input_tokens": 0, "output_tokens": 0, "cost": 0.0, "finish_reason": None}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

def _litellm_success_callback(kwargs, completion_response, start_time, end_time):
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(completion_response, 'usage', None)
        in_tok = getattr(usage, 'prompt_tokens', 0)
        out_tok = getattr(usage, 'completion_tokens', 0)
        
        # Calculate cost
        cost = 0.0
        try:
            cost = litellm.completion_cost(completion_response=completion_response)
        except Exception:
            # Fallback to CSV rates
            model = kwargs.get("model")
            rates = _MODEL_RATE_MAP.get(str(model))
            if rates:
                in_rate, out_rate = rates
                cost = (in_tok * in_rate + out_tok * out_rate) / 1_000_000.0
        
        _LAST_CALLBACK_DATA = {
            "input_tokens": in_tok,
            "output_tokens": out_tok,
            "cost": cost,
            "finish_reason": getattr(completion_response.choices[0], 'finish_reason', None)
        }
    except Exception as e:
        logger.debug(f"Callback error: {e}")

litellm.success_callback = [_litellm_success_callback]


# --- Helper Functions ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively set all properties as required for OpenAI strict mode."""
    if not isinstance(schema, dict):
        return schema
    
    if schema.get('type') == 'object' and 'properties' in schema:
        schema['required'] = list(schema['properties'].keys())
        for prop in schema['properties'].values():
            _ensure_all_properties_required(prop)
            
    if schema.get('type') == 'array' and 'items' in schema:
        _ensure_all_properties_required(schema['items'])
        
    for key in ('anyOf', 'oneOf', 'allOf'):
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
                
    if '$defs' in schema:
        for definition in schema['$defs'].values():
            _ensure_all_properties_required(definition)
            
    return schema


def _add_additional_properties_false(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Recursively add additionalProperties: false for OpenAI strict mode."""
    if not isinstance(schema, dict):
        return schema
        
    if schema.get('type') == 'object':
        schema['additionalProperties'] = False
        if 'properties' in schema:
            for prop in schema['properties'].values():
                _add_additional_properties_false(prop)
                
    if schema.get('type') == 'array' and 'items' in schema:
        _add_additional_properties_false(schema['items'])
        
    for key in ('anyOf', 'oneOf', 'allOf'):
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
                
    if '$defs' in schema:
        for definition in schema['$defs'].values():
            _add_additional_properties_false(definition)
            
    return schema


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    """Convert Pydantic model to JSON Schema optimized for strict structured output."""
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    schema['__pydantic_class_name__'] = pydantic_class.__name__
    return schema


def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> BaseModel:
    """Validate result against Pydantic model."""
    if isinstance(result, dict):
        return pydantic_class.model_validate(result)
    elif isinstance(result, str):
        return pydantic_class.model_validate_json(result)
    elif isinstance(result, pydantic_class):
        return result
    raise ValueError(f"Cannot validate type {type(result)}")


def _is_wsl_environment() -> bool:
    """Detect Windows Subsystem for Linux."""
    try:
        if os.path.exists('/proc/version'):
            with open('/proc/version', 'r') as f:
                content = f.read().lower()
                if 'microsoft' in content or 'wsl' in content:
                    return True
        return bool(os.getenv('WSL_DISTRO_NAME'))
    except Exception:
        return False


def _sanitize_api_key(key: str) -> str:
    """Sanitize API key (trim whitespace, remove control chars)."""
    if not key:
        return key
    sanitized = key.strip()
    return ''.join(c for c in sanitized if ord(c) >= 32)


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    """Save API key to .env file, replacing existing and cleaning up."""
    lines = []
    if env_path.exists():
        with open(env_path, 'r') as f:
            lines = f.readlines()
            
    new_lines = []
    found = False
    
    for line in lines:
        stripped = line.strip()
        # Remove old commented versions
        if stripped.startswith(f"# {key_name}=") or stripped.startswith(f"# {key_name} ="):
            continue
        # Replace existing
        if stripped.startswith(f"{key_name}=") or stripped.startswith(f"{key_name} ="):
            new_lines.append(f'{key_name}="{value}"\n')
            found = True
        else:
            new_lines.append(line)
            
    if not found:
        if new_lines and not new_lines[-1].endswith('\n'):
            new_lines.append('\n')
        new_lines.append(f'{key_name}="{value}"\n')
        
    with open(env_path, 'w') as f:
        f.writelines(new_lines)


def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    """Load model data from CSV."""
    if csv_path is None or not csv_path.exists():
        try:
            csv_content = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()
            import io
            df = pd.read_csv(io.StringIO(csv_content))
        except Exception:
            raise FileNotFoundError("Could not load llm_model.csv from path or package.")
    else:
        df = pd.read_csv(csv_path)
        
    # Validation & cleanup
    numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_reasoning_tokens']
    for col in numeric_cols:
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors='coerce').fillna(0)
            
    df['avg_cost'] = (df['input'] + df['output']) / 2
    if 'structured_output' in df.columns:
        df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
    if 'reasoning_type' in df.columns:
        df['reasoning_type'] = df['reasoning_type'].fillna('none').astype(str).str.lower()
        
    return df


def _select_model_candidates(strength: float, base_model_name: Optional[str], df: pd.DataFrame) -> List[Dict]:
    """Select candidate models based on strength."""
    # Filter available models (must have API key placeholder)
    df = df[df['api_key'].notna()].copy()
    if df.empty:
        raise ValueError("No models available in CSV.")
        
    # Find base model or surrogate
    base_model = None
    if base_model_name:
        matches = df[df['model'] == base_model_name]
        if not matches.empty:
            base_model = matches.iloc[0]
            
    if base_model is None:
        base_model = df.iloc[0] # Surrogate
        
    candidates = []
    
    if strength == 0.5:
        # Base model priority, fallback by ELO
        candidates = df.sort_values(by='coding_arena_elo', ascending=False).to_dict('records')
        # Move base model to front
        candidates.sort(key=lambda x: 0 if x['model'] == base_model['model'] else 1)
        
    elif strength < 0.5:
        # Interpolate Cost: Base -> Cheapest
        base_cost = base_model['avg_cost']
        cheapest = df.loc[df['avg_cost'].idxmin()]
        
        target_cost = cheapest['avg_cost'] + (strength / 0.5) * (base_cost - cheapest['avg_cost'])
        df['diff'] = abs(df['avg_cost'] - target_cost)
        candidates = df.sort_values('diff').to_dict('records')
        
    else:
        # Interpolate ELO: Base -> Best
        base_elo = base_model['coding_arena_elo']
        best = df.loc[df['coding_arena_elo'].idxmax()]
        
        target_elo = base_elo + ((strength - 0.5) / 0.5) * (best['coding_arena_elo'] - base_elo)
        df['diff'] = abs(df['coding_arena_elo'] - target_elo)
        candidates = df.sort_values('diff').to_dict('records')
        
    return candidates


def _ensure_api_key(model_info: Dict, newly_acquired: Dict, verbose: bool) -> bool:
    """Ensure API key exists, prompt if needed."""
    key_name = model_info.get('api_key')
    if not key_name or key_name == "EXISTING_KEY":
        return True
        
    val = os.getenv(key_name)
    if val:
        os.environ[key_name] = _sanitize_api_key(val)
        newly_acquired[key_name] = False
        return True
        
    if os.getenv('PDD_FORCE'):
        logger.warning(f"Missing key {key_name} in non-interactive mode. Skipping.")
        return False
        
    console = Console()
    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name} for model {model_info['model']}")
    try:
        new_key = input(f"Enter {key_name}: ").strip()
    except EOFError:
        return False
        
    if not new_key:
        return False
        
    sanitized = _sanitize_api_key(new_key)
    os.environ[key_name] = sanitized
    try:
        _save_key_to_env_file(key_name, sanitized, ENV_PATH)
        console.print(f"[green]Saved {key_name} to .env[/green]")
    except Exception as e:
        logger.warning(f"Could not save to .env: {e}")
        
    newly_acquired[key_name] = True
    return True


# --- Response Processing Helpers ---

def _is_malformed_json_response(content: str) -> bool:
    """Detect JSON truncated by excessive newlines (common in some models)."""
    if not content or not isinstance(content, str):
        return False
    stripped = content.strip()
    if not stripped.startswith('{') and not stripped.startswith('['):
        return False
    if stripped.endswith('}') or stripped.endswith(']'):
        return False
        
    # Check for excessive trailing escaped newlines
    trailing_newlines = 0
    temp = stripped
    while temp.endswith('\\n'):
        trailing_newlines += 1
        temp = temp[:-2]
        
    return trailing_newlines > 50 or stripped.endswith('\\')


def _smart_unescape_code(text: str) -> str:
    """Unescape literal \\n to \n only outside of string literals."""
    if '\\n' not in text:
        return text
    # Simple heuristic fallback if complex parsing fails:
    # If text has real newlines, assume mixed state and don't touch
    if '\n' in text:
        return text
    # Otherwise replace all literal \n with real newlines
    return text.replace('\\n', '\n').replace('\\t', '\t').replace('\\"', '"')


def _repair_python_syntax(code: str) -> str:
    """Attempt basic syntax repair on Python code string."""
    import ast
    if not code: return code
    
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        pass
        
    # Trailing quotes
    for q in ['"', "'"]:
        if code.strip().endswith(q):
            candidate = code.strip()[:-1]
            try:
                ast.parse(candidate)
                return candidate
            except SyntaxError:
                pass
    return code


def _unescape_code_newlines(obj: Any) -> Any:
    """Recursively process Pydantic/Dict objects to fix code strings."""
    if isinstance(obj, str):
        # Heuristic: if it looks like code (def, import), try to fix
        if 'def ' in obj or 'import ' in obj or 'return ' in obj:
            repaired = _smart_unescape_code(obj)
            return _repair_python_syntax(repaired)
        return obj
        
    if isinstance(obj, dict):
        return {k: _unescape_code_newlines(v) for k, v in obj.items()}
        
    if isinstance(obj, list):
        return [_unescape_code_newlines(i) for i in obj]
        
    if isinstance(obj, BaseModel):
        for field in obj.model_fields:
            val = getattr(obj, field)
            setattr(obj, field, _unescape_code_newlines(val))
        return obj
        
    return obj


def _llm_invoke_cloud(
    prompt, input_json, strength, temperature, verbose, 
    output_pydantic, output_schema, time, use_batch_mode, messages, language
):
    """Execute via Cloud Function."""
    try:
        from pdd.core.cloud import CloudConfig
    except ImportError:
        raise CloudFallbackError("Cloud module not available")
    
    console = Console()
    jwt = CloudConfig.get_jwt_token(verbose=verbose)
    if not jwt:
        raise CloudFallbackError("Authentication failed")
        
    url = CloudConfig.get_endpoint_url("llmInvoke")
    
    payload = {
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "useBatchMode": use_batch_mode,
        "language": language
    }
    
    if messages:
        payload["messages"] = messages
    else:
        payload["prompt"] = prompt
        payload["inputJson"] = input_json
        
    if output_pydantic:
        payload["outputSchema"] = _pydantic_to_json_schema(output_pydantic)
    elif output_schema:
        payload["outputSchema"] = output_schema
        
    try:
        resp = requests.post(
            url, 
            json=payload, 
            headers={"Authorization": f"Bearer {jwt}"},
            timeout=300
        )
        
        if resp.status_code == 200:
            data = resp.json()
            result = data.get("result")
            if output_pydantic and result:
                result = _validate_with_pydantic(result, output_pydantic)
            return {
                "result": result,
                "cost": data.get("totalCost", 0),
                "model_name": data.get("modelName", "cloud"),
                "thinking_output": data.get("thinkingOutput")
            }
            
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits")
            
        if resp.status_code in [401, 403]:
            # Clear cache on auth error
            try:
                from pdd.auth_service import clear_jwt_cache
                clear_jwt_cache()
            except ImportError:
                pass
            raise CloudFallbackError(f"Auth error {resp.status_code}")
            
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Server error {resp.status_code}")
            
        raise CloudInvocationError(f"Cloud error: {resp.text}")
        
    except requests.RequestException as e:
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
    """
    Invoke LLM with automatic fallback, API management, and structured output.
    """
    set_verbose_logging(verbose)
    console = Console()

    # Cloud logic
    if use_cloud is None:
        if os.getenv("PDD_FORCE_LOCAL") == "1":
            use_cloud = False
        else:
            try:
                from pdd.core.cloud import CloudConfig
                use_cloud = CloudConfig.is_cloud_enabled()
            except ImportError:
                use_cloud = False

    if use_cloud:
        try:
            return _llm_invoke_cloud(
                prompt, input_json, strength, temperature, verbose, 
                output_pydantic, output_schema, time, use_batch_mode, messages, language
            )
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud failed ({e}), falling back to local...[/yellow]")
        except InsufficientCreditsError:
            raise
        except CloudInvocationError as e:
            console.print(f"[yellow]Cloud error ({e}), falling back to local...[/yellow]")

    # Input Validation
    if not messages and not (prompt and input_json is not None):
        raise ValueError("Either 'messages' or both 'prompt' and 'input_json' must be provided.")
        
    formatted_messages = messages
    if not messages:
        # Format prompt
        if use_batch_mode:
            if not isinstance(input_json, list):
                raise ValueError("input_json must be list for batch mode")
            formatted_messages = [[{"role": "user", "content": prompt.format(**item)}] for item in input_json]
        else:
            if not isinstance(input_json, dict):
                raise ValueError("input_json must be dict when use_batch_mode is False")
            try:
                formatted_messages = [{"role": "user", "content": prompt.format(**input_json)}]
            except KeyError as e:
                raise ValueError(f"Prompt formatting error: Missing key {e}")

    # Model Selection
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)
    _MODEL_RATE_MAP.update({
        str(r['model']): (r.get('input', 0), r.get('output', 0)) 
        for _, r in model_df.iterrows()
    })
    
    candidates = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    
    last_exception = None
    newly_acquired_keys = {}
    
    for model_info in candidates:
        model_name = model_info['model']
        provider = model_info.get('provider', '').lower()
        api_key_name = model_info.get('api_key')
        
        if verbose:
            logger.info(f"Attempting model: {model_name}")
            
        retry_same = True
        current_temp = temperature
        
        while retry_same:
            retry_same = False
            
            # API Key
            if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
                break
                
            kwargs = {
                "model": model_name,
                "messages": formatted_messages,
                "temperature": current_temp,
                "num_retries": 2,
                "timeout": LLM_CALL_TIMEOUT
            }
            
            # Vertex AI
            if provider in ('google', 'vertex_ai') or model_name.startswith('vertex_ai/'):
                if api_key_name == 'VERTEX_CREDENTIALS':
                    creds_path = os.getenv("VERTEX_CREDENTIALS")
                    if creds_path:
                        try:
                            with open(creds_path) as f:
                                kwargs['vertex_credentials'] = json.dumps(json.load(f))
                        except Exception:
                            logger.warning("Could not load vertex credentials file")
                    
                    proj = os.getenv("VERTEX_PROJECT")
                    loc = model_info.get('location') or os.getenv("VERTEX_LOCATION")
                    if proj: kwargs['vertex_project'] = proj
                    if loc: kwargs['vertex_location'] = loc
            
            # Other keys
            elif api_key_name:
                val = os.getenv(api_key_name)
                if val: kwargs['api_key'] = _sanitize_api_key(val)
                
            # Base URL
            if model_info.get('base_url'):
                kwargs['base_url'] = model_info['base_url']
                
            # LM Studio
            if 'lm_studio' in model_name.lower() or provider == 'lm_studio':
                if not kwargs.get('base_url'):
                    kwargs['base_url'] = os.getenv('LM_STUDIO_API_BASE', 'http://localhost:1234/v1')
                if not kwargs.get('api_key'):
                    kwargs['api_key'] = 'lm-studio'
                    
            # Reasoning
            reasoning_type = model_info.get('reasoning_type', 'none')
            max_r_tokens = int(model_info.get('max_reasoning_tokens', 0))
            
            if time > 0 and reasoning_type != 'none':
                if reasoning_type == 'budget' and max_r_tokens > 0:
                    budget = int(time * max_r_tokens)
                    if provider == 'anthropic':
                        kwargs['thinking'] = {"type": "enabled", "budget_tokens": budget}
                        kwargs['temperature'] = 1.0  # Anthropic requirement
                elif reasoning_type == 'effort':
                    effort = "high" if time > 0.7 else "medium" if time > 0.3 else "low"
                    # OpenAI gpt-5 specific
                    if 'gpt-5' in model_name.lower() and provider == 'openai':
                        kwargs['reasoning'] = {"effort": effort, "summary": "auto"}
                    else:
                        kwargs['reasoning_effort'] = effort

            # Structured Output
            response_format = None
            if output_pydantic or output_schema:
                is_supported = model_info.get('structured_output', False)
                if is_supported:
                    if output_pydantic:
                        schema = output_pydantic.model_json_schema()
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {
                                "name": output_pydantic.__name__,
                                "schema": schema,
                                "strict": True
                            }
                        }
                    else:
                        # Schema handling
                        schema = output_schema.copy()
                        _ensure_all_properties_required(schema)
                        _add_additional_properties_false(schema)
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {"name": "response", "schema": schema, "strict": True}
                        }
                    
                    kwargs['response_format'] = response_format
                    
                    # Provider hacks
                    if provider == 'lm_studio':
                        kwargs['extra_body'] = {"response_format": response_format}
                        del kwargs['response_format']
                    elif provider == 'groq':
                        # Groq specific handling: simple json_object + prompt injection
                        kwargs['response_format'] = {"type": "json_object"}
                        instr = f"Respond with valid JSON matching:\n{json.dumps(schema)}"
                        if kwargs['messages'] and isinstance(kwargs['messages'][0], dict):
                            kwargs['messages'][0]['content'] += f"\n\n{instr}"

            try:
                # Execution
                if 'gpt-5' in model_name.lower() and provider == 'openai' and not use_batch_mode:
                    # Responses API
                    txt_fmt = {"type": "text"}
                    if response_format:
                        txt_fmt = response_format["json_schema"]
                    
                    # Convert messages to input string for responses API if needed
                    input_text = str(formatted_messages) 
                    
                    resp = litellm.responses(
                        model=model_name,
                        input=input_text,
                        text={"format": txt_fmt},
                        **{k:v for k,v in kwargs.items() if k not in ['messages', 'response_format']}
                    )
                    # Helper to extract from responses API structure
                    content = getattr(resp.output[0].content[0], 'text', None)
                    response_obj = type('obj', (object,), {'choices': [type('c', (object,), {'message': type('m', (object,), {'content': content, 'reasoning_content': None})})()]})
                    
                elif use_batch_mode:
                    response_obj = litellm.batch_completion(**kwargs)
                else:
                    response_obj = litellm.completion(**kwargs)

                # Processing
                responses = response_obj if use_batch_mode else [response_obj]
                results = []
                thinking_data = []
                
                for idx, r in enumerate(responses):
                    msg = r.choices[0].message
                    content = msg.content
                    thinking = getattr(msg, 'reasoning_content', None) or r._hidden_params.get('thinking')
                    thinking_data.append(thinking)
                    
                    # Repairs and Parsing
                    if content is None or (isinstance(content, str) and _is_malformed_json_response(content)):
                        logger.warning(f"Malformed/None response for item {idx}, retrying...")
                        litellm.cache = None
                        if content is None: raise ValueError("None content received")

                    val_res = content
                    if output_pydantic or output_schema:
                        try:
                            # Attempt parse
                            to_parse = content
                            if isinstance(content, str):
                                # Extraction logic
                                import re
                                match = re.search(r"```json\s*(\{.*?\})\s*```", content, re.DOTALL)
                                if match: to_parse = match.group(1)
                                
                            if output_pydantic:
                                if isinstance(to_parse, str):
                                    val_res = output_pydantic.model_validate_json(to_parse)
                                else:
                                    val_res = output_pydantic.model_validate(to_parse)
                            else:
                                if isinstance(to_parse, str):
                                    val_res = json.loads(to_parse)
                                    
                            # Post-processing
                            val_res = _unescape_code_newlines(val_res)
                            
                            # Validation
                            if language in (None, 'python') and _has_invalid_python_code(val_res):
                                logger.warning("Invalid Python syntax detected after repair.")
                                
                        except Exception as e:
                            raise SchemaValidationError(f"Validation failed: {e}", raw_response=content)

                    results.append(val_res)

                # Cost from callback
                cost = _LAST_CALLBACK_DATA.get('cost', 0.0)
                
                return {
                    "result": results if use_batch_mode else results[0],
                    "cost": cost,
                    "model_name": model_name,
                    "thinking_output": thinking_data if use_batch_mode else thinking_data[0]
                }

            except (openai.AuthenticationError, openai.BadRequestError) as e:
                # Auth error logic
                if "temperature" in str(e).lower() and "thinking" in str(e).lower() and not retry_same:
                    # Auto-fix anthropic temp
                    current_temp = 1.0 if 'thinking' in kwargs else 0.99
                    retry_same = True
                    continue
                    
                if newly_acquired_keys.get(api_key_name):
                    # Retry prompt
                    os.environ.pop(api_key_name, None)
                    retry_same = True
                    continue
                last_exception = e
                logger.warning(f"Model {model_name} failed: {e}")
                
            except SchemaValidationError as e:
                logger.warning(f"Schema validation failed for {model_name}: {e}")
                last_exception = e
                
            except Exception as e:
                logger.warning(f"Model {model_name} error: {e}")
                last_exception = e

    raise RuntimeError(f"All candidates failed. Last error: {last_exception}")

def _has_invalid_python_code(obj: Any) -> bool:
    import ast
    if isinstance(obj, str):
        if 'def ' in obj or 'import ' in obj:
            try:
                ast.parse(obj)
            except SyntaxError:
                return True
    if isinstance(obj, dict):
        return any(_has_invalid_python_code(v) for k,v in obj.items() if k not in ['reasoning', 'explanation'])
    if isinstance(obj, BaseModel):
        return any(_has_invalid_python_code(getattr(obj, k)) for k in obj.model_fields if k not in ['reasoning', 'explanation'])
    return False