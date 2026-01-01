# Corrected code_under_test (llm_invoke.py)
# Added optional debugging prints in _select_model_candidates

import os
import pandas as pd
import litellm
import logging # ADDED FOR DETAILED LOGGING
import importlib.resources
from litellm.caching.caching import Cache  # Fix for LiteLLM v1.75.5+

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

# Ensure LiteLLM drops provider-unsupported params instead of erroring
# This prevents failures like UnsupportedParamsError for OpenAI gpt-5-* when
# passing generic params (e.g., reasoning_effort) not accepted by that API path.
try:
    _drop_params_env = os.getenv("LITELLM_DROP_PARAMS", "true")
    litellm.drop_params = str(_drop_params_env).lower() in ("1", "true", "yes", "on")
except Exception:
    # Be conservative: default to True even if env parsing fails
    litellm.drop_params = True

# Add a console handler if none exists
if not logger.handlers:
    console_handler = logging.StreamHandler()
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    
    # Only add handler to litellm logger if it doesn't have any
    if not litellm_logger.handlers:
        litellm_logger.addHandler(console_handler)

# Function to set up file logging if needed
def setup_file_logging(log_file_path=None):
    """Configure rotating file handler for logging"""
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

# Function to set verbose logging
def set_verbose_logging(verbose=False):
    """Set verbose logging based on flag or environment variable"""
    if verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1":
        logger.setLevel(logging.DEBUG)
        litellm_logger.setLevel(logging.DEBUG)
        logger.debug("Verbose logging enabled")
    
# --- End Logging Configuration ---

import json
# from rich import print as rprint # Replaced with logger
from dotenv import load_dotenv
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union, Tuple
from pydantic import BaseModel, ValidationError
import openai  # Import openai for exception handling as LiteLLM maps to its types
import warnings
import time as time_module # Alias to avoid conflict with 'time' parameter
# Import the default model constant
from pdd import DEFAULT_LLM_MODEL

# Opt-in to future pandas behavior regarding downcasting
try:
    pd.set_option('future.no_silent_downcasting', True)
except pd._config.config.OptionError:
    # Skip if option doesn't exist in older pandas versions
    pass


# --- Custom Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM response fails Pydantic/JSON schema validation.

    This exception triggers model fallback when caught at the outer exception
    handler level, allowing the next candidate model to be tried.

    Issue #168: Previously, validation errors only logged an error and continued
    to the next batch item, never triggering model fallback.
    """

    def __init__(self, message: str, raw_response: Any = None, item_index: int = 0):
        super().__init__(message)
        self.raw_response = raw_response
        self.item_index = item_index


def _is_wsl_environment() -> bool:
    """
    Detect if we're running in WSL (Windows Subsystem for Linux) environment.
    
    Returns:
        True if running in WSL, False otherwise
    """
    try:
        # Check for WSL-specific indicators
        if os.path.exists('/proc/version'):
            with open('/proc/version', 'r') as f:
                version_info = f.read().lower()
                return 'microsoft' in version_info or 'wsl' in version_info
        
        # Alternative check: WSL_DISTRO_NAME environment variable
        if os.getenv('WSL_DISTRO_NAME'):
            return True
            
        # Check for Windows-style paths in PATH
        path_env = os.getenv('PATH', '')
        return '/mnt/c/' in path_env.lower()
        
    except Exception:
        return False


def _openai_responses_supports_response_format() -> bool:
    """Detect if current OpenAI Python SDK supports `response_format` on Responses.create.

    Returns True if the installed SDK exposes a `response_format` parameter on
    `openai.resources.responses.Responses.create`, else False. This avoids
    sending unsupported kwargs and triggering TypeError at runtime.
    """
    try:
        import inspect
        from openai.resources.responses import Responses
        sig = inspect.signature(Responses.create)
        return "response_format" in sig.parameters
    except Exception:
        return False


def _get_environment_info() -> Dict[str, str]:
    """
    Get environment information for debugging and error reporting.
    
    Returns:
        Dictionary containing environment details
    """
    import platform
    
    info = {
        'platform': platform.system(),
        'platform_release': platform.release(),
        'platform_version': platform.version(),
        'architecture': platform.machine(),
        'is_wsl': str(_is_wsl_environment()),
        'python_version': platform.python_version(),
    }
    
    # Add WSL-specific information
    if _is_wsl_environment():
        info['wsl_distro'] = os.getenv('WSL_DISTRO_NAME', 'unknown')
        info['wsl_interop'] = os.getenv('WSL_INTEROP', 'not_set')
    
    return info

# <<< SET LITELLM DEBUG LOGGING >>>
# os.environ['LITELLM_LOG'] = 'DEBUG' # Keep commented out unless debugging LiteLLM itself

# --- Constants and Configuration ---

# Determine project root: 1. PDD_PATH env var, 2. Search upwards from script, 3. CWD
PROJECT_ROOT = None
PDD_PATH_ENV = os.getenv("PDD_PATH")

if PDD_PATH_ENV:
    _path_from_env = Path(PDD_PATH_ENV)
    if _path_from_env.is_dir():
        PROJECT_ROOT = _path_from_env.resolve()
        logger.debug(f"Using PROJECT_ROOT from PDD_PATH: {PROJECT_ROOT}")
    else:
        warnings.warn(f"PDD_PATH environment variable ('{PDD_PATH_ENV}') is set but not a valid directory. Attempting auto-detection.")

if PROJECT_ROOT is None: # If PDD_PATH wasn't set or was invalid
    try:
        # Start from the current working directory (where user is running PDD)
        current_dir = Path.cwd().resolve()
        # Look for project markers (e.g., .git, pyproject.toml, data/, .env)
        # Go up a maximum of 5 levels to prevent infinite loops
        for _ in range(5):
            has_git = (current_dir / ".git").exists()
            has_pyproject = (current_dir / "pyproject.toml").exists()
            has_data = (current_dir / "data").is_dir()
            has_dotenv = (current_dir / ".env").exists()

            if has_git or has_pyproject or has_data or has_dotenv:
                PROJECT_ROOT = current_dir
                logger.debug(f"Determined PROJECT_ROOT by marker search from CWD: {PROJECT_ROOT}")
                break

            parent_dir = current_dir.parent
            if parent_dir == current_dir: # Reached filesystem root
                break
            current_dir = parent_dir

    except Exception as e: # Catch potential permission errors etc.
        warnings.warn(f"Error during project root auto-detection from current working directory: {e}")

if PROJECT_ROOT is None: # Fallback to CWD if no method succeeded
    PROJECT_ROOT = Path.cwd().resolve()
    warnings.warn(f"Could not determine project root automatically. Using current working directory: {PROJECT_ROOT}. Ensure this is the intended root or set the PDD_PATH environment variable.")


# ENV_PATH is set after _is_env_path_package_dir is defined (see below)

# --- Determine LLM_MODEL_CSV_PATH ---
# Prioritize ~/.pdd/llm_model.csv, then a project .pdd from the current CWD,
# then PROJECT_ROOT (which may be set from PDD_PATH), else fall back to package.
user_pdd_dir = Path.home() / ".pdd"
user_model_csv_path = user_pdd_dir / "llm_model.csv"

def _detect_project_root_from_cwd(max_levels: int = 5) -> Path:
    """Search upwards from the current working directory for common project markers.

    This intentionally ignores PDD_PATH to support CLI invocations that set
    PDD_PATH to the installed package location. We want to honor a real project
    checkout's .pdd/llm_model.csv when running inside it.
    """
    try:
        current_dir = Path.cwd().resolve()
        for _ in range(max_levels):
            if (
                (current_dir / ".git").exists()
                or (current_dir / "pyproject.toml").exists()
                or (current_dir / "data").is_dir()
                or (current_dir / ".env").exists()
            ):
                return current_dir
            parent = current_dir.parent
            if parent == current_dir:
                break
            current_dir = parent
    except Exception:
        pass
    return Path.cwd().resolve()

# Resolve candidates
project_root_from_cwd = _detect_project_root_from_cwd()
project_csv_from_cwd = project_root_from_cwd / ".pdd" / "llm_model.csv"
project_csv_from_env = PROJECT_ROOT / ".pdd" / "llm_model.csv"

# Detect whether PDD_PATH points to the installed package directory. If so,
# don't prioritize it over the real project from CWD.
try:
    _installed_pkg_root = importlib.resources.files('pdd')
    # importlib.resources.files returns a Traversable; get a FS path string if possible
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
        # Treat equal or subpath as package dir
        return env_path == pkg_path or str(env_path).startswith(str(pkg_path))
    except Exception:
        return False

# ENV_PATH: Use CWD-based project root when PDD_PATH points to package directory
# This ensures .env is written to the user's project, not the installed package location
if _is_env_path_package_dir(PROJECT_ROOT):
    ENV_PATH = project_root_from_cwd / ".env"
    logger.debug(f"PDD_PATH points to package; using ENV_PATH from CWD: {ENV_PATH}")
else:
    ENV_PATH = PROJECT_ROOT / ".env"

# Selection order
if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH = user_model_csv_path
    logger.info(f"Using user-specific LLM model CSV: {LLM_MODEL_CSV_PATH}")
elif (not _is_env_path_package_dir(PROJECT_ROOT)) and project_csv_from_env.is_file():
    # Honor an explicitly-set PDD_PATH pointing to a real project directory
    LLM_MODEL_CSV_PATH = project_csv_from_env
    logger.info(f"Using project-specific LLM model CSV (from PDD_PATH): {LLM_MODEL_CSV_PATH}")
elif project_csv_from_cwd.is_file():
    # Otherwise, prefer the project relative to the current working directory
    LLM_MODEL_CSV_PATH = project_csv_from_cwd
    logger.info(f"Using project-specific LLM model CSV (from CWD): {LLM_MODEL_CSV_PATH}")
else:
    # Neither exists, we'll use a marker path that _load_model_data will handle
    LLM_MODEL_CSV_PATH = None
    logger.info("No local LLM model CSV found, will use package default")
# ---------------------------------

# Load environment variables from .env file
logger.debug(f"Attempting to load .env from: {ENV_PATH}")
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)
    logger.debug(f"Loaded .env file from: {ENV_PATH}")
else:
    # Silently proceed if .env is optional
    logger.debug(f".env file not found at {ENV_PATH}. API keys might need to be provided manually.")

# Default model if PDD_MODEL_DEFAULT is not set
# Use the imported constant as the default
DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", DEFAULT_LLM_MODEL)

# --- LiteLLM Cache Configuration (S3 compatible for GCS, with SQLite fallback) ---
GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_ENDPOINT_URL = "https://storage.googleapis.com" # GCS S3 compatibility endpoint
GCS_REGION_NAME = os.getenv("GCS_REGION_NAME", "auto") # Often 'auto' works for GCS
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID") # Load HMAC Key ID
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY") # Load HMAC Secret

# Sanitize GCS credentials to handle WSL environment issues
if GCS_HMAC_ACCESS_KEY_ID:
    GCS_HMAC_ACCESS_KEY_ID = GCS_HMAC_ACCESS_KEY_ID.strip()
if GCS_HMAC_SECRET_ACCESS_KEY:
    GCS_HMAC_SECRET_ACCESS_KEY = GCS_HMAC_SECRET_ACCESS_KEY.strip()

cache_configured = False
configured_cache = None  # Store the configured cache instance for restoration

if GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    # Store original AWS credentials before overwriting for GCS cache setup
    original_aws_access_key_id = os.environ.get('AWS_ACCESS_KEY_ID')
    original_aws_secret_access_key = os.environ.get('AWS_SECRET_ACCESS_KEY')
    original_aws_region_name = os.environ.get('AWS_REGION_NAME')

    try:
        # Temporarily set AWS env vars to GCS HMAC keys for S3 compatible cache
        os.environ['AWS_ACCESS_KEY_ID'] = GCS_HMAC_ACCESS_KEY_ID
        os.environ['AWS_SECRET_ACCESS_KEY'] = GCS_HMAC_SECRET_ACCESS_KEY
        # os.environ['AWS_REGION_NAME'] = GCS_REGION_NAME  # Uncomment if needed

        configured_cache = Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_region_name=GCS_REGION_NAME, # Pass region explicitly to cache
            s3_endpoint_url=GCS_ENDPOINT_URL,
        )
        litellm.cache = configured_cache
        logger.info(f"LiteLLM cache configured for GCS bucket (S3 compatible): {GCS_BUCKET_NAME}")
        cache_configured = True

    except Exception as e:
        warnings.warn(f"Failed to configure LiteLLM S3/GCS cache: {e}. Attempting SQLite cache fallback.")
        litellm.cache = None # Explicitly disable cache on failure (will try SQLite next)

    finally:
        # Restore original AWS credentials after cache setup attempt
        if original_aws_access_key_id is not None:
            os.environ['AWS_ACCESS_KEY_ID'] = original_aws_access_key_id
        elif 'AWS_ACCESS_KEY_ID' in os.environ:
            del os.environ['AWS_ACCESS_KEY_ID']

        if original_aws_secret_access_key is not None:
            os.environ['AWS_SECRET_ACCESS_KEY'] = original_aws_secret_access_key
        elif 'AWS_SECRET_ACCESS_KEY' in os.environ:
            del os.environ['AWS_SECRET_ACCESS_KEY']

        if original_aws_region_name is not None:
            os.environ['AWS_REGION_NAME'] = original_aws_region_name
        elif 'AWS_REGION_NAME' in os.environ:
            pass # Or just leave it if the temporary setting wasn't done/needed

# Check if caching is disabled via environment variable
if os.getenv("LITELLM_CACHE_DISABLE") == "1":
    logger.info("LiteLLM caching disabled via LITELLM_CACHE_DISABLE=1")
    litellm.cache = None
    cache_configured = True

if not cache_configured:
    try:
        # Try disk-based cache as a fallback
        sqlite_cache_path = PROJECT_ROOT / "litellm_cache.sqlite"
        configured_cache = Cache(type="disk", disk_cache_dir=str(sqlite_cache_path))
        litellm.cache = configured_cache
        logger.info(f"LiteLLM disk cache configured at {sqlite_cache_path}")
        cache_configured = True
    except Exception as e2:
        warnings.warn(f"Failed to configure LiteLLM disk cache: {e2}. Caching is disabled.")
        litellm.cache = None

if not cache_configured:
    warnings.warn("All LiteLLM cache configuration attempts failed. Caching is disabled.")
    litellm.cache = None

# --- LiteLLM Callback for Success Logging ---

# Module-level storage for last callback data (Use with caution in concurrent environments)
_LAST_CALLBACK_DATA = {
    "input_tokens": 0,
    "output_tokens": 0,
    "finish_reason": None,
    "cost": 0.0,
}

def _litellm_success_callback(
    kwargs: Dict[str, Any],              # kwargs passed to completion
    completion_response: Any,            # response object from completion
    start_time: float, end_time: float   # start/end time
):
    """
    LiteLLM success callback to capture usage and finish reason.
    Stores data in a module-level variable for potential retrieval.
    """
    global _LAST_CALLBACK_DATA
    usage = getattr(completion_response, 'usage', None)
    input_tokens = getattr(usage, 'prompt_tokens', 0)
    output_tokens = getattr(usage, 'completion_tokens', 0)
    finish_reason = getattr(completion_response.choices[0], 'finish_reason', None)

    calculated_cost = 0.0
    try:
        # Attempt 1: Use the response object directly (works for most single calls)
        cost_val = litellm.completion_cost(completion_response=completion_response)
        calculated_cost = cost_val if cost_val is not None else 0.0
    except Exception as e1:
        # Attempt 2: Compute via tokens and model mapping. If LiteLLM mapping is
        # missing or API differs, fall back to CSV rates in _MODEL_RATE_MAP.
        logger.debug(f"Attempting cost calculation with fallback method: {e1}")
        try:
            model_name = kwargs.get("model")
            if model_name and usage:
                in_tok = getattr(usage, 'prompt_tokens', None)
                out_tok = getattr(usage, 'completion_tokens', None)
                # Some providers may use 'input_tokens'/'output_tokens'
                if in_tok is None:
                    in_tok = getattr(usage, 'input_tokens', 0)
                if out_tok is None:
                    out_tok = getattr(usage, 'output_tokens', 0)

                # Try LiteLLM helper (arg names vary across versions)
                try:
                    cost_val = litellm.completion_cost(
                        model=model_name,
                        prompt_tokens=in_tok,
                        completion_tokens=out_tok,
                    )
                    calculated_cost = cost_val if cost_val is not None else 0.0
                except TypeError:
                    # Older/newer versions may require input/output token names
                    try:
                        cost_val = litellm.completion_cost(
                            model=model_name,
                            input_tokens=in_tok,
                            output_tokens=out_tok,
                        )
                        calculated_cost = cost_val if cost_val is not None else 0.0
                    except Exception as e3:
                        # Final fallback: compute using CSV rates
                        rates = _MODEL_RATE_MAP.get(str(model_name))
                        if rates is not None:
                            in_rate, out_rate = rates
                            calculated_cost = (float(in_tok or 0) * in_rate + float(out_tok or 0) * out_rate) / 1_000_000.0
                        else:
                            calculated_cost = 0.0
                        logger.debug(f"Cost calculation failed with LiteLLM token API; used CSV rates if available. Detail: {e3}")
            else:
                calculated_cost = 0.0
        except Exception as e2:
            calculated_cost = 0.0 # Default to 0 on any error
            logger.debug(f"Cost calculation failed with fallback method: {e2}")

    _LAST_CALLBACK_DATA["input_tokens"] = input_tokens
    _LAST_CALLBACK_DATA["output_tokens"] = output_tokens
    _LAST_CALLBACK_DATA["finish_reason"] = finish_reason
    _LAST_CALLBACK_DATA["cost"] = calculated_cost # Store the calculated cost

    # Callback doesn't need to return a value now
    # return calculated_cost

    # Example of logging within the callback (can be expanded)
    # logger.info(f"[Callback] Tokens: In={input_tokens}, Out={output_tokens}. Reason: {finish_reason}. Cost: ${calculated_cost:.6f}")

# Register the callback with LiteLLM
litellm.success_callback = [_litellm_success_callback]

# --- Cost Mapping Support (CSV Rates) ---
# Populate from CSV inside llm_invoke; used by callback fallback
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}

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

# --- Helper Functions ---

def _is_malformed_json_response(content: str, threshold: int = 100) -> bool:
    """
    Detect if a JSON response appears malformed due to excessive trailing newlines.

    This can happen when Gemini generates thousands of \n characters in a JSON string value,
    causing the response to be truncated and missing closing braces.

    Args:
        content: The raw response content string
        threshold: Number of consecutive trailing \n sequences to consider malformed

    Returns:
        True if the response appears malformed, False otherwise
    """
    if not content or not isinstance(content, str):
        return False

    # Check if it starts like JSON but doesn't end properly
    stripped = content.strip()
    if not stripped.startswith('{'):
        return False

    # If it ends with }, it's probably fine
    if stripped.endswith('}'):
        return False

    # Count trailing \n sequences (escaped newlines in JSON strings)
    # The pattern \n in a JSON string appears as \\n in the raw content
    trailing_newline_count = 0
    check_content = stripped
    while check_content.endswith('\\n'):
        trailing_newline_count += 1
        check_content = check_content[:-2]

    # If there are many trailing \n sequences, it's likely malformed
    if trailing_newline_count >= threshold:
        return True

    # Also check for response that looks truncated mid-string
    # (ends with characters that suggest we're inside a JSON string value)
    if not stripped.endswith('}') and not stripped.endswith(']') and not stripped.endswith('"'):
        # Could be truncated in the middle of an escaped sequence
        if stripped.endswith('\\'):
            return True

    return False


def _load_model_data(csv_path: Optional[Path]) -> pd.DataFrame:
    """Loads and preprocesses the LLM model data from CSV.
    
    Args:
        csv_path: Path to CSV file, or None to use package default
        
    Returns:
        DataFrame with model configuration data
    """
    # If csv_path is provided, try to load from it
    if csv_path is not None:
        if not csv_path.exists():
            logger.warning(f"Specified LLM model CSV not found at {csv_path}, trying package default")
            csv_path = None
        else:
            try:
                df = pd.read_csv(csv_path)
                logger.debug(f"Loaded model data from {csv_path}")
                # Continue with the rest of the function...
            except Exception as e:
                logger.warning(f"Failed to load CSV from {csv_path}: {e}, trying package default")
                csv_path = None
    
    # If csv_path is None or loading failed, use package default
    if csv_path is None:
        try:
            # Use importlib.resources to load the packaged CSV
            csv_data = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()
            import io
            df = pd.read_csv(io.StringIO(csv_data))
            logger.info("Loaded model data from package default")
        except Exception as e:
            raise FileNotFoundError(f"Failed to load default LLM model CSV from package: {e}")
    
    try:
        # Basic validation and type conversion
        required_cols = ['provider', 'model', 'input', 'output', 'coding_arena_elo', 'api_key', 'structured_output', 'reasoning_type']
        for col in required_cols:
            if col not in df.columns:
                raise ValueError(f"Missing required column in CSV: {col}")

        # Convert numeric columns, handling potential errors
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
            if col in df.columns:
                # Use errors='coerce' to turn unparseable values into NaN
                df[col] = pd.to_numeric(df[col], errors='coerce')

        # Fill NaN in critical numeric columns used for selection/interpolation
        df['input'] = df['input'].fillna(0.0)
        df['output'] = df['output'].fillna(0.0)
        df['coding_arena_elo'] = df['coding_arena_elo'].fillna(0) # Use 0 ELO for missing
        # Ensure max_reasoning_tokens is numeric, fillna with 0
        df['max_reasoning_tokens'] = df['max_reasoning_tokens'].fillna(0).astype(int) # Ensure int

        # Calculate average cost (handle potential division by zero if needed, though unlikely with fillna)
        df['avg_cost'] = (df['input'] + df['output']) / 2

        # Ensure boolean interpretation for structured_output
        if 'structured_output' in df.columns:
             df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
        else:
             df['structured_output'] = False # Assume false if column missing

        # Ensure reasoning_type is string, fillna with 'none' and lowercase
        df['reasoning_type'] = df['reasoning_type'].fillna('none').astype(str).str.lower()

        # Ensure api_key is treated as string, fill NaN with empty string ''
        # This handles cases where read_csv might interpret empty fields as NaN
        df['api_key'] = df['api_key'].fillna('').astype(str)

        return df
    except Exception as e:
        raise RuntimeError(f"Error loading or processing LLM model CSV {csv_path}: {e}") from e

def _select_model_candidates(
    strength: float,
    base_model_name: str,
    model_df: pd.DataFrame
) -> List[Dict[str, Any]]:
    """Selects and sorts candidate models based on strength and availability."""

    # 1. Filter by API Key Name Presence (initial availability check)
    # Keep models with a non-empty api_key field in the CSV.
    # The actual key value check happens later.
    # Allow models with empty api_key (e.g., Bedrock using AWS creds, local models)
    available_df = model_df[model_df['api_key'].notna()].copy()

    # --- Check if the initial DataFrame itself was empty ---
    if model_df.empty:
        raise ValueError("Loaded model data is empty. Check CSV file.")

    # --- Check if filtering resulted in empty (might indicate all models had NaN api_key) ---
    if available_df.empty:
        # This case is less likely if notna() is the only filter, but good to check.
        logger.warning("No models found after filtering for non-NaN api_key. Check CSV 'api_key' column.")
        # Decide if this should be a hard error or allow proceeding if logic permits
        # For now, let's raise an error as it likely indicates a CSV issue.
        raise ValueError("No models available after initial filtering (all had NaN 'api_key'?).")

    # 2. Find Base Model
    base_model_row = available_df[available_df['model'] == base_model_name]
    if base_model_row.empty:
        # Try finding base model in the *original* df in case it was filtered out
        original_base = model_df[model_df['model'] == base_model_name]
        if not original_base.empty:
            # Base exists but may be misconfigured (e.g., missing API key). Keep erroring loudly.
            raise ValueError(
                f"Base model '{base_model_name}' found in CSV but requires API key '{original_base.iloc[0]['api_key']}' which might be missing or invalid configuration."
            )
        # Option A': Soft fallback – choose a reasonable surrogate base and continue
        # Strategy (simplified and deterministic): pick the first available model
        # from the CSV as the surrogate base. This mirrors typical CSV ordering
        # expectations and keeps behavior predictable across environments.
        try:
            base_model = available_df.iloc[0]
            logger.warning(
                f"Base model '{base_model_name}' not found in CSV. Falling back to surrogate base '{base_model['model']}' (Option A')."
            )
        except Exception:
            # If any unexpected error occurs during fallback, raise a clear error
            raise ValueError(
                f"Specified base model '{base_model_name}' not found and fallback selection failed. Check your LLM model CSV."
            )
    else:
        base_model = base_model_row.iloc[0]

    # 3. Determine Target and Sort
    candidates = []
    target_metric_value = None # For debugging print

    if strength == 0.5:
        # target_model = base_model
        # Sort remaining by ELO descending as fallback
        available_df['sort_metric'] = -available_df['coding_arena_elo'] # Negative for descending sort
        candidates = available_df.sort_values(by='sort_metric').to_dict('records')
        # Ensure effective base model is first if it exists (supports surrogate base)
        effective_base_name = str(base_model['model']) if isinstance(base_model, pd.Series) else base_model_name
        if any(c['model'] == effective_base_name for c in candidates):
            candidates.sort(key=lambda x: 0 if x['model'] == effective_base_name else 1)
        target_metric_value = f"Base Model ELO: {base_model['coding_arena_elo']}"

    elif strength < 0.5:
        # Interpolate by Cost (downwards from base)
        base_cost = base_model['avg_cost']
        cheapest_model = available_df.loc[available_df['avg_cost'].idxmin()]
        cheapest_cost = cheapest_model['avg_cost']

        if base_cost <= cheapest_cost: # Handle edge case where base is cheapest
             target_cost = cheapest_cost + strength * (base_cost - cheapest_cost) # Will be <= base_cost
        else:
             # Interpolate between cheapest and base
             target_cost = cheapest_cost + (strength / 0.5) * (base_cost - cheapest_cost)

        available_df['sort_metric'] = abs(available_df['avg_cost'] - target_cost)
        candidates = available_df.sort_values(by='sort_metric').to_dict('records')
        target_metric_value = f"Target Cost: {target_cost:.6f}"

    else: # strength > 0.5
        # Interpolate by ELO (upwards from base)
        base_elo = base_model['coding_arena_elo']
        highest_elo_model = available_df.loc[available_df['coding_arena_elo'].idxmax()]
        highest_elo = highest_elo_model['coding_arena_elo']

        if highest_elo <= base_elo: # Handle edge case where base has highest ELO
            target_elo = base_elo + (strength - 0.5) * (highest_elo - base_elo) # Will be >= base_elo
        else:
            # Interpolate between base and highest
            target_elo = base_elo + ((strength - 0.5) / 0.5) * (highest_elo - base_elo)

        available_df['sort_metric'] = abs(available_df['coding_arena_elo'] - target_elo)
        candidates = available_df.sort_values(by='sort_metric').to_dict('records')
        target_metric_value = f"Target ELO: {target_elo:.2f}"


    if not candidates:
         # This should ideally not happen if available_df was not empty
         raise RuntimeError("Model selection resulted in an empty candidate list.")

    # --- DEBUGGING PRINT ---
    if os.getenv("PDD_DEBUG_SELECTOR"): # Add env var check for debug prints
        logger.debug("\n--- DEBUG: _select_model_candidates ---")
        logger.debug(f"Strength: {strength}, Base Model: {base_model_name}")
        logger.debug(f"Metric: {target_metric_value}")
        logger.debug("Available DF (Sorted by metric):")
        # Select columns relevant to the sorting metric
        sort_cols = ['model', 'avg_cost', 'coding_arena_elo', 'sort_metric']
        logger.debug(available_df.sort_values(by='sort_metric')[sort_cols])
        logger.debug("Final Candidates List (Model Names):")
        logger.debug([c['model'] for c in candidates])
        logger.debug("---------------------------------------\n")
    # --- END DEBUGGING PRINT ---

    return candidates


def _sanitize_api_key(key_value: str) -> str:
    """
    Sanitize API key by removing whitespace and carriage returns.
    
    This fixes WSL environment issues where API keys may contain trailing \r characters
    that make them invalid for HTTP headers.
    
    Args:
        key_value: The raw API key value from environment
        
    Returns:
        Sanitized API key with whitespace and carriage returns removed
        
    Raises:
        ValueError: If the API key format is invalid after sanitization
    """
    if not key_value:
        return key_value
    
    # Strip all whitespace including carriage returns, newlines, etc.
    sanitized = key_value.strip()
    
    # Additional validation: ensure no remaining control characters
    if any(ord(c) < 32 for c in sanitized):
        logger.warning("API key contains control characters that may cause issues")
        # Remove any remaining control characters
        sanitized = ''.join(c for c in sanitized if ord(c) >= 32)
    
    # Validate API key format (basic checks)
    if sanitized:
        # Check for common API key patterns
        if len(sanitized) < 10:
            logger.warning(f"API key appears too short ({len(sanitized)} characters) - may be invalid")
        
        # Check for invalid characters in API keys (should be printable ASCII)
        if not all(32 <= ord(c) <= 126 for c in sanitized):
            logger.warning("API key contains non-printable characters")
            
        # Check for WSL-specific issues (detect if original had carriage returns)
        if key_value != sanitized and '\r' in key_value:
            if _is_wsl_environment():
                logger.info("Detected and fixed WSL line ending issue in API key")
            else:
                logger.info("Detected and fixed line ending issue in API key")
    
    return sanitized


def _save_key_to_env_file(key_name: str, value: str, env_path: Path) -> None:
    """Save or update a key in the .env file.

    - Replaces existing key in-place (no comment + append)
    - Removes old commented versions of the same key (Issue #183)
    - Preserves all other content
    """
    lines = []
    if env_path.exists():
        with open(env_path, 'r') as f:
            lines = f.readlines()

    new_lines = []
    key_replaced = False
    prefix = f"{key_name}="
    prefix_spaced = f"{key_name} ="

    for line in lines:
        stripped = line.strip()
        # Skip old commented versions of this key (cleanup accumulation)
        if stripped.startswith(f"# {prefix}") or stripped.startswith(f"# {prefix_spaced}"):
            continue
        elif stripped.startswith(prefix) or stripped.startswith(prefix_spaced):
            # Replace in-place
            new_lines.append(f'{key_name}="{value}"\n')
            key_replaced = True
        else:
            new_lines.append(line)

    # Add key if not found
    if not key_replaced:
        if new_lines and not new_lines[-1].endswith('\n'):
            new_lines.append('\n')
        new_lines.append(f'{key_name}="{value}"\n')

    with open(env_path, 'w') as f:
        f.writelines(new_lines)


def _ensure_api_key(model_info: Dict[str, Any], newly_acquired_keys: Dict[str, bool], verbose: bool) -> bool:
    """Checks for API key in env, prompts user if missing, and updates .env."""
    key_name = model_info.get('api_key')

    if not key_name or key_name == "EXISTING_KEY":
        if verbose:
            logger.info(f"Skipping API key check for model {model_info.get('model')} (key name: {key_name})")
        return True # Assume key is handled elsewhere or not needed

    key_value = os.getenv(key_name)
    if key_value:
        key_value = _sanitize_api_key(key_value)

    if key_value:
        if verbose:
            logger.info(f"API key '{key_name}' found in environment.")
        newly_acquired_keys[key_name] = False # Mark as existing
        return True
    else:
        logger.warning(f"API key environment variable '{key_name}' for model '{model_info.get('model')}' is not set.")

        # Skip prompting if --force flag is set (non-interactive mode)
        if os.environ.get('PDD_FORCE'):
            logger.error(f"API key '{key_name}' not set. In --force mode, skipping interactive prompt.")
            return False

        try:
            # Interactive prompt
            user_provided_key = input(f"Please enter the API key for {key_name}: ").strip()
            if not user_provided_key:
                logger.error("No API key provided. Cannot proceed with this model.")
                return False

            # Sanitize the user-provided key
            user_provided_key = _sanitize_api_key(user_provided_key)
            
            # Set environment variable for the current process
            os.environ[key_name] = user_provided_key
            logger.info(f"API key '{key_name}' set for the current session.")
            newly_acquired_keys[key_name] = True # Mark as newly acquired

            # Update .env file
            try:
                _save_key_to_env_file(key_name, user_provided_key, ENV_PATH)
                logger.info(f"API key '{key_name}' saved to {ENV_PATH}.")
                logger.warning("SECURITY WARNING: The API key has been saved to your .env file. "
                       "Ensure this file is kept secure and is included in your .gitignore.")

            except IOError as e:
                logger.error(f"Failed to update .env file at {ENV_PATH}: {e}")
                # Continue since the key is set in the environment for this session

            return True

        except EOFError: # Handle non-interactive environments
             logger.error(f"Cannot prompt for API key '{key_name}' in a non-interactive environment.")
             return False
        except Exception as e:
             logger.error(f"An unexpected error occurred during API key acquisition: {e}")
             return False


def _format_messages(prompt: str, input_data: Union[Dict[str, Any], List[Dict[str, Any]]], use_batch_mode: bool) -> Union[List[Dict[str, str]], List[List[Dict[str, str]]]]:
    """Formats prompt and input into LiteLLM message format."""
    try:
        if use_batch_mode:
            if not isinstance(input_data, list):
                raise ValueError("input_json must be a list of dictionaries when use_batch_mode is True.")
            all_messages = []
            for item in input_data:
                if not isinstance(item, dict):
                     raise ValueError("Each item in input_json list must be a dictionary for batch mode.")
                formatted_prompt = prompt.format(**item)
                all_messages.append([{"role": "user", "content": formatted_prompt}])
            return all_messages
        else:
            if not isinstance(input_data, dict):
                raise ValueError("input_json must be a dictionary when use_batch_mode is False.")
            formatted_prompt = prompt.format(**input_data)
            return [{"role": "user", "content": formatted_prompt}]
    except KeyError as e:
        raise ValueError(f"Prompt formatting error: Missing key {e} in input_json for prompt string.") from e
    except Exception as e:
        raise ValueError(f"Error formatting prompt: {e}") from e

# --- JSON Extraction Helpers ---
import re

def _extract_fenced_json_block(text: str) -> Optional[str]:
    try:
        m = re.search(r"```json\s*(\{[\s\S]*?\})\s*```", text, flags=re.IGNORECASE)
        if m:
            return m.group(1)
        return None
    except Exception:
        return None

def _extract_balanced_json_objects(text: str) -> List[str]:
    results: List[str] = []
    brace_stack = 0
    start_idx = -1
    in_string = False
    escape = False
    for i, ch in enumerate(text):
        if in_string:
            if escape:
                escape = False
            elif ch == '\\':
                escape = True
            elif ch == '"':
                in_string = False
            continue
        else:
            if ch == '"':
                in_string = True
                continue
            if ch == '{':
                if brace_stack == 0:
                    start_idx = i
                brace_stack += 1
            elif ch == '}':
                if brace_stack > 0:
                    brace_stack -= 1
                    if brace_stack == 0 and start_idx != -1:
                        results.append(text[start_idx:i+1])
                        start_idx = -1
    return results


def _looks_like_python_code(s: str) -> bool:
    """
    Heuristic check if a string looks like Python code.

    Used to determine if we should attempt Python syntax repair on a string field.
    """
    if not s or len(s) < 10:
        return False
    # Check for common Python patterns
    code_indicators = ('def ', 'class ', 'import ', 'from ', 'if __name__', 'return ', 'print(')
    return any(indicator in s for indicator in code_indicators)


# Field names known to contain prose text, not Python code
# These are skipped during syntax validation to avoid false positives
_PROSE_FIELD_NAMES = frozenset({
    'reasoning',           # PromptAnalysis - completeness reasoning
    'explanation',         # TrimResultsOutput, FixerOutput - prose explanations
    'analysis',            # DiffAnalysis, CodePatchResult - analysis text
    'change_instructions', # ChangeInstruction, ConflictChange - instructions
    'change_description',  # DiffAnalysis - description of changes
    'planned_modifications', # CodePatchResult - modification plans
    'details',             # VerificationOutput - issue details
    'description',         # General prose descriptions
    'focus',               # Focus descriptions
})


def _is_prose_field_name(field_name: str) -> bool:
    """Check if a field name indicates it contains prose, not code.

    Used to skip syntax validation on prose fields that may contain
    Python keywords (like 'return' or 'import') but are not actual code.
    """
    return field_name.lower() in _PROSE_FIELD_NAMES


def _repair_python_syntax(code: str) -> str:
    """
    Validate Python code syntax and attempt repairs if invalid.

    Sometimes LLMs include spurious characters at string boundaries,
    especially when the code contains quotes. This function attempts
    to detect and repair such issues.

    Args:
        code: Python code string to validate/repair

    Returns:
        Repaired code if a fix was found, otherwise original code
    """
    import ast

    if not code or not code.strip():
        return code

    # First, try to parse as-is
    try:
        ast.parse(code)
        return code  # Valid, no repair needed
    except SyntaxError:
        pass

    # Try common repairs
    repaired = code

    # Repair 1: Trailing spurious quote (the specific issue we've seen)
    for quote in ['"', "'"]:
        if repaired.rstrip().endswith(quote):
            candidate = repaired.rstrip()[:-1]
            try:
                ast.parse(candidate)
                logger.info(f"[INFO] Repaired code by removing trailing {quote!r}")
                return candidate
            except SyntaxError:
                pass

    # Repair 2: Leading spurious quote
    for quote in ['"', "'"]:
        if repaired.lstrip().startswith(quote):
            candidate = repaired.lstrip()[1:]
            try:
                ast.parse(candidate)
                logger.info(f"[INFO] Repaired code by removing leading {quote!r}")
                return candidate
            except SyntaxError:
                pass

    # Repair 3: Both leading and trailing spurious quotes
    for quote in ['"', "'"]:
        stripped = repaired.strip()
        if stripped.startswith(quote) and stripped.endswith(quote):
            candidate = stripped[1:-1]
            try:
                ast.parse(candidate)
                logger.info(f"[INFO] Repaired code by removing surrounding {quote!r}")
                return candidate
            except SyntaxError:
                pass

    # If no repair worked, return original (let it fail downstream)
    return code


def _smart_unescape_code(code: str) -> str:
    """
    Unescape literal \\n sequences in code while preserving them inside string literals.

    When LLMs return code as JSON, newlines get double-escaped. After JSON parsing,
    we have literal backslash-n (2 chars) that should be actual newlines for code
    structure, BUT escape sequences inside Python strings (like print("\\n")) should
    remain as escape sequences.

    Args:
        code: Python code that may have literal \\n sequences

    Returns:
        Code with structural newlines unescaped but string literals preserved
    """
    LITERAL_BACKSLASH_N = '\\' + 'n'      # Literal \n (2 chars)

    if LITERAL_BACKSLASH_N not in code:
        return code

    # First, check if the code already has actual newlines (mixed state)
    # If it does, we need to be more careful
    has_actual_newlines = '\n' in code

    if not has_actual_newlines:
        # All newlines are escaped - this is the double-escaped case
        # We need to unescape them but preserve \n inside string literals

        # Strategy: Use a placeholder for \n inside strings, unescape all, then restore
        # We detect string literals by tracking quote state

        result = []
        i = 0
        in_string = False
        string_char = None
        in_fstring = False

        # Placeholder that won't appear in code
        PLACEHOLDER = '\x00NEWLINE_ESCAPE\x00'

        while i < len(code):
            # Check for escape sequences (both actual and literal)
            if i + 1 < len(code) and code[i] == '\\':
                next_char = code[i + 1]

                if in_string:
                    # Inside a string - preserve escape sequences
                    if next_char == 'n':
                        result.append(PLACEHOLDER)
                        i += 2
                        continue
                    elif next_char == 't':
                        result.append('\\' + 't')  # Keep \t as-is in strings
                        i += 2
                        continue
                    elif next_char == 'r':
                        result.append('\\' + 'r')  # Keep \r as-is in strings
                        i += 2
                        continue
                    elif next_char in ('"', "'", '\\'):
                        # Keep escaped quotes and backslashes
                        result.append(code[i:i+2])
                        i += 2
                        continue

            # Check for string delimiters
            if not in_string:
                # Check for triple quotes first
                if i + 2 < len(code) and code[i:i+3] in ('"""', "'''"):
                    in_string = True
                    string_char = code[i:i+3]
                    # Check if preceded by 'f' for f-string
                    in_fstring = i > 0 and code[i-1] == 'f'
                    result.append(code[i:i+3])
                    i += 3
                    continue
                elif code[i] in ('"', "'"):
                    in_string = True
                    string_char = code[i]
                    in_fstring = i > 0 and code[i-1] == 'f'
                    result.append(code[i])
                    i += 1
                    continue
            else:
                # Check for end of string
                if len(string_char) == 3:  # Triple quote
                    if i + 2 < len(code) and code[i:i+3] == string_char:
                        in_string = False
                        in_fstring = False
                        result.append(code[i:i+3])
                        i += 3
                        continue
                else:  # Single quote
                    if code[i] == string_char:
                        in_string = False
                        in_fstring = False
                        result.append(code[i])
                        i += 1
                        continue

            result.append(code[i])
            i += 1

        intermediate = ''.join(result)

        # Now unescape all remaining \n (these are structural)
        LITERAL_BACKSLASH_R_N = '\\' + 'r' + '\\' + 'n'
        LITERAL_BACKSLASH_T = '\\' + 't'

        intermediate = intermediate.replace(LITERAL_BACKSLASH_R_N, '\r\n')
        intermediate = intermediate.replace(LITERAL_BACKSLASH_N, '\n')
        intermediate = intermediate.replace(LITERAL_BACKSLASH_T, '\t')

        # Restore placeholders to \n (as escape sequences in strings)
        result_code = intermediate.replace(PLACEHOLDER, '\\n')

        return result_code
    else:
        # Mixed state - some actual newlines, some literal \n
        # This means the JSON parsing already converted some, but not all
        # The literal \n remaining are likely in strings, so leave them alone
        return code


def _unescape_code_newlines(obj: Any) -> Any:
    """
    Fix double-escaped newlines in Pydantic model string fields.

    Some models (e.g., Gemini) return JSON with \\\\n instead of \\n in code strings,
    resulting in literal backslash-n text instead of actual newlines after JSON parsing.
    This function recursively unescapes these in string fields of Pydantic models.

    Also repairs Python syntax errors in code-like string fields (e.g., trailing quotes).

    The check uses literal backslash-n (2 chars) vs actual newline (1 char):
    - '\\\\n' in Python source = literal backslash + n (2 chars) - needs fixing
    - '\\n' in Python source = newline character (1 char) - already correct

    Args:
        obj: A Pydantic model, dict, list, or primitive value

    Returns:
        The same object with string fields unescaped and code fields repaired
    """
    if obj is None:
        return obj

    def _process_string(s: str) -> str:
        """Process a string: unescape newlines and repair Python syntax if needed."""
        result = s
        # Smart unescape that preserves \n inside string literals
        if _looks_like_python_code(result):
            result = _smart_unescape_code(result)
            result = _repair_python_syntax(result)
        else:
            # For non-code strings, do simple unescape
            LITERAL_BACKSLASH_N = '\\' + 'n'
            LITERAL_BACKSLASH_R_N = '\\' + 'r' + '\\' + 'n'
            LITERAL_BACKSLASH_T = '\\' + 't'
            if LITERAL_BACKSLASH_N in result:
                result = result.replace(LITERAL_BACKSLASH_R_N, '\r\n')
                result = result.replace(LITERAL_BACKSLASH_N, '\n')
                result = result.replace(LITERAL_BACKSLASH_T, '\t')
        return result

    # Handle Pydantic models
    if isinstance(obj, BaseModel):
        # Get all field values and process strings
        for field_name in obj.model_fields:
            value = getattr(obj, field_name)
            if isinstance(value, str):
                processed = _process_string(value)
                if processed != value:
                    object.__setattr__(obj, field_name, processed)
            elif isinstance(value, (dict, list, BaseModel)):
                _unescape_code_newlines(value)
        return obj

    # Handle dicts
    if isinstance(obj, dict):
        for key, value in obj.items():
            if isinstance(value, str):
                obj[key] = _process_string(value)
            elif isinstance(value, (dict, list)):
                _unescape_code_newlines(value)
        return obj

    # Handle lists
    if isinstance(obj, list):
        for i, item in enumerate(obj):
            if isinstance(item, str):
                obj[i] = _process_string(item)
            elif isinstance(item, (dict, list, BaseModel)):
                _unescape_code_newlines(item)
        return obj

    return obj


def _has_invalid_python_code(obj: Any, field_name: str = "") -> bool:
    """
    Check if any code-like string fields have invalid Python syntax.

    This is used after _unescape_code_newlines to detect if repair failed
    and we should retry with cache disabled.

    Skips fields in _PROSE_FIELD_NAMES to avoid false positives on prose
    text that mentions code patterns (e.g., "ends on a return statement").

    Args:
        obj: A Pydantic model, dict, list, or primitive value
        field_name: The name of the field being validated (used to skip prose)

    Returns:
        True if there are invalid code fields that couldn't be repaired
    """
    import ast

    if obj is None:
        return False

    if isinstance(obj, str):
        # Skip validation for known prose fields
        if _is_prose_field_name(field_name):
            return False
        if _looks_like_python_code(obj):
            try:
                ast.parse(obj)
                return False  # Valid
            except SyntaxError:
                return True  # Invalid
        return False

    if isinstance(obj, BaseModel):
        for name in obj.model_fields:
            value = getattr(obj, name)
            if _has_invalid_python_code(value, field_name=name):
                return True
        return False

    if isinstance(obj, dict):
        for key, value in obj.items():
            fname = key if isinstance(key, str) else ""
            if _has_invalid_python_code(value, field_name=fname):
                return True
        return False

    if isinstance(obj, list):
        for item in obj:
            if _has_invalid_python_code(item, field_name=field_name):
                return True
        return False

    return False


# --- Main Function ---

def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = 0.5, # Use pdd.DEFAULT_STRENGTH if available, else 0.5
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    time: float = 0.25,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]] = None,
    language: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Runs a prompt with given input using LiteLLM, handling model selection,
    API key acquisition, structured output, batching, and reasoning time.
    The maximum completion token length defaults to the provider's maximum.

    Args:
        prompt: Prompt template string (required if messages is None).
        input_json: Dictionary or list of dictionaries for prompt variables (required if messages is None).
        strength: Model selection strength (0=cheapest, 0.5=base, 1=highest ELO).
        temperature: LLM temperature.
        verbose: Print detailed logs.
        output_pydantic: Optional Pydantic model for structured output.
        output_schema: Optional raw JSON schema dictionary for structured output (alternative to output_pydantic).
        time: Relative thinking time (0-1, default 0.25).
        use_batch_mode: Use batch completion if True.
        messages: Pre-formatted list of messages (or list of lists for batch). If provided, ignores prompt and input_json.

    Returns:
        Dictionary containing 'result', 'cost', 'model_name', 'thinking_output'.

    Raises:
        ValueError: For invalid inputs or prompt formatting errors.
        FileNotFoundError: If llm_model.csv is missing.
        RuntimeError: If all candidate models fail.
        openai.*Error: If LiteLLM encounters API errors after retries.
    """
    # Set verbose logging if requested
    set_verbose_logging(verbose)
    
    if verbose:
        logger.debug("llm_invoke start - Arguments received:")
        logger.debug(f"  prompt: {'provided' if prompt else 'None'}")
        logger.debug(f"  input_json: {'provided' if input_json is not None else 'None'}")
        logger.debug(f"  strength: {strength}")
        logger.debug(f"  temperature: {temperature}")
        logger.debug(f"  verbose: {verbose}")
        logger.debug(f"  output_pydantic: {output_pydantic.__name__ if output_pydantic else 'None'}")
        logger.debug(f"  time: {time}")
        logger.debug(f"  use_batch_mode: {use_batch_mode}")
        logger.debug(f"  messages: {'provided' if messages else 'None'}")

    # --- 1. Load Environment & Validate Inputs ---
    # .env loading happens at module level

    if messages:
        if verbose:
            logger.info("Using provided 'messages' input.")
        # Basic validation of messages format
        if use_batch_mode:
            if not isinstance(messages, list) or not all(isinstance(m_list, list) for m_list in messages):
                 raise ValueError("'messages' must be a list of lists when use_batch_mode is True.")
            if not all(isinstance(msg, dict) and 'role' in msg and 'content' in msg for m_list in messages for msg in m_list):
                 raise ValueError("Each message in the lists within 'messages' must be a dictionary with 'role' and 'content'.")
        else:
            if not isinstance(messages, list) or not all(isinstance(msg, dict) and 'role' in msg and 'content' in msg for msg in messages):
                 raise ValueError("'messages' must be a list of dictionaries with 'role' and 'content'.")
        formatted_messages = messages
    elif prompt and input_json is not None:
         if not isinstance(prompt, str) or not prompt:
             raise ValueError("'prompt' must be a non-empty string when 'messages' is not provided.")
         formatted_messages = _format_messages(prompt, input_json, use_batch_mode)
    else:
        raise ValueError("Either 'messages' or both 'prompt' and 'input_json' must be provided.")

    if not (0.0 <= strength <= 1.0):
        raise ValueError("'strength' must be between 0.0 and 1.0.")
    if not (0.0 <= temperature <= 2.0): # Common range for temperature
        warnings.warn("'temperature' is outside the typical range (0.0-2.0).")
    if not (0.0 <= time <= 1.0):
        raise ValueError("'time' must be between 0.0 and 1.0.")

    # --- 2. Load Model Data & Select Candidates ---
    try:
        model_df = _load_model_data(LLM_MODEL_CSV_PATH)
        candidate_models = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
    except (FileNotFoundError, ValueError, RuntimeError) as e:
        logger.error(f"Failed during model loading or selection: {e}")
        raise

    if verbose:
        # This print statement is crucial for the verbose test
        # Calculate and print strength for each candidate model
        # Find min/max for cost and ELO
        min_cost = model_df['avg_cost'].min()
        max_elo = model_df['coding_arena_elo'].max()
        base_cost = model_df[model_df['model'] == DEFAULT_BASE_MODEL]['avg_cost'].iloc[0] if not model_df[model_df['model'] == DEFAULT_BASE_MODEL].empty else min_cost
        base_elo = model_df[model_df['model'] == DEFAULT_BASE_MODEL]['coding_arena_elo'].iloc[0] if not model_df[model_df['model'] == DEFAULT_BASE_MODEL].empty else max_elo
        
        def calc_strength(candidate):
            # If strength < 0.5, interpolate by cost (cheaper = 0, base = 0.5)
            # If strength > 0.5, interpolate by ELO (base = 0.5, highest = 1.0)
            avg_cost = candidate.get('avg_cost', min_cost)
            elo = candidate.get('coding_arena_elo', base_elo)
            if strength < 0.5:
                # Map cost to [0, 0.5]
                if base_cost == min_cost:
                    return 0.5 # Avoid div by zero
                rel = (avg_cost - min_cost) / (base_cost - min_cost)
                return max(0.0, min(0.5, rel * 0.5))
            elif strength > 0.5:
                # Map ELO to [0.5, 1.0]
                if max_elo == base_elo:
                    return 0.5 # Avoid div by zero
                rel = (elo - base_elo) / (max_elo - base_elo)
                return max(0.5, min(1.0, 0.5 + rel * 0.5))
            else:
                return 0.5
        
        model_strengths_formatted = [(c['model'], f"{float(calc_strength(c)):.3f}") for c in candidate_models]
        logger.info("Candidate models selected and ordered (with strength): %s", model_strengths_formatted) # CORRECTED
        logger.info(f"Strength: {strength}, Temperature: {temperature}, Time: {time}")
        if use_batch_mode:
            logger.info("Batch mode enabled.")
        if output_pydantic:
            logger.info(f"Pydantic output requested: {output_pydantic.__name__}")
        try:
            # Only print input_json if it was actually provided (not when messages were used)
            if input_json is not None:
                logger.info("Input JSON:")
                logger.info(input_json) 
            else:
                 logger.info("Input: Using pre-formatted 'messages'.")
        except Exception:
            logger.info("Input JSON/Messages (fallback print):") 
            logger.info(input_json if input_json is not None else "[Messages provided directly]")


    # --- 3. Iterate Through Candidates and Invoke LLM ---
    last_exception = None
    newly_acquired_keys: Dict[str, bool] = {} # Track keys obtained in this run
    
    # Initialize variables for retry section
    response_format = None
    time_kwargs = {}

    # Update global rate map for callback cost fallback
    try:
        _set_model_rate_map(model_df)
    except Exception:
        pass

    for model_info in candidate_models:
        model_name_litellm = model_info['model']
        api_key_name = model_info.get('api_key')
        provider = model_info.get('provider', '').lower()

        if verbose:
            logger.info(f"\n[ATTEMPT] Trying model: {model_name_litellm} (Provider: {provider})")

        retry_with_same_model = True
        # Track per-model temperature adjustment attempt (avoid infinite loop)
        current_temperature = temperature
        temp_adjustment_done = False
        while retry_with_same_model:
            retry_with_same_model = False # Assume success unless auth error on new key

            # --- 4. API Key Check & Acquisition ---
            if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
                # Problem getting key, break inner loop, try next model candidate
                if verbose:
                    logger.info(f"[SKIP] Skipping {model_name_litellm} due to API key/credentials issue after prompt.")
                break # Breaks the 'while retry_with_same_model' loop

            # --- 5. Prepare LiteLLM Arguments ---
            litellm_kwargs: Dict[str, Any] = {
                "model": model_name_litellm,
                "messages": formatted_messages,
                # Use a local adjustable temperature to allow provider-specific fallbacks
                "temperature": current_temperature,
                # Retry on transient network errors (APIError, TimeoutError, ServiceUnavailableError)
                "num_retries": 2,
            }

            api_key_name_from_csv = model_info.get('api_key') # From CSV
            # Determine if it's a Vertex AI model for special handling
            is_vertex_model = (provider.lower() == 'google') or \
                              (provider.lower() == 'googlevertexai') or \
                              (provider.lower() == 'vertex_ai') or \
                              model_name_litellm.startswith('vertex_ai/')

            if is_vertex_model and api_key_name_from_csv == 'VERTEX_CREDENTIALS':
                credentials_file_path = os.getenv("VERTEX_CREDENTIALS") # Path from env var
                vertex_project_env = os.getenv("VERTEX_PROJECT")
                # Check for per-model location override, fall back to env var
                model_location = model_info.get('location')
                if pd.notna(model_location) and str(model_location).strip():
                    vertex_location_env = str(model_location).strip()
                    if verbose:
                        logger.info(f"[INFO] Using per-model location override: '{vertex_location_env}' for model '{model_name_litellm}'")
                else:
                    vertex_location_env = os.getenv("VERTEX_LOCATION")

                if credentials_file_path and vertex_project_env and vertex_location_env:
                    try:
                        with open(credentials_file_path, 'r') as f:
                            loaded_credentials = json.load(f)
                        vertex_credentials_json_string = json.dumps(loaded_credentials)
                        
                        litellm_kwargs["vertex_credentials"] = vertex_credentials_json_string
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.info(f"[INFO] For Vertex AI: using vertex_credentials from '{credentials_file_path}', project '{vertex_project_env}', location '{vertex_location_env}'.")
                    except FileNotFoundError:
                        # Still pass project and location so ADC can work
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.warning(f"[WARN] Vertex credentials file not found at '{credentials_file_path}'. Using ADC with project '{vertex_project_env}', location '{vertex_location_env}'.")
                    except json.JSONDecodeError:
                        # Still pass project and location so ADC can work
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.error(f"[ERROR] Failed to decode JSON from Vertex credentials file: '{credentials_file_path}'. Using ADC with project '{vertex_project_env}', location '{vertex_location_env}'.")
                    except Exception as e:
                        # Still pass project and location so ADC can work
                        litellm_kwargs["vertex_project"] = vertex_project_env
                        litellm_kwargs["vertex_location"] = vertex_location_env
                        if verbose:
                            logger.error(f"[ERROR] Failed to load Vertex credentials from '{credentials_file_path}': {e}. Using ADC with project '{vertex_project_env}', location '{vertex_location_env}'.")
                else:
                    if verbose:
                        logger.warning(f"[WARN] For Vertex AI (using '{api_key_name_from_csv}'): One or more required environment variables (VERTEX_CREDENTIALS, VERTEX_PROJECT, VERTEX_LOCATION) are missing.")
                        if not credentials_file_path: logger.warning(f"  Reason: VERTEX_CREDENTIALS (path to JSON file) env var not set or empty.")
                        if not vertex_project_env: logger.warning(f"  Reason: VERTEX_PROJECT env var not set or empty.")
                        if not vertex_location_env: logger.warning(f"  Reason: VERTEX_LOCATION env var not set or empty.")
                        logger.warning(f"  LiteLLM may attempt to use Application Default Credentials or the call may fail.")

            elif api_key_name_from_csv: # For other api_key_names specified in CSV (e.g., OPENAI_API_KEY, or a direct VERTEX_AI_API_KEY string)
                key_value = os.getenv(api_key_name_from_csv)
                if key_value:
                    key_value = _sanitize_api_key(key_value)
                    litellm_kwargs["api_key"] = key_value
                    if verbose:
                        logger.info(f"[INFO] Explicitly passing API key from env var '{api_key_name_from_csv}' as 'api_key' parameter to LiteLLM.")
                    
                    # If this model is Vertex AI AND uses a direct API key string (not VERTEX_CREDENTIALS from CSV),
                    # also pass project and location from env vars.
                    if is_vertex_model:
                        vertex_project_env = os.getenv("VERTEX_PROJECT")
                        # Check for per-model location override, fall back to env var
                        model_location = model_info.get('location')
                        if pd.notna(model_location) and str(model_location).strip():
                            vertex_location_env = str(model_location).strip()
                            if verbose:
                                logger.info(f"[INFO] Using per-model location override: '{vertex_location_env}' for model '{model_name_litellm}'")
                        else:
                            vertex_location_env = os.getenv("VERTEX_LOCATION")
                        if vertex_project_env and vertex_location_env:
                            litellm_kwargs["vertex_project"] = vertex_project_env
                            litellm_kwargs["vertex_location"] = vertex_location_env
                            if verbose:
                                logger.info(f"[INFO] For Vertex AI model (using direct API key '{api_key_name_from_csv}'), also passing vertex_project='{vertex_project_env}' and vertex_location='{vertex_location_env}' from env vars.")
                        elif verbose:
                             logger.warning(f"[WARN] For Vertex AI model (using direct API key '{api_key_name_from_csv}'), VERTEX_PROJECT or VERTEX_LOCATION env vars not set. This might be required by LiteLLM.")
                elif verbose: # api_key_name_from_csv was in CSV, but corresponding env var was not set/empty
                    logger.warning(f"[WARN] API key name '{api_key_name_from_csv}' found in CSV, but the environment variable '{api_key_name_from_csv}' is not set or empty. LiteLLM will use default authentication if applicable (e.g., other standard env vars or ADC).")
            
            elif verbose: # No api_key_name_from_csv in CSV for this model
                logger.info(f"[INFO] No API key name specified in CSV for model '{model_name_litellm}'. LiteLLM will use its default authentication mechanisms (e.g., standard provider env vars or ADC for Vertex AI).")

            # Add base_url/api_base override if present in CSV
            api_base = model_info.get('base_url')
            if pd.notna(api_base) and api_base:
                # LiteLLM prefers `base_url`; some older paths accept `api_base`.
                litellm_kwargs["base_url"] = str(api_base)
                litellm_kwargs["api_base"] = str(api_base)

            # Provider-specific defaults (e.g., LM Studio)
            model_name_lower = str(model_name_litellm).lower()
            provider_lower_for_model = provider.lower()
            is_lm_studio = model_name_lower.startswith('lm_studio/') or provider_lower_for_model == 'lm_studio'
            is_groq = model_name_lower.startswith('groq/') or provider_lower_for_model == 'groq'
            if is_lm_studio:
                # Ensure base_url is set (fallback to env LM_STUDIO_API_BASE or localhost)
                if not litellm_kwargs.get("base_url"):
                    lm_studio_base = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
                    litellm_kwargs["base_url"] = lm_studio_base
                    litellm_kwargs["api_base"] = lm_studio_base
                    if verbose:
                        logger.info(f"[INFO] Using LM Studio base_url: {lm_studio_base}")

                # Ensure a non-empty api_key; LM Studio accepts any non-empty token (e.g., 'lm-studio')
                if not litellm_kwargs.get("api_key"):
                    lm_studio_key = os.getenv("LM_STUDIO_API_KEY") or "lm-studio"
                    litellm_kwargs["api_key"] = lm_studio_key
                    if verbose:
                        logger.info("[INFO] Using LM Studio api_key placeholder (set LM_STUDIO_API_KEY to customize).")

            # Handle Structured Output (JSON Mode / Pydantic / JSON Schema)
            if output_pydantic or output_schema:
                # Check if model supports structured output based on CSV flag or LiteLLM check
                supports_structured = model_info.get('structured_output', False)
                # Optional: Add litellm.supports_response_schema check if CSV flag is unreliable
                # if not supports_structured:
                #     try: supports_structured = litellm.supports_response_schema(model=model_name_litellm)
                #     except: pass # Ignore errors in supports_response_schema check

                if supports_structured:
                    if output_pydantic:
                        if verbose:
                            logger.info(f"[INFO] Requesting structured output (Pydantic: {output_pydantic.__name__}) for {model_name_litellm}")
                        # Use explicit json_object format with response_schema for better Gemini/Vertex AI compatibility
                        # Passing Pydantic class directly may not trigger native structured output for all providers
                        response_format = {
                            "type": "json_object",
                            "response_schema": output_pydantic.model_json_schema()
                        }
                    else: # output_schema is set
                        if verbose:
                            logger.info(f"[INFO] Requesting structured output (JSON Schema) for {model_name_litellm}")
                        # LiteLLM expects {"type": "json_schema", "json_schema": {"name": "response", "schema": schema_dict, "strict": true}}
                        # OR for some providers just the schema dict if type is json_object.
                        # Best practice for broad compatibility via LiteLLM is usually the dict directly or wrapped.
                        # For now, let's assume we pass the schema dict as 'response_format' which LiteLLM handles for many providers
                        # or wrap it if needed. LiteLLM 1.40+ supports passing the dict directly for many.
                        response_format = {
                            "type": "json_schema",
                            "json_schema": {
                                "name": "response",
                                "schema": output_schema,
                                "strict": False
                            }
                        }
                    
                    litellm_kwargs["response_format"] = response_format

                    # LM Studio requires "json_schema" format, not "json_object"
                    # Use extra_body to bypass litellm.drop_params stripping the schema
                    if is_lm_studio and response_format and response_format.get("type") == "json_object":
                        schema = response_format.get("response_schema", {})
                        lm_studio_response_format = {
                            "type": "json_schema",
                            "json_schema": {
                                "name": "response",
                                "strict": True,
                                "schema": schema
                            }
                        }
                        # Use extra_body to bypass drop_params - passes directly to API
                        litellm_kwargs["extra_body"] = {"response_format": lm_studio_response_format}
                        # Remove from regular response_format to avoid conflicts
                        if "response_format" in litellm_kwargs:
                            del litellm_kwargs["response_format"]
                        if verbose:
                            logger.info(f"[INFO] Using extra_body for LM Studio response_format to bypass drop_params")

                    # Groq has issues with tool-based structured output - use JSON mode with schema in prompt
                    if is_groq and response_format:
                        # Get the schema to include in system prompt
                        if output_pydantic:
                            schema = output_pydantic.model_json_schema()
                        else:
                            schema = output_schema

                        # Use simple json_object mode (Groq's tool_use often fails)
                        litellm_kwargs["response_format"] = {"type": "json_object"}

                        # Prepend schema instruction to messages (json module is imported at top of file)
                        schema_instruction = f"You must respond with valid JSON matching this schema:\n```json\n{json.dumps(schema, indent=2)}\n```\nRespond ONLY with the JSON object, no other text."

                        # Find or create system message to prepend schema
                        messages_list = litellm_kwargs.get("messages", [])
                        if messages_list and messages_list[0].get("role") == "system":
                            messages_list[0]["content"] = schema_instruction + "\n\n" + messages_list[0]["content"]
                        else:
                            messages_list.insert(0, {"role": "system", "content": schema_instruction})
                        litellm_kwargs["messages"] = messages_list

                        if verbose:
                            logger.info(f"[INFO] Using JSON object mode with schema in prompt for Groq (avoiding tool_use issues)")

                    # As a fallback, one could use:
                    # litellm_kwargs["response_format"] = {"type": "json_object"}
                    # And potentially enable client-side validation:
                    # litellm.enable_json_schema_validation = True # Enable globally if needed
                else:
                    schema_name = output_pydantic.__name__ if output_pydantic else "JSON Schema"
                    if verbose:
                        logger.warning(f"[WARN] Model {model_name_litellm} does not support structured output via CSV flag. Output might not be valid {schema_name}.")
                    # Proceed without forcing JSON mode, parsing will be attempted later

            # --- NEW REASONING LOGIC ---
            reasoning_type = model_info.get('reasoning_type', 'none') # Defaults to 'none'
            max_reasoning_tokens_val = model_info.get('max_reasoning_tokens', 0) # Defaults to 0

            if time > 0: # Only apply reasoning if time is requested
                if reasoning_type == 'budget':
                    if max_reasoning_tokens_val > 0:
                        budget = int(time * max_reasoning_tokens_val)
                        if budget > 0:
                            # Currently known: Anthropic uses 'thinking'
                            # Model name comparison is more robust than provider string
                            if provider == 'anthropic': # Check provider column instead of model prefix
                                thinking_param = {"type": "enabled", "budget_tokens": budget}
                                litellm_kwargs["thinking"] = thinking_param
                                time_kwargs["thinking"] = thinking_param
                                if verbose:
                                    logger.info(f"[INFO] Requesting Anthropic thinking (budget type) with budget: {budget} tokens for {model_name_litellm}")
                            else:
                                # If other providers adopt a budget param recognized by LiteLLM, add here
                                if verbose:
                                    logger.warning(f"[WARN] Reasoning type is 'budget' for {model_name_litellm}, but no specific LiteLLM budget parameter known for this provider. Parameter not sent.")
                        elif verbose:
                            logger.info(f"[INFO] Calculated reasoning budget is 0 for {model_name_litellm}, skipping reasoning parameter.")
                    elif verbose:
                        logger.warning(f"[WARN] Reasoning type is 'budget' for {model_name_litellm}, but 'max_reasoning_tokens' is missing or zero in CSV. Reasoning parameter not sent.")

                elif reasoning_type == 'effort':
                    effort = "low"
                    if time > 0.7:
                        effort = "high"
                    elif time > 0.3:
                        effort = "medium"

                    # Map effort parameter per-provider/model family
                    model_lower = str(model_name_litellm).lower()
                    provider_lower = str(provider).lower()

                    if provider_lower == 'openai' and model_lower.startswith('gpt-5'):
                        # OpenAI 5-series uses Responses API with nested 'reasoning'
                        reasoning_obj = {"effort": effort, "summary": "auto"}
                        litellm_kwargs["reasoning"] = reasoning_obj
                        time_kwargs["reasoning"] = reasoning_obj
                        if verbose:
                            logger.info(f"[INFO] Requesting OpenAI reasoning.effort='{effort}' for {model_name_litellm} (Responses API)")

                    elif provider_lower == 'openai' and model_lower.startswith('o') and 'mini' not in model_lower:
                        # Historical o* models may use LiteLLM's generic reasoning_effort param
                        litellm_kwargs["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort
                        if verbose:
                            logger.info(f"[INFO] Requesting reasoning_effort='{effort}' for {model_name_litellm}")

                    else:
                        # Fallback to LiteLLM generic param when supported by provider adapter
                        litellm_kwargs["reasoning_effort"] = effort
                        time_kwargs["reasoning_effort"] = effort
                        if verbose:
                            logger.info(f"[INFO] Requesting generic reasoning_effort='{effort}' for {model_name_litellm}")

                elif reasoning_type == 'none':
                    if verbose:
                        logger.info(f"[INFO] Model {model_name_litellm} has reasoning_type='none'. No reasoning parameter sent.")

                else: # Unknown reasoning_type in CSV
                     if verbose:
                         logger.warning(f"[WARN] Unknown reasoning_type '{reasoning_type}' for model {model_name_litellm} in CSV. No reasoning parameter sent.")

            # --- END NEW REASONING LOGIC ---

            # Add caching control per call if needed (example: force refresh)
            # litellm_kwargs["cache"] = {"no-cache": True}

            # --- 6. LLM Invocation ---
            try:
                start_time = time_module.time()

                # Log cache status with proper logging
                logger.debug(f"Cache Check: litellm.cache is None: {litellm.cache is None}")
                if litellm.cache is not None:
                    logger.debug(f"litellm.cache type: {type(litellm.cache)}, ID: {id(litellm.cache)}")

                # Only add if litellm.cache is configured
                if litellm.cache is not None:
                    litellm_kwargs["caching"] = True
                    logger.debug("Caching enabled for this request")
                else:
                    logger.debug("NOT ENABLING CACHING: litellm.cache is None at call time")


                # Route OpenAI gpt-5* models through Responses API to support 'reasoning'
                model_lower_for_call = str(model_name_litellm).lower()
                provider_lower_for_call = str(provider).lower()

                if (
                    not use_batch_mode
                    and provider_lower_for_call == 'openai'
                    and model_lower_for_call.startswith('gpt-5')
                ):
                    if verbose:
                        logger.info(f"[INFO] Calling LiteLLM Responses API for {model_name_litellm}...")
                    try:
                        # Build input text from messages
                        if isinstance(formatted_messages, list) and formatted_messages and isinstance(formatted_messages[0], dict):
                            input_text = "\n\n".join(f"{m.get('role','user')}: {m.get('content','')}" for m in formatted_messages)
                        else:
                            # Fallback: string cast
                            input_text = str(formatted_messages)

                        # Derive effort mapping already computed in time_kwargs
                        reasoning_param = time_kwargs.get("reasoning")

                        # Build text.format block for structured output
                        # Default to plain text format
                        text_block = {"format": {"type": "text"}}

                        # If structured output requested, use text.format with json_schema
                        # This is the correct way to enforce structured output via litellm.responses()
                        if output_pydantic or output_schema:
                            try:
                                if output_pydantic:
                                    schema = output_pydantic.model_json_schema()
                                    name = output_pydantic.__name__
                                else:
                                    schema = output_schema
                                    name = "response"

                                # Add additionalProperties: false for strict mode (required by OpenAI)
                                schema['additionalProperties'] = False

                                # Use text.format with json_schema for structured output
                                text_block = {
                                    "format": {
                                        "type": "json_schema",
                                        "name": name,
                                        "strict": True,
                                        "schema": schema,
                                    }
                                }
                                if verbose:
                                    logger.info(f"[INFO] Using structured output via text.format for Responses API")
                            except Exception as schema_e:
                                logger.warning(f"[WARN] Failed to derive JSON schema: {schema_e}. Proceeding with plain text format.")

                        # Build kwargs for litellm.responses()
                        responses_kwargs = {
                            "model": model_name_litellm,
                            "input": input_text,
                            "text": text_block,
                        }
                        if verbose and temperature not in (None, 0, 0.0):
                            logger.info("[INFO] Skipping 'temperature' for OpenAI GPT-5 Responses call (unsupported by API).")
                        if reasoning_param is not None:
                            responses_kwargs["reasoning"] = reasoning_param

                        # Call litellm.responses() which handles the API interaction
                        resp = litellm.responses(**responses_kwargs)

                        # Extract text result from response
                        result_text = None
                        try:
                            # LiteLLM responses return output as a list of items
                            for item in resp.output:
                                if getattr(item, 'type', None) == 'message' and hasattr(item, 'content') and item.content:
                                    for content_item in item.content:
                                        if hasattr(content_item, 'text'):
                                            result_text = content_item.text
                                            break
                                    if result_text:
                                        break
                        except Exception:
                            result_text = None

                        # Calculate cost using usage + CSV rates
                        total_cost = 0.0
                        usage = getattr(resp, "usage", None)
                        if usage is not None:
                            in_tok = getattr(usage, "input_tokens", 0) or 0
                            out_tok = getattr(usage, "output_tokens", 0) or 0
                            in_rate = model_info.get('input', 0.0) or 0.0
                            out_rate = model_info.get('output', 0.0) or 0.0
                            total_cost = (in_tok * in_rate + out_tok * out_rate) / 1_000_000.0

                        # Parse result if Pydantic output requested
                        final_result = None
                        if output_pydantic and result_text:
                            try:
                                final_result = output_pydantic.model_validate_json(result_text)
                            except Exception as e:
                                # With structured output, parsing should succeed
                                # But if it fails, try JSON repair as fallback
                                logger.warning(f"[WARN] Pydantic parse failed on Responses output: {e}. Attempting JSON repair...")

                                # Try extracting from fenced JSON blocks first
                                fenced = _extract_fenced_json_block(result_text)
                                candidates: List[str] = []
                                if fenced:
                                    candidates.append(fenced)
                                else:
                                    candidates.extend(_extract_balanced_json_objects(result_text))

                                # Also try the raw text as-is after stripping fences
                                cleaned = result_text.strip()
                                if cleaned.startswith("```json"):
                                    cleaned = cleaned[7:]
                                elif cleaned.startswith("```"):
                                    cleaned = cleaned[3:]
                                if cleaned.endswith("```"):
                                    cleaned = cleaned[:-3]
                                cleaned = cleaned.strip()
                                if cleaned and cleaned not in candidates:
                                    candidates.append(cleaned)

                                parse_succeeded = False
                                for cand in candidates:
                                    try:
                                        final_result = output_pydantic.model_validate_json(cand)
                                        parse_succeeded = True
                                        logger.info(f"[SUCCESS] JSON repair succeeded for Responses output")
                                        break
                                    except Exception:
                                        continue

                                if not parse_succeeded:
                                    logger.error(f"[ERROR] All JSON repair attempts failed for Responses output. Original error: {e}")
                                    final_result = f"ERROR: Failed to parse structured output from Responses API. Raw: {repr(result_text)[:200]}"
                        else:
                            final_result = result_text

                        if verbose:
                            logger.info(f"[RESULT] Model Used: {model_name_litellm}")
                            logger.info(f"[RESULT] Total Cost (estimated): ${total_cost:.6g}")

                        return {
                            'result': final_result,
                            'cost': total_cost,
                            'model_name': model_name_litellm,
                            'thinking_output': None,
                        }
                    except Exception as e:
                        last_exception = e
                        logger.error(f"[ERROR] OpenAI Responses call failed for {model_name_litellm}: {e}")
                        # Remove 'reasoning' key to avoid OpenAI Chat API unknown param errors
                        if "reasoning" in litellm_kwargs:
                            try:
                                litellm_kwargs.pop("reasoning", None)
                            except Exception:
                                pass
                        # Fall through to LiteLLM path as a fallback

                if use_batch_mode:
                    if verbose:
                        logger.info(f"[INFO] Calling litellm.batch_completion for {model_name_litellm}...")
                    response = litellm.batch_completion(**litellm_kwargs)


                else:
                    # Anthropic requirement: when 'thinking' is enabled, temperature must be 1
                    try:
                        if provider.lower() == 'anthropic' and 'thinking' in litellm_kwargs:
                            if litellm_kwargs.get('temperature') != 1:
                                if verbose:
                                    logger.info("[INFO] Anthropic thinking enabled: forcing temperature=1 for compliance.")
                                litellm_kwargs['temperature'] = 1
                                current_temperature = 1
                    except Exception:
                        pass
                    if verbose:
                        logger.info(f"[INFO] Calling litellm.completion for {model_name_litellm}...")
                    response = litellm.completion(**litellm_kwargs)

                end_time = time_module.time()

                if verbose:
                    logger.info(f"[SUCCESS] Invocation successful for {model_name_litellm} (took {end_time - start_time:.2f}s)")

                # Build retry kwargs with provider credentials from litellm_kwargs
                # Issue #185: Retry calls were missing vertex_location, vertex_project, etc.
                retry_provider_kwargs = {k: v for k, v in litellm_kwargs.items()
                                         if k in ('vertex_credentials', 'vertex_project', 'vertex_location',
                                                  'api_key', 'base_url', 'api_base')}

                # --- 7. Process Response ---
                results = []
                thinking_outputs = []

                response_list = response if use_batch_mode else [response]

                for i, resp_item in enumerate(response_list):
                    # Cost calculation is handled entirely by the success callback

                    # Thinking Output
                    thinking = None
                    try:
                        # Attempt 1: Check _hidden_params based on isolated test script
                        if hasattr(resp_item, '_hidden_params') and resp_item._hidden_params and 'thinking' in resp_item._hidden_params:
                             thinking = resp_item._hidden_params['thinking']
                             if verbose:
                                 logger.debug("[DEBUG] Extracted thinking output from response._hidden_params['thinking']")
                        # Attempt 2: Fallback to reasoning_content in message
                        # Use .get() for safer access
                        elif hasattr(resp_item, 'choices') and resp_item.choices and hasattr(resp_item.choices[0], 'message') and hasattr(resp_item.choices[0].message, 'get') and resp_item.choices[0].message.get('reasoning_content'):
                            thinking = resp_item.choices[0].message.get('reasoning_content')
                            if verbose:
                                logger.debug("[DEBUG] Extracted thinking output from response.choices[0].message.get('reasoning_content')")

                    except (AttributeError, IndexError, KeyError, TypeError):
                        if verbose:
                            logger.debug("[DEBUG] Failed to extract thinking output from known locations.")
                        pass # Ignore if structure doesn't match or errors occur
                    thinking_outputs.append(thinking)

                    # Result (String or Pydantic)
                    try:
                        raw_result = resp_item.choices[0].message.content
                        
                        # Check if raw_result is None (likely cached corrupted data)
                        if raw_result is None:
                            logger.warning(f"[WARNING] LLM returned None content for item {i}, likely due to corrupted cache. Retrying with cache bypass...")
                            # Retry with cache bypass by modifying the prompt slightly
                            if not use_batch_mode and prompt and input_json is not None:
                                # Add a small space to bypass cache
                                modified_prompt = prompt + " "
                                try:
                                    retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                    # Disable cache for retry
                                    litellm.cache = None
                                    retry_response = litellm.completion(
                                        model=model_name_litellm,
                                        messages=retry_messages,
                                        temperature=current_temperature,
                                        response_format=response_format,
                                        **time_kwargs,
                                        **retry_provider_kwargs  # Issue #185: Pass Vertex AI credentials
                                    )
                                    # Re-enable cache - restore original configured cache (restore to original state, even if None)
                                    litellm.cache = configured_cache
                                    # Extract result from retry
                                    retry_raw_result = retry_response.choices[0].message.content
                                    if retry_raw_result is not None:
                                        logger.info(f"[SUCCESS] Cache bypass retry succeeded for item {i}")
                                        raw_result = retry_raw_result
                                    else:
                                        logger.error(f"[ERROR] Cache bypass retry also returned None for item {i}")
                                        results.append("ERROR: LLM returned None content even after cache bypass")
                                        continue
                                except Exception as retry_e:
                                    logger.error(f"[ERROR] Cache bypass retry failed for item {i}: {retry_e}")
                                    results.append(f"ERROR: LLM returned None content and retry failed: {retry_e}")
                                    continue
                            else:
                                logger.error(f"[ERROR] Cannot retry - batch mode or missing prompt/input_json")
                                results.append("ERROR: LLM returned None content and cannot retry")
                                continue

                        # Check for malformed JSON response (excessive trailing newlines causing truncation)
                        # This can happen when Gemini generates thousands of \n in JSON string values
                        if isinstance(raw_result, str) and _is_malformed_json_response(raw_result):
                            logger.warning(f"[WARNING] Detected malformed JSON response with excessive trailing newlines for item {i}. Retrying with cache bypass...")
                            if not use_batch_mode and prompt and input_json is not None:
                                # Add a small space to bypass cache
                                modified_prompt = prompt + " "
                                try:
                                    retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                    # Disable cache for retry
                                    original_cache = litellm.cache
                                    litellm.cache = None
                                    retry_response = litellm.completion(
                                        model=model_name_litellm,
                                        messages=retry_messages,
                                        temperature=current_temperature,
                                        response_format=response_format,
                                        **time_kwargs,
                                        **retry_provider_kwargs  # Issue #185: Pass Vertex AI credentials
                                    )
                                    # Re-enable cache
                                    litellm.cache = original_cache
                                    # Extract result from retry
                                    retry_raw_result = retry_response.choices[0].message.content
                                    if retry_raw_result is not None and not _is_malformed_json_response(retry_raw_result):
                                        logger.info(f"[SUCCESS] Cache bypass retry for malformed JSON succeeded for item {i}")
                                        raw_result = retry_raw_result
                                    else:
                                        # Retry also failed, but we'll continue with repair logic below
                                        logger.warning(f"[WARNING] Cache bypass retry also returned malformed JSON for item {i}, attempting repair...")
                                except Exception as retry_e:
                                    logger.warning(f"[WARNING] Cache bypass retry for malformed JSON failed for item {i}: {retry_e}, attempting repair...")
                            else:
                                logger.warning(f"[WARNING] Cannot retry malformed JSON - batch mode or missing prompt/input_json, attempting repair...")

                        if output_pydantic or output_schema:
                            parsed_result = None
                            json_string_to_parse = None

                            try:
                                # Attempt 1: Check if LiteLLM already parsed it (only for Pydantic)
                                if output_pydantic and isinstance(raw_result, output_pydantic):
                                    parsed_result = raw_result
                                    if verbose:
                                        logger.debug("[DEBUG] Pydantic object received directly from LiteLLM.")

                                # Attempt 2: Check if raw_result is dict-like and validate
                                elif isinstance(raw_result, dict):
                                    if output_pydantic:
                                        parsed_result = output_pydantic.model_validate(raw_result)
                                    else:
                                        # Validate against JSON schema
                                        try:
                                            import jsonschema
                                            jsonschema.validate(instance=raw_result, schema=output_schema)
                                            parsed_result = json.dumps(raw_result) # Return as JSON string for consistency
                                        except ImportError:
                                            logger.warning("jsonschema not installed, skipping validation")
                                            parsed_result = json.dumps(raw_result)
                                    
                                    if verbose:
                                        logger.debug("[DEBUG] Validated dictionary-like object directly.")

                                # Attempt 3: Process as string (if not already parsed/validated)
                                elif isinstance(raw_result, str):
                                    json_string_to_parse = raw_result # Start with the raw string
                                    try:
                                        # 1) Prefer fenced ```json blocks
                                        fenced = _extract_fenced_json_block(raw_result)
                                        candidates: List[str] = []
                                        if fenced:
                                            candidates.append(fenced)
                                        else:
                                            # 2) Fall back to scanning for balanced JSON objects
                                            candidates.extend(_extract_balanced_json_objects(raw_result))

                                        if not candidates:
                                            raise ValueError("No JSON-like content found")

                                        parse_err: Optional[Exception] = None
                                        for cand in candidates:
                                            try:
                                                if verbose:
                                                    logger.debug(f"[DEBUG] Attempting to parse candidate JSON block: {cand}")
                                                
                                                if output_pydantic:
                                                    parsed_result = output_pydantic.model_validate_json(cand)
                                                else:
                                                    # Parse JSON and validate against schema
                                                    loaded = json.loads(cand)
                                                    try:
                                                        import jsonschema
                                                        jsonschema.validate(instance=loaded, schema=output_schema)
                                                    except ImportError:
                                                        pass # Skip validation if lib missing
                                                    parsed_result = cand # Return string if valid

                                                json_string_to_parse = cand
                                                parse_err = None
                                                break
                                            except (json.JSONDecodeError, ValidationError, ValueError) as pe:
                                                # Also catch jsonschema.ValidationError if imported
                                                parse_err = pe
                                                try:
                                                    import jsonschema
                                                    if isinstance(pe, jsonschema.ValidationError):
                                                        parse_err = pe
                                                except ImportError:
                                                    pass

                                        if parsed_result is None:
                                            # If none of the candidates parsed, raise last error
                                            if parse_err is not None:
                                                raise parse_err
                                            raise ValueError("Unable to parse any JSON candidates")
                                    except (json.JSONDecodeError, ValidationError, ValueError, Exception) as extraction_error:
                                        # Catch generic Exception to handle jsonschema errors without explicit import here
                                        if verbose:
                                            logger.debug(f"[DEBUG] JSON extraction/validation failed ('{extraction_error}'). Trying fence cleaning.")
                                        # Last resort: strip any leading/trailing code fences and retry
                                        cleaned_result_str = raw_result.strip()
                                        if cleaned_result_str.startswith("```json"):
                                            cleaned_result_str = cleaned_result_str[7:]
                                        elif cleaned_result_str.startswith("```"):
                                            cleaned_result_str = cleaned_result_str[3:]
                                        if cleaned_result_str.endswith("```"):
                                            cleaned_result_str = cleaned_result_str[:-3]
                                        cleaned_result_str = cleaned_result_str.strip()
                                        # Check for complete JSON object or array
                                        is_complete_object = cleaned_result_str.startswith('{') and cleaned_result_str.endswith('}')
                                        is_complete_array = cleaned_result_str.startswith('[') and cleaned_result_str.endswith(']')
                                        if is_complete_object or is_complete_array:
                                            if verbose:
                                                logger.debug(f"[DEBUG] Attempting parse after generic fence cleaning. Cleaned string: '{cleaned_result_str}'")
                                            json_string_to_parse = cleaned_result_str

                                            if output_pydantic:
                                                parsed_result = output_pydantic.model_validate_json(json_string_to_parse)
                                            else:
                                                loaded = json.loads(json_string_to_parse)
                                                try:
                                                    import jsonschema
                                                    jsonschema.validate(instance=loaded, schema=output_schema)
                                                except ImportError:
                                                    pass
                                                parsed_result = json_string_to_parse
                                        elif cleaned_result_str.startswith('{') or cleaned_result_str.startswith('['):
                                            # Attempt to repair truncated JSON (e.g., missing closing braces)
                                            # This can happen when Gemini generates excessive trailing content
                                            # that causes token limit truncation
                                            if verbose:
                                                logger.debug(f"[DEBUG] JSON appears truncated (missing closing brace). Attempting repair.")

                                            # Try to find the last valid JSON structure
                                            # For simple schemas like {"extracted_code": "..."}, we can try to close it
                                            repaired = cleaned_result_str.rstrip()

                                            # Strip trailing escaped newline sequences (\\n in the JSON string)
                                            # These appear as literal backslash-n when Gemini generates excessive newlines
                                            while repaired.endswith('\\n'):
                                                repaired = repaired[:-2]
                                            # Also strip trailing literal backslashes that might be orphaned
                                            repaired = repaired.rstrip('\\')

                                            # If we're in the middle of a string value, try to close it
                                            # Count unescaped quotes to determine if we're inside a string
                                            # Simple heuristic: if it ends without proper closure, add closing
                                            is_array = cleaned_result_str.startswith('[')
                                            expected_end = ']' if is_array else '}'
                                            if not repaired.endswith(expected_end):
                                                # Try adding various closures to repair
                                                if is_array:
                                                    repair_attempts = [
                                                        repaired + '}]',  # Close object and array
                                                        repaired + '"}]',  # Close string, object and array
                                                        repaired + '"}}]',  # Close string, nested object and array
                                                        repaired.rstrip(',') + ']',  # Remove trailing comma and close array
                                                        repaired.rstrip('"') + '"}]',  # Handle partial string end
                                                    ]
                                                else:
                                                    repair_attempts = [
                                                        repaired + '"}',  # Close string and object
                                                        repaired + '"}\n}',  # Close string and nested object
                                                        repaired + '"}}}',  # Deeper nesting
                                                        repaired.rstrip(',') + '}',  # Remove trailing comma
                                                        repaired.rstrip('"') + '"}',  # Handle partial string end
                                                    ]

                                                for attempt in repair_attempts:
                                                    try:
                                                        if output_pydantic:
                                                            parsed_result = output_pydantic.model_validate_json(attempt)
                                                        else:
                                                            loaded = json.loads(attempt)
                                                            try:
                                                                import jsonschema
                                                                jsonschema.validate(instance=loaded, schema=output_schema)
                                                            except ImportError:
                                                                pass
                                                            parsed_result = attempt

                                                        if verbose:
                                                            logger.info(f"[INFO] Successfully repaired truncated JSON response")
                                                        json_string_to_parse = attempt
                                                        break
                                                    except (json.JSONDecodeError, ValidationError, ValueError):
                                                        continue

                                                if parsed_result is None:
                                                    raise ValueError("Content after cleaning doesn't look like JSON (and repair attempts failed)")
                                        else:
                                            raise ValueError("Content after cleaning doesn't look like JSON")


                                # Check if any parsing attempt succeeded
                                if parsed_result is None:
                                    target_name = output_pydantic.__name__ if output_pydantic else "JSON Schema"
                                    # This case should ideally be caught by exceptions above, but as a safeguard:
                                    raise TypeError(f"Raw result type {type(raw_result)} or content could not be validated/parsed against {target_name}.")

                            except (ValidationError, json.JSONDecodeError, TypeError, ValueError, Exception) as parse_error:
                                target_name = output_pydantic.__name__ if output_pydantic else "JSON Schema"
                                logger.error(f"[ERROR] Failed to parse response into {target_name} for item {i}: {parse_error}")
                                # Use the string that was last attempted for parsing in the error message
                                error_content = json_string_to_parse if json_string_to_parse is not None else raw_result
                                logger.error("[ERROR] Content attempted for parsing: %s", repr(error_content))
                                # Issue #168: Raise SchemaValidationError to trigger model fallback
                                # Previously this used `continue` which only skipped to the next batch item
                                raise SchemaValidationError(
                                    f"Failed to parse response into {target_name}: {parse_error}",
                                    raw_response=raw_result,
                                    item_index=i
                                ) from parse_error

                            # Post-process: unescape newlines and repair Python syntax
                            _unescape_code_newlines(parsed_result)

                            # Check if code fields still have invalid Python syntax after repair
                            # If so, retry without cache to get a fresh response
                            # Skip validation for non-Python languages to avoid false positives
                            if language in (None, "python") and _has_invalid_python_code(parsed_result):
                                logger.warning(f"[WARNING] Detected invalid Python syntax in code fields for item {i} after repair. Retrying with cache bypass...")
                                if not use_batch_mode and prompt and input_json is not None:
                                    # Add a small variation to bypass cache
                                    modified_prompt = prompt + "  "  # Two spaces to differentiate from other retries
                                    try:
                                        retry_messages = _format_messages(modified_prompt, input_json, use_batch_mode)
                                        # Disable cache for retry
                                        original_cache = litellm.cache
                                        litellm.cache = None
                                        retry_response = litellm.completion(
                                            model=model_name_litellm,
                                            messages=retry_messages,
                                            temperature=current_temperature,
                                            response_format=response_format,
                                            **time_kwargs,
                                            **retry_provider_kwargs  # Issue #185: Pass Vertex AI credentials
                                        )
                                        # Re-enable cache
                                        litellm.cache = original_cache
                                        # Extract and re-parse the retry result
                                        retry_raw_result = retry_response.choices[0].message.content
                                        if retry_raw_result is not None:
                                            # Re-parse the retry result
                                            retry_parsed = None
                                            if output_pydantic:
                                                if isinstance(retry_raw_result, output_pydantic):
                                                    retry_parsed = retry_raw_result
                                                elif isinstance(retry_raw_result, dict):
                                                    retry_parsed = output_pydantic.model_validate(retry_raw_result)
                                                elif isinstance(retry_raw_result, str):
                                                    retry_parsed = output_pydantic.model_validate_json(retry_raw_result)
                                            elif output_schema and isinstance(retry_raw_result, str):
                                                retry_parsed = retry_raw_result  # Keep as string for schema validation

                                            if retry_parsed is not None:
                                                _unescape_code_newlines(retry_parsed)
                                                if not _has_invalid_python_code(retry_parsed):
                                                    logger.info(f"[SUCCESS] Cache bypass retry for invalid Python code succeeded for item {i}")
                                                    parsed_result = retry_parsed
                                                else:
                                                    logger.warning(f"[WARNING] Cache bypass retry still has invalid Python code for item {i}, using original")
                                            else:
                                                logger.warning(f"[WARNING] Cache bypass retry returned unparseable result for item {i}")
                                        else:
                                            logger.warning(f"[WARNING] Cache bypass retry returned None for item {i}")
                                    except Exception as retry_e:
                                        logger.warning(f"[WARNING] Cache bypass retry for invalid Python code failed for item {i}: {retry_e}")
                                else:
                                    logger.warning(f"[WARNING] Cannot retry invalid Python code - batch mode or missing prompt/input_json")

                            results.append(parsed_result)

                        else:
                            # If output_pydantic/schema was not requested, append the raw result
                            results.append(raw_result)

                    except (AttributeError, IndexError) as e:
                         logger.error(f"[ERROR] Could not extract result content from response item {i}: {e}")
                         results.append(f"ERROR: Could not extract result content. Response: {resp_item}")

                # --- Retrieve Cost from Callback Data --- (Reinstated)
                # For batch, this will reflect the cost associated with the *last* item processed by the callback.
                # A fully accurate batch total would require a more complex callback class to aggregate.
                total_cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
                # ----------------------------------------

                final_result = results if use_batch_mode else results[0]
                final_thinking = thinking_outputs if use_batch_mode else thinking_outputs[0]

                # --- Verbose Output for Success ---
                if verbose:
                    # Get token usage from the *last* callback data (might not be accurate for batch)
                    input_tokens = _LAST_CALLBACK_DATA.get("input_tokens", 0)
                    output_tokens = _LAST_CALLBACK_DATA.get("output_tokens", 0)

                    cost_input_pm = model_info.get('input', 0.0) if pd.notna(model_info.get('input')) else 0.0
                    cost_output_pm = model_info.get('output', 0.0) if pd.notna(model_info.get('output')) else 0.0

                    logger.info(f"[RESULT] Model Used: {model_name_litellm}")
                    logger.info(f"[RESULT] Cost (Input): ${cost_input_pm:.2f}/M tokens")
                    logger.info(f"[RESULT] Cost (Output): ${cost_output_pm:.2f}/M tokens")
                    logger.info(f"[RESULT] Tokens (Prompt): {input_tokens}")
                    logger.info(f"[RESULT] Tokens (Completion): {output_tokens}")
                    # Display the cost captured by the callback
                    logger.info(f"[RESULT] Total Cost (from callback): ${total_cost:.6g}") # Renamed label for clarity
                    logger.info("[RESULT] Max Completion Tokens: Provider Default") # Indicate default limit
                    if final_thinking:
                        logger.info("[RESULT] Thinking Output:")
                        logger.info(final_thinking) 

                # --- Print raw output before returning if verbose ---
                if verbose:
                    logger.debug("[DEBUG] Raw output before return:")
                    logger.debug(f"  Raw Result (repr): {repr(final_result)}")
                    logger.debug(f"  Raw Thinking (repr): {repr(final_thinking)}")
                    logger.debug("-" * 20) # Separator

                # --- Return Success ---
                return {
                    'result': final_result,
                    'cost': total_cost,
                    'model_name': model_name_litellm, # Actual model used
                    'thinking_output': final_thinking if final_thinking else None
                }

            # --- 6b. Handle Invocation Errors ---
            except openai.AuthenticationError as e:
                last_exception = e
                error_message = str(e)
                
                # Check for WSL-specific issues in authentication errors
                if _is_wsl_environment() and ('Illegal header value' in error_message or '\r' in error_message):
                    logger.warning(f"[WSL AUTH ERROR] Authentication failed for {model_name_litellm} - detected WSL line ending issue")
                    logger.warning("[WSL AUTH ERROR] This is likely caused by API key environment variables containing carriage returns")
                    logger.warning("[WSL AUTH ERROR] Try setting your API key again or check your .env file for line ending issues")
                    env_info = _get_environment_info()
                    logger.debug(f"Environment info: {env_info}")
                    
                if newly_acquired_keys.get(api_key_name):
                    logger.warning(f"[AUTH ERROR] Authentication failed for {model_name_litellm} with the newly provided key for '{api_key_name}'. Please check the key and try again.")
                    # Invalidate the key in env for this session to force re-prompt on retry
                    if api_key_name in os.environ:
                         del os.environ[api_key_name]
                    # Clear the 'newly acquired' status for this key so the next attempt doesn't trigger immediate retry loop
                    newly_acquired_keys[api_key_name] = False
                    retry_with_same_model = True # Set flag to retry the same model after re-prompt
                    # Go back to the start of the 'while retry_with_same_model' loop
                else:
                    logger.warning(f"[AUTH ERROR] Authentication failed for {model_name_litellm} using existing key '{api_key_name}'. Trying next model.")
                    break # Break inner loop, try next model candidate

            except SchemaValidationError as e:
                # Issue #168: Schema validation failures now trigger model fallback
                last_exception = e
                logger.warning(f"[SCHEMA ERROR] Validation failed for {model_name_litellm}: {e}. Trying next model.")
                if verbose:
                    logger.debug(f"Raw response that failed validation: {repr(e.raw_response)}")
                break  # Break inner loop, try next model candidate

            except (openai.RateLimitError, openai.APITimeoutError, openai.APIConnectionError,
                    openai.APIStatusError, openai.BadRequestError, openai.InternalServerError,
                    Exception) as e: # Catch generic Exception last
                last_exception = e
                error_type = type(e).__name__
                error_str = str(e)

                # Provider-specific handling for Anthropic temperature + thinking rules.
                # Two scenarios we auto-correct:
                # 1) temperature==1 without thinking -> retry with 0.99
                # 2) thinking enabled but temperature!=1 -> retry with 1
                lower_err = error_str.lower()
                if (not temp_adjustment_done) and ("temperature" in lower_err) and ("thinking" in lower_err):
                    anthropic_thinking_sent = ('thinking' in litellm_kwargs) and (provider.lower() == 'anthropic')
                    # Decide direction of adjustment based on whether thinking was enabled in the call
                    if anthropic_thinking_sent:
                        # thinking enabled -> force temperature=1
                        adjusted_temp = 1
                        logger.warning(
                            f"[WARN] {model_name_litellm}: Anthropic with thinking requires temperature=1. "
                            f"Retrying with temperature={adjusted_temp}."
                        )
                    else:
                        # thinking not enabled -> avoid temperature=1
                        adjusted_temp = 0.99
                        logger.warning(
                            f"[WARN] {model_name_litellm}: Provider rejected temperature=1 without thinking. "
                            f"Retrying with temperature={adjusted_temp}."
                        )
                    current_temperature = adjusted_temp
                    temp_adjustment_done = True
                    retry_with_same_model = True
                    if verbose:
                        logger.debug(f"Retrying {model_name_litellm} with adjusted temperature {current_temperature}")
                    continue

                logger.error(f"[ERROR] Invocation failed for {model_name_litellm} ({error_type}): {e}. Trying next model.")
                # Log more details in verbose mode
                if verbose:
                    logger.debug(f"Detailed exception traceback for {model_name_litellm}:", exc_info=True)
                break # Break inner loop, try next model candidate

        # If the inner loop was broken (not by success), continue to the next candidate model
        continue

    # --- 8. Handle Failure of All Candidates ---
    error_message = "All candidate models failed."
    if last_exception:
        error_message += f" Last error ({type(last_exception).__name__}): {last_exception}"
    logger.error(f"[FATAL] {error_message}")
    raise RuntimeError(error_message) from last_exception

# --- Example Usage (Optional) ---
if __name__ == "__main__":
    # This block allows running the file directly for testing.
    # Ensure you have a ./data/llm_model.csv file and potentially a .env file.

    # Set PDD_DEBUG_SELECTOR=1 to see model selection details
    # os.environ["PDD_DEBUG_SELECTOR"] = "1"

    # Example 1: Simple text generation
    logger.info("\n--- Example 1: Simple Text Generation (Strength 0.5) ---")
    try:
        response = llm_invoke(
            prompt="Tell me a short joke about {topic}.",
            input_json={"topic": "programmers"},
            strength=0.5, # Use base model (gpt-5-nano)
            temperature=0.7,
            verbose=True
        )
        logger.info("\nExample 1 Response:")
        logger.info(response)
    except Exception as e:
        logger.error(f"\nExample 1 Failed: {e}", exc_info=True)

    # Example 1b: Simple text generation (Strength 0.3)
    logger.info("\n--- Example 1b: Simple Text Generation (Strength 0.3) ---")
    try:
        response = llm_invoke(
            prompt="Tell me a short joke about {topic}.",
            input_json={"topic": "keyboards"},
            strength=0.3, # Should select gemini-pro based on cost interpolation
            temperature=0.7,
            verbose=True
        )
        logger.info("\nExample 1b Response:")
        logger.info(response)
    except Exception as e:
        logger.error(f"\nExample 1b Failed: {e}", exc_info=True)

    # Example 2: Structured output (requires a Pydantic model)
    logger.info("\n--- Example 2: Structured Output (Pydantic, Strength 0.8) ---")
    class JokeStructure(BaseModel):
        setup: str
        punchline: str
        rating: Optional[int] = None

    try:
        # Use a model known to support structured output (check your CSV)
        # Strength 0.8 should select gemini-pro based on ELO interpolation
        response_structured = llm_invoke(
            prompt="Create a joke about {topic}. Output ONLY the JSON object with 'setup' and 'punchline'.",
            input_json={"topic": "data science"},
            strength=0.8, # Try a higher ELO model (gemini-pro expected)
            temperature=1,
            output_pydantic=JokeStructure,
            verbose=True
        )
        logger.info("\nExample 2 Response:")
        logger.info(response_structured)
        if isinstance(response_structured.get('result'), JokeStructure):
             logger.info("\nPydantic object received successfully: %s", response_structured['result'].model_dump())
        else:
             logger.info("\nResult was not the expected Pydantic object: %s", response_structured.get('result'))

    except Exception as e:
        logger.error(f"\nExample 2 Failed: {e}", exc_info=True)


    # Example 3: Batch processing
    logger.info("\n--- Example 3: Batch Processing (Strength 0.3) ---")
    try:
        batch_input = [
            {"animal": "cat", "adjective": "lazy"},
            {"animal": "dog", "adjective": "energetic"},
        ]
        # Strength 0.3 should select gemini-pro
        response_batch = llm_invoke(
            prompt="Describe a {adjective} {animal} in one sentence.",
            input_json=batch_input,
            strength=0.3, # Cheaper model maybe (gemini-pro expected)
            temperature=0.5,
            use_batch_mode=True,
            verbose=True
        )
        logger.info("\nExample 3 Response:")
        logger.info(response_batch)
    except Exception as e:
        logger.error(f"\nExample 3 Failed: {e}", exc_info=True)

    # Example 4: Using 'messages' input
    logger.info("\n--- Example 4: Using 'messages' input (Strength 0.5) ---")
    try:
        custom_messages = [
            {"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": "What is the capital of France?"}
        ]
        # Strength 0.5 should select gpt-5-nano
        response_messages = llm_invoke(
            messages=custom_messages,
            strength=0.5,
            temperature=0.1,
            verbose=True
        )
        logger.info("\nExample 4 Response:")
        logger.info(response_messages)
    except Exception as e:
        logger.error(f"\nExample 4 Failed: {e}", exc_info=True)

    # Example 5: Requesting thinking time (e.g., for Anthropic)
    logger.info("\n--- Example 5: Requesting Thinking Time (Strength 1.0, Time 0.5) ---")
    try:
        # Ensure your CSV has max_reasoning_tokens for an Anthropic model
        # Strength 1.0 should select claude-3 (highest ELO)
        # Time 0.5 with budget type should request thinking
        response_thinking = llm_invoke(
            prompt="Explain the theory of relativity simply, taking some time to think.",
            input_json={},
            strength=1.0, # Try to get highest ELO model (claude-3)
            temperature=1,
            time=0.5, # Request moderate thinking time
            verbose=True
        )
        logger.info("\nExample 5 Response:")
        logger.info(response_thinking)
    except Exception as e:
        logger.error(f"\nExample 5 Failed: {e}", exc_info=True)

    # Example 6: Pydantic Fallback Parsing (Strength 0.3)
    logger.info("\n--- Example 6: Pydantic Fallback Parsing (Strength 0.3) ---")
    # This requires mocking litellm.completion to return a JSON string
    # even when gemini-pro (which supports structured output) is selected.
    # This is hard to demonstrate cleanly in the __main__ block without mocks.
    # The unit test test_llm_invoke_output_pydantic_unsupported_parses covers this.
    logger.info("(Covered by unit tests)")
