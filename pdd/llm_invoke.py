# Corrected code_under_test (llm_invoke.py)
# Added optional debugging prints in _select_model_candidates

import os
import pandas as pd
import litellm
import logging # ADDED FOR DETAILED LOGGING

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
from typing import Optional, Dict, List, Any, Type, Union
from pydantic import BaseModel, ValidationError
import openai  # Import openai for exception handling as LiteLLM maps to its types
from langchain_core.prompts import PromptTemplate
import warnings
import time as time_module # Alias to avoid conflict with 'time' parameter
# Import the default model constant
from pdd import DEFAULT_LLM_MODEL

# Opt-in to future pandas behavior regarding downcasting
pd.set_option('future.no_silent_downcasting', True)

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
        # Start from the directory containing this script
        current_dir = Path(__file__).resolve().parent
        # Look for project markers (e.g., .git, pyproject.toml, data/, .env)
        # Go up a maximum of 5 levels to prevent infinite loops
        for _ in range(5):
            has_git = (current_dir / ".git").exists()
            has_pyproject = (current_dir / "pyproject.toml").exists()
            has_data = (current_dir / "data").is_dir()
            has_dotenv = (current_dir / ".env").exists()

            if has_git or has_pyproject or has_data or has_dotenv:
                PROJECT_ROOT = current_dir
                logger.debug(f"Determined PROJECT_ROOT by marker search: {PROJECT_ROOT}")
                break

            parent_dir = current_dir.parent
            if parent_dir == current_dir: # Reached filesystem root
                break
            current_dir = parent_dir

    except NameError: # __file__ might not be defined (e.g., interactive session)
        warnings.warn("__file__ not defined. Cannot automatically detect project root from script location.")
    except Exception as e: # Catch potential permission errors etc.
        warnings.warn(f"Error during project root auto-detection: {e}")

if PROJECT_ROOT is None: # Fallback to CWD if no method succeeded
    PROJECT_ROOT = Path.cwd().resolve()
    warnings.warn(f"Could not determine project root automatically. Using current working directory: {PROJECT_ROOT}. Ensure this is the intended root or set the PDD_PATH environment variable.")


ENV_PATH = PROJECT_ROOT / ".env"
# --- Determine LLM_MODEL_CSV_PATH ---
# Prioritize ~/.pdd/llm_model.csv
user_pdd_dir = Path.home() / ".pdd"
user_model_csv_path = user_pdd_dir / "llm_model.csv"

if user_model_csv_path.is_file():
    LLM_MODEL_CSV_PATH = user_model_csv_path
    logger.info(f"Using user-specific LLM model CSV: {LLM_MODEL_CSV_PATH}")
else:
    LLM_MODEL_CSV_PATH = PROJECT_ROOT / "data" / "llm_model.csv"
    logger.info(f"Using project LLM model CSV: {LLM_MODEL_CSV_PATH}")
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

cache_configured = False

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

        litellm.cache = litellm.Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_region_name=GCS_REGION_NAME, # Pass region explicitly to cache
            s3_endpoint_url=GCS_ENDPOINT_URL,
        )
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

if not cache_configured:
    try:
        # Try SQLite-based cache as a fallback
        sqlite_cache_path = PROJECT_ROOT / "litellm_cache.sqlite"
        litellm.cache = litellm.Cache(type="sqlite", cache_path=str(sqlite_cache_path))
        logger.info(f"LiteLLM SQLite cache configured at {sqlite_cache_path}")
        cache_configured = True
    except Exception as e2:
        warnings.warn(f"Failed to configure LiteLLM SQLite cache: {e2}. Caching is disabled.")
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
        # Attempt 2: If response object failed (e.g., missing provider in model name),
        # try again using explicit model from kwargs and tokens from usage.
        # This is often needed for batch completion items.
        logger.debug(f"Attempting cost calculation with fallback method: {e1}")
        try:
            model_name = kwargs.get("model") # Get original model name from input kwargs
            if model_name and usage:
                prompt_tokens = getattr(usage, 'prompt_tokens', 0)
                completion_tokens = getattr(usage, 'completion_tokens', 0)
                cost_val = litellm.completion_cost(
                    model=model_name,
                    prompt_tokens=prompt_tokens,
                    completion_tokens=completion_tokens
                )
                calculated_cost = cost_val if cost_val is not None else 0.0
            else:
                # If we can't get model name or usage, fallback to 0
                calculated_cost = 0.0
                # Optional: Log the original error e1 if needed
                # logger.warning(f"[Callback WARN] Failed to calculate cost with response object ({e1}) and fallback failed.")
        except Exception as e2:
            # Optional: Log secondary error e2 if needed
            # logger.warning(f"[Callback WARN] Failed to calculate cost with fallback method: {e2}")
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

# --- Helper Functions ---

def _load_model_data(csv_path: Path) -> pd.DataFrame:
    """Loads and preprocesses the LLM model data from CSV."""
    if not csv_path.exists():
        raise FileNotFoundError(f"LLM model CSV not found at {csv_path}")
    try:
        df = pd.read_csv(csv_path)
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
             raise ValueError(f"Base model '{base_model_name}' found in CSV but requires API key '{original_base.iloc[0]['api_key']}' which might be missing or invalid configuration.")
        else:
             raise ValueError(f"Specified base model '{base_model_name}' not found in the LLM model CSV.")

    base_model = base_model_row.iloc[0]

    # 3. Determine Target and Sort
    candidates = []
    target_metric_value = None # For debugging print

    if strength == 0.5:
        # target_model = base_model
        # Sort remaining by ELO descending as fallback
        available_df['sort_metric'] = -available_df['coding_arena_elo'] # Negative for descending sort
        candidates = available_df.sort_values(by='sort_metric').to_dict('records')
        # Ensure base model is first if it exists
        if any(c['model'] == base_model_name for c in candidates):
            candidates.sort(key=lambda x: 0 if x['model'] == base_model_name else 1)
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


def _ensure_api_key(model_info: Dict[str, Any], newly_acquired_keys: Dict[str, bool], verbose: bool) -> bool:
    """Checks for API key in env, prompts user if missing, and updates .env."""
    key_name = model_info.get('api_key')

    if not key_name or key_name == "EXISTING_KEY":
        if verbose:
            logger.info(f"Skipping API key check for model {model_info.get('model')} (key name: {key_name})")
        return True # Assume key is handled elsewhere or not needed

    key_value = os.getenv(key_name)

    if key_value:
        if verbose:
            logger.info(f"API key '{key_name}' found in environment.")
        newly_acquired_keys[key_name] = False # Mark as existing
        return True
    else:
        logger.warning(f"API key environment variable '{key_name}' for model '{model_info.get('model')}' is not set.")
        try:
            # Interactive prompt
            user_provided_key = input(f"Please enter the API key for {key_name}: ").strip()
            if not user_provided_key:
                logger.error("No API key provided. Cannot proceed with this model.")
                return False

            # Set environment variable for the current process
            os.environ[key_name] = user_provided_key
            logger.info(f"API key '{key_name}' set for the current session.")
            newly_acquired_keys[key_name] = True # Mark as newly acquired

            # Update .env file
            try:
                lines = []
                if ENV_PATH.exists():
                    with open(ENV_PATH, 'r') as f:
                        lines = f.readlines()

                new_lines = []
                # key_updated = False
                prefix = f"{key_name}="
                prefix_spaced = f"{key_name} =" # Handle potential spaces

                for line in lines:
                    stripped_line = line.strip()
                    if stripped_line.startswith(prefix) or stripped_line.startswith(prefix_spaced):
                        # Comment out the old key
                        new_lines.append(f"# {line}")
                        # key_updated = True # Indicates we found an old line to comment
                    elif stripped_line.startswith(f"# {prefix}") or stripped_line.startswith(f"# {prefix_spaced}"):
                         # Keep already commented lines as they are
                         new_lines.append(line)
                    else:
                        new_lines.append(line)

                # Append the new key, ensuring quotes for robustness
                new_key_line = f'{key_name}="{user_provided_key}"\n'
                # Add newline before if file not empty and doesn't end with newline
                if new_lines and not new_lines[-1].endswith('\n'):
                     new_lines.append('\n')
                new_lines.append(new_key_line)


                with open(ENV_PATH, 'w') as f:
                    f.writelines(new_lines)

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
        prompt_template = PromptTemplate.from_template(prompt)
        if use_batch_mode:
            if not isinstance(input_data, list):
                raise ValueError("input_json must be a list of dictionaries when use_batch_mode is True.")
            all_messages = []
            for item in input_data:
                if not isinstance(item, dict):
                     raise ValueError("Each item in input_json list must be a dictionary for batch mode.")
                formatted_prompt = prompt_template.format(**item)
                all_messages.append([{"role": "user", "content": formatted_prompt}])
            return all_messages
        else:
            if not isinstance(input_data, dict):
                raise ValueError("input_json must be a dictionary when use_batch_mode is False.")
            formatted_prompt = prompt_template.format(**input_data)
            return [{"role": "user", "content": formatted_prompt}]
    except KeyError as e:
        raise ValueError(f"Prompt formatting error: Missing key {e} in input_json for prompt template.") from e
    except Exception as e:
        raise ValueError(f"Error formatting prompt: {e}") from e

# --- Main Function ---

def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]] = None,
    strength: float = 0.5, # Use pdd.DEFAULT_STRENGTH if available, else 0.5
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    time: float = 0.25,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict[str, str]], List[List[Dict[str, str]]]]] = None,
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

    for model_info in candidate_models:
        model_name_litellm = model_info['model']
        api_key_name = model_info.get('api_key')
        provider = model_info.get('provider', '').lower()

        if verbose:
            logger.info(f"\n[ATTEMPT] Trying model: {model_name_litellm} (Provider: {provider})")

        retry_with_same_model = True
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
                "temperature": temperature,
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
                        if verbose:
                            logger.error(f"[ERROR] Vertex credentials file not found at path specified by VERTEX_CREDENTIALS env var: '{credentials_file_path}'. LiteLLM may try ADC or fail.")
                    except json.JSONDecodeError:
                        if verbose:
                            logger.error(f"[ERROR] Failed to decode JSON from Vertex credentials file: '{credentials_file_path}'. Check file content. LiteLLM may try ADC or fail.")
                    except Exception as e:
                        if verbose:
                            logger.error(f"[ERROR] Failed to load or process Vertex credentials from '{credentials_file_path}': {e}. LiteLLM may try ADC or fail.")
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
                    litellm_kwargs["api_key"] = key_value
                    if verbose:
                        logger.info(f"[INFO] Explicitly passing API key from env var '{api_key_name_from_csv}' as 'api_key' parameter to LiteLLM.")
                    
                    # If this model is Vertex AI AND uses a direct API key string (not VERTEX_CREDENTIALS from CSV),
                    # also pass project and location from env vars.
                    if is_vertex_model: 
                        vertex_project_env = os.getenv("VERTEX_PROJECT")
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

            # Add api_base if present in CSV
            api_base = model_info.get('base_url')
            if pd.notna(api_base) and api_base:
                litellm_kwargs["api_base"] = str(api_base)

            # Handle Structured Output (JSON Mode / Pydantic)
            if output_pydantic:
                # Check if model supports structured output based on CSV flag or LiteLLM check
                supports_structured = model_info.get('structured_output', False)
                # Optional: Add litellm.supports_response_schema check if CSV flag is unreliable
                # if not supports_structured:
                #     try: supports_structured = litellm.supports_response_schema(model=model_name_litellm)
                #     except: pass # Ignore errors in supports_response_schema check

                if supports_structured:
                    if verbose:
                        logger.info(f"[INFO] Requesting structured output (Pydantic: {output_pydantic.__name__}) for {model_name_litellm}")
                    # Pass the Pydantic model directly if supported, else use json_object
                    # LiteLLM handles passing Pydantic models for supported providers
                    litellm_kwargs["response_format"] = output_pydantic
                    # As a fallback, one could use:
                    # litellm_kwargs["response_format"] = {"type": "json_object"}
                    # And potentially enable client-side validation:
                    # litellm.enable_json_schema_validation = True # Enable globally if needed
                else:
                    if verbose:
                        logger.warning(f"[WARN] Model {model_name_litellm} does not support structured output via CSV flag. Output might not be valid {output_pydantic.__name__}.")
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
                                litellm_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
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
                    # Use the common 'reasoning_effort' param LiteLLM provides
                    litellm_kwargs["reasoning_effort"] = effort
                    if verbose:
                        logger.info(f"[INFO] Requesting reasoning_effort='{effort}' (effort type) for {model_name_litellm} based on time={time}")

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


                if use_batch_mode:
                    if verbose:
                        logger.info(f"[INFO] Calling litellm.batch_completion for {model_name_litellm}...")
                    response = litellm.batch_completion(**litellm_kwargs)


                else:
                    if verbose:
                        logger.info(f"[INFO] Calling litellm.completion for {model_name_litellm}...")
                    response = litellm.completion(**litellm_kwargs)

                end_time = time_module.time()

                if verbose:
                    logger.info(f"[SUCCESS] Invocation successful for {model_name_litellm} (took {end_time - start_time:.2f}s)")

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
                        if output_pydantic:
                            parsed_result = None
                            json_string_to_parse = None

                            try:
                                # Attempt 1: Check if LiteLLM already parsed it
                                if isinstance(raw_result, output_pydantic):
                                    parsed_result = raw_result
                                    if verbose:
                                        logger.debug("[DEBUG] Pydantic object received directly from LiteLLM.")

                                # Attempt 2: Check if raw_result is dict-like and validate
                                elif isinstance(raw_result, dict):
                                    parsed_result = output_pydantic.model_validate(raw_result)
                                    if verbose:
                                        logger.debug("[DEBUG] Validated dictionary-like object directly.")

                                # Attempt 3: Process as string (if not already parsed/validated)
                                elif isinstance(raw_result, str):
                                    json_string_to_parse = raw_result # Start with the raw string
                                    try:
                                        # Look for first { and last }
                                        start_brace = json_string_to_parse.find('{')
                                        end_brace = json_string_to_parse.rfind('}')
                                        if start_brace != -1 and end_brace != -1 and end_brace > start_brace:
                                            potential_json = json_string_to_parse[start_brace:end_brace+1]
                                            # Basic check if it looks like JSON
                                            if potential_json.strip().startswith('{') and potential_json.strip().endswith('}'):
                                                if verbose:
                                                    logger.debug(f"[DEBUG] Attempting to parse extracted JSON block: '{potential_json}'")
                                                parsed_result = output_pydantic.model_validate_json(potential_json)
                                            else:
                                                # If block extraction fails, try cleaning markdown next
                                                raise ValueError("Extracted block doesn't look like JSON")
                                        else:
                                             # If no braces found, try cleaning markdown next
                                            raise ValueError("Could not find enclosing {}")
                                    except (json.JSONDecodeError, ValidationError, ValueError) as extraction_error:
                                        if verbose:
                                            logger.debug(f"[DEBUG] JSON block extraction/validation failed ('{extraction_error}'). Trying markdown cleaning.")
                                        # Fallback: Clean markdown fences and retry JSON validation
                                        cleaned_result_str = raw_result.strip()
                                        if cleaned_result_str.startswith("```json"):
                                            cleaned_result_str = cleaned_result_str[7:]
                                        elif cleaned_result_str.startswith("```"):
                                            cleaned_result_str = cleaned_result_str[3:]
                                        if cleaned_result_str.endswith("```"):
                                            cleaned_result_str = cleaned_result_str[:-3]
                                        cleaned_result_str = cleaned_result_str.strip()
                                        # Check again if it looks like JSON before parsing
                                        if cleaned_result_str.startswith('{') and cleaned_result_str.endswith('}'):
                                            if verbose:
                                                logger.debug(f"[DEBUG] Attempting parse after cleaning markdown fences. Cleaned string: '{cleaned_result_str}'")
                                            json_string_to_parse = cleaned_result_str # Update string for error reporting
                                            parsed_result = output_pydantic.model_validate_json(json_string_to_parse)
                                        else:
                                            # If still doesn't look like JSON, raise error
                                            raise ValueError("Content after cleaning markdown doesn't look like JSON")


                                # Check if any parsing attempt succeeded
                                if parsed_result is None:
                                    # This case should ideally be caught by exceptions above, but as a safeguard:
                                    raise TypeError(f"Raw result type {type(raw_result)} or content could not be validated/parsed against {output_pydantic.__name__}.")

                            except (ValidationError, json.JSONDecodeError, TypeError, ValueError) as parse_error:
                                logger.error(f"[ERROR] Failed to parse response into Pydantic model {output_pydantic.__name__} for item {i}: {parse_error}")
                                # Use the string that was last attempted for parsing in the error message
                                error_content = json_string_to_parse if json_string_to_parse is not None else raw_result
                                logger.error("[ERROR] Content attempted for parsing: %s", repr(error_content)) # CORRECTED (or use f-string)
                                results.append(f"ERROR: Failed to parse Pydantic. Raw: {repr(raw_result)}")
                                continue # Skip appending result below if parsing failed

                            # If parsing succeeded, append the parsed_result
                            results.append(parsed_result)

                        else:
                            # If output_pydantic was not requested, append the raw result
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

            except (openai.RateLimitError, openai.APITimeoutError, openai.APIConnectionError,
                    openai.APIStatusError, openai.BadRequestError, openai.InternalServerError,
                    Exception) as e: # Catch generic Exception last
                last_exception = e
                error_type = type(e).__name__
                logger.error(f"[ERROR] Invocation failed for {model_name_litellm} ({error_type}): {e}. Trying next model.")
                # Log more details in verbose mode
                if verbose:
                    # import traceback # Not needed if using exc_info=True
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
            strength=0.5, # Use base model (gpt-4.1-nano)
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
        # Strength 0.5 should select gpt-4.1-nano
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
