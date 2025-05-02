# llm_invoke.py

import os
import sys
import pandas as pd
import litellm
import json
from rich import print as rprint
from rich.pretty import pretty_repr
from dotenv import load_dotenv
from pathlib import Path
from typing import Optional, Dict, List, Any, Type, Union
from pydantic import BaseModel, ValidationError
import openai  # Import openai for exception handling as LiteLLM maps to its types
from langchain_core.prompts import PromptTemplate
import warnings
import time as time_module # Alias to avoid conflict with 'time' parameter

# <<< SET LITELLM DEBUG LOGGING >>>
os.environ['LITELLM_LOG'] = 'DEBUG'

# --- Constants and Configuration ---

# Determine project root: 1. PDD_PATH env var, 2. Search upwards from script, 3. CWD
PROJECT_ROOT = None
PDD_PATH_ENV = os.getenv("PDD_PATH")

if PDD_PATH_ENV:
    _path_from_env = Path(PDD_PATH_ENV)
    if _path_from_env.is_dir():
        PROJECT_ROOT = _path_from_env.resolve()
        # print(f"[DEBUG] Using PROJECT_ROOT from PDD_PATH: {PROJECT_ROOT}") # Optional debug
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
                # print(f"[DEBUG] Determined PROJECT_ROOT by marker search: {PROJECT_ROOT}") # Optional debug
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
LLM_MODEL_CSV_PATH = PROJECT_ROOT / "data" / "llm_model.csv"

# Load environment variables from .env file
# print(f"[DEBUG] Attempting to load .env from: {ENV_PATH}") # Optional debug
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)
    # print(f"[DEBUG] Loaded .env file from: {ENV_PATH}") # Optional debug
else:
    # Reduce verbosity if .env is optional or often missing
    # warnings.warn(f".env file not found at {ENV_PATH}. API keys might be missing.")
    pass # Silently proceed if .env is optional

# Default model if PDD_MODEL_DEFAULT is not set
DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT", "gpt-4.1-nano") # Using LiteLLM format potentially

# --- LiteLLM Cache Configuration (S3 compatible for GCS) ---
GCS_BUCKET_NAME = os.getenv("GCS_BUCKET_NAME")
GCS_ENDPOINT_URL = "https://storage.googleapis.com" # GCS S3 compatibility endpoint
GCS_REGION_NAME = os.getenv("GCS_REGION_NAME", "auto") # Often 'auto' works for GCS
GCS_HMAC_ACCESS_KEY_ID = os.getenv("GCS_HMAC_ACCESS_KEY_ID") # Load HMAC Key ID
GCS_HMAC_SECRET_ACCESS_KEY = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY") # Load HMAC Secret

# <<< CONFIGURING GCS CACHE (S3 Compatible) >>>
if GCS_BUCKET_NAME and GCS_HMAC_ACCESS_KEY_ID and GCS_HMAC_SECRET_ACCESS_KEY:
    try:
        # LiteLLM uses boto3 conventions. Setting the standard AWS env vars
        # AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY will be automatically picked up.
        # We explicitly set them here from the GCS-specific vars for clarity
        # and to ensure they override any other AWS credentials if present.
        os.environ['AWS_ACCESS_KEY_ID'] = GCS_HMAC_ACCESS_KEY_ID
        os.environ['AWS_SECRET_ACCESS_KEY'] = GCS_HMAC_SECRET_ACCESS_KEY

        litellm.cache = litellm.Cache(
            type="s3",
            s3_bucket_name=GCS_BUCKET_NAME,
            s3_region_name=GCS_REGION_NAME,
            s3_endpoint_url=GCS_ENDPOINT_URL,
            # Note: LiteLLM/boto3 will use AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY from env
        )
        print(f"[INFO] LiteLLM cache configured for GCS bucket (S3 compatible): {GCS_BUCKET_NAME}")
    except Exception as e:
        warnings.warn(f"Failed to configure LiteLLM S3/GCS cache: {e}. Caching might be disabled or fallback.")
        litellm.cache = None # Explicitly disable cache on failure
else:
    warnings.warn("Required GCS cache environment variables (GCS_BUCKET_NAME, GCS_HMAC_ACCESS_KEY_ID, GCS_HMAC_SECRET_ACCESS_KEY) not fully set. LiteLLM caching is disabled.")
    litellm.cache = None # Explicitly disable cache

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
    cost = getattr(completion_response, 'cost', 0.0)

    _LAST_CALLBACK_DATA["input_tokens"] = input_tokens
    _LAST_CALLBACK_DATA["output_tokens"] = output_tokens
    _LAST_CALLBACK_DATA["finish_reason"] = finish_reason
    _LAST_CALLBACK_DATA["cost"] = cost

    # Example of logging within the callback (can be expanded)
    # print(f"[Callback] Tokens: In={input_tokens}, Out={output_tokens}. Reason: {finish_reason}. Cost: ${cost:.6f}")

# Register the callback with LiteLLM
litellm.success_callback = [_litellm_success_callback]
litellm.set_verbose=True # Enable detailed LiteLLM internal logging

# --- Helper Functions ---

def _load_model_data(csv_path: Path) -> pd.DataFrame:
    """Loads and preprocesses the LLM model data from CSV."""
    if not csv_path.exists():
        raise FileNotFoundError(f"LLM model CSV not found at {csv_path}")
    try:
        df = pd.read_csv(csv_path)
        # Basic validation and type conversion
        required_cols = ['provider', 'model', 'input', 'output', 'coding_arena_elo', 'api_key']
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

        # Calculate average cost (handle potential division by zero if needed, though unlikely with fillna)
        df['avg_cost'] = (df['input'] + df['output']) / 2

        # Ensure boolean interpretation for structured_output
        if 'structured_output' in df.columns:
             df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
        else:
             df['structured_output'] = False # Assume false if column missing

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
    available_df = model_df[model_df['api_key'].notna() & (model_df['api_key'] != '')].copy()

    if available_df.empty:
        raise ValueError("No models available after initial filtering (missing 'api_key' in CSV?).")

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
    if strength == 0.5:
        target_model = base_model
        # Sort remaining by ELO descending as fallback
        available_df['sort_metric'] = -available_df['coding_arena_elo'] # Negative for descending sort
        candidates = available_df.sort_values(by='sort_metric').to_dict('records')
        # Ensure base model is first if it exists
        if any(c['model'] == base_model_name for c in candidates):
            candidates.sort(key=lambda x: 0 if x['model'] == base_model_name else 1)

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

    if not candidates:
         # This should ideally not happen if available_df was not empty
         raise RuntimeError("Model selection resulted in an empty candidate list.")

    return candidates


def _ensure_api_key(model_info: Dict[str, Any], newly_acquired_keys: Dict[str, bool], verbose: bool) -> bool:
    """Checks for API key in env, prompts user if missing, and updates .env."""
    key_name = model_info.get('api_key')

    if not key_name or key_name == "EXISTING_KEY":
        if verbose:
            rprint(f"[INFO] Skipping API key check for model {model_info.get('model')} (key name: {key_name})")
        return True # Assume key is handled elsewhere or not needed

    key_value = os.getenv(key_name)

    if key_value:
        if verbose:
            rprint(f"[INFO] API key '{key_name}' found in environment.")
        newly_acquired_keys[key_name] = False # Mark as existing
        return True
    else:
        rprint(f"[WARN] API key environment variable '{key_name}' for model '{model_info.get('model')}' is not set.")
        try:
            # Interactive prompt
            user_provided_key = input(f"Please enter the API key for {key_name}: ").strip()
            if not user_provided_key:
                rprint("[ERROR] No API key provided. Cannot proceed with this model.")
                return False

            # Set environment variable for the current process
            os.environ[key_name] = user_provided_key
            rprint(f"[INFO] API key '{key_name}' set for the current session.")
            newly_acquired_keys[key_name] = True # Mark as newly acquired

            # Update .env file
            try:
                lines = []
                if ENV_PATH.exists():
                    with open(ENV_PATH, 'r') as f:
                        lines = f.readlines()

                new_lines = []
                key_updated = False
                prefix = f"{key_name}="
                prefix_spaced = f"{key_name} =" # Handle potential spaces

                for line in lines:
                    stripped_line = line.strip()
                    if stripped_line.startswith(prefix) or stripped_line.startswith(prefix_spaced):
                        # Comment out the old key
                        new_lines.append(f"# {line}")
                        key_updated = True # Indicates we found an old line to comment
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

                rprint(f"[INFO] API key '{key_name}' saved to {ENV_PATH}.")
                rprint("[bold yellow]SECURITY WARNING:[/bold yellow] The API key has been saved to your .env file. "
                       "Ensure this file is kept secure and is included in your .gitignore.")

            except IOError as e:
                rprint(f"[ERROR] Failed to update .env file at {ENV_PATH}: {e}")
                # Continue since the key is set in the environment for this session

            return True

        except EOFError: # Handle non-interactive environments
             rprint(f"[ERROR] Cannot prompt for API key '{key_name}' in a non-interactive environment.")
             return False
        except Exception as e:
             rprint(f"[ERROR] An unexpected error occurred during API key acquisition: {e}")
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
    # --- 1. Load Environment & Validate Inputs ---
    # .env loading happens at module level

    if messages:
        if verbose:
            rprint("[INFO] Using provided 'messages' input.")
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
        rprint(f"[ERROR] Failed during model loading or selection: {e}")
        raise

    if verbose:
        rprint("[INFO] Candidate models selected and ordered:", [c['model'] for c in candidate_models])
        rprint(f"[INFO] Strength: {strength}, Temperature: {temperature}, Time: {time}")
        if use_batch_mode: rprint("[INFO] Batch mode enabled.")
        if output_pydantic: rprint(f"[INFO] Pydantic output requested: {output_pydantic.__name__}")
        try:
            rprint("[INFO] Input JSON:")
            rprint(input_json if input_json is not None else "[Messages provided directly]")
        except Exception:
            print("[INFO] Input JSON (fallback print):") # Fallback for complex objects rich might fail on
            print(input_json if input_json is not None else "[Messages provided directly]")


    # --- 3. Iterate Through Candidates and Invoke LLM ---
    last_exception = None
    newly_acquired_keys: Dict[str, bool] = {} # Track keys obtained in this run

    for model_info in candidate_models:
        model_name_litellm = model_info['model']
        api_key_name = model_info.get('api_key')
        provider = model_info.get('provider', '').lower()

        if verbose:
            rprint(f"\n[ATTEMPT] Trying model: {model_name_litellm} (Provider: {provider})")

        retry_with_same_model = True
        while retry_with_same_model:
            retry_with_same_model = False # Assume success unless auth error on new key

            # --- 4. API Key Check & Acquisition ---
            if not _ensure_api_key(model_info, newly_acquired_keys, verbose):
                # Problem getting key, break inner loop, try next model candidate
                if verbose: rprint(f"[SKIP] Skipping {model_name_litellm} due to API key issue.")
                break # Breaks the 'while retry_with_same_model' loop

            # --- 5. Prepare LiteLLM Arguments ---
            litellm_kwargs: Dict[str, Any] = {
                "model": model_name_litellm,
                "messages": formatted_messages,
                "temperature": temperature,
                # LiteLLM uses env vars for keys by default, but can be overridden
                # "api_key": os.getenv(api_key_name) if api_key_name else None,
            }

            # Add api_base if present in CSV
            api_base = model_info.get('base_url')
            if pd.notna(api_base) and api_base:
                litellm_kwargs["api_base"] = str(api_base)

            # Add max_tokens (completion tokens)
            max_completion_tokens = model_info.get('max_completion_tokens')
            if pd.notna(max_completion_tokens) and max_completion_tokens > 0:
                litellm_kwargs["max_tokens"] = int(max_completion_tokens)
            else:
                 # Fallback to max_tokens if max_completion_tokens is missing/invalid
                 max_tokens_fallback = model_info.get('max_tokens')
                 if pd.notna(max_tokens_fallback) and max_tokens_fallback > 0:
                      litellm_kwargs["max_tokens"] = int(max_tokens_fallback)
                      if verbose: rprint(f"[WARN] Using 'max_tokens' ({int(max_tokens_fallback)}) as fallback for {model_name_litellm}")


            # Handle Structured Output (JSON Mode / Pydantic)
            if output_pydantic:
                # Check if model supports structured output based on CSV flag or LiteLLM check
                supports_structured = model_info.get('structured_output', False)
                # Optional: Add litellm.supports_response_schema check if CSV flag is unreliable
                # if not supports_structured:
                #     try: supports_structured = litellm.supports_response_schema(model=model_name_litellm)
                #     except: pass # Ignore errors in supports_response_schema check

                if supports_structured:
                    if verbose: rprint(f"[INFO] Requesting structured output (Pydantic: {output_pydantic.__name__}) for {model_name_litellm}")
                    # Pass the Pydantic model directly if supported, else use json_object
                    # LiteLLM handles passing Pydantic models for supported providers
                    litellm_kwargs["response_format"] = output_pydantic
                    # As a fallback, one could use:
                    # litellm_kwargs["response_format"] = {"type": "json_object"}
                    # And potentially enable client-side validation:
                    # litellm.enable_json_schema_validation = True # Enable globally if needed
                else:
                    if verbose: rprint(f"[WARN] Model {model_name_litellm} does not support structured output via CSV flag. Output might not be valid {output_pydantic.__name__}.")
                    # Proceed without forcing JSON mode, parsing will be attempted later

            # Handle Reasoning/Thinking Time
            max_reasoning_tokens = model_info.get('max_reasoning_tokens')
            if pd.notna(max_reasoning_tokens) and max_reasoning_tokens > 0 and time > 0:
                 budget = int(time * max_reasoning_tokens)
                 if budget > 0:
                     # Provider-specific handling based on LiteLLM docs/examples
                     if provider == 'anthropic':
                         litellm_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                         if verbose: rprint(f"[INFO] Requesting Anthropic thinking with budget: {budget} tokens")
                     # Add other providers if LiteLLM supports direct budget mapping
                     # elif provider == 'google': # Example if Google supported it
                     #     litellm_kwargs["reasoning_budget"] = budget # Fictional parameter
                     else:
                         # Fallback: Map 'time' to 'reasoning_effort' if budget not directly supported
                         effort = "low"
                         if time > 0.7: effort = "high"
                         elif time > 0.3: effort = "medium"
                         try:
                             if litellm.supports_reasoning(model=model_name_litellm):
                                 litellm_kwargs["reasoning_effort"] = effort
                                 if verbose: rprint(f"[INFO] Requesting reasoning_effort='{effort}' for {model_name_litellm} based on time={time}")
                             elif verbose:
                                 rprint(f"[INFO] Model {model_name_litellm} does not support reasoning via litellm.supports_reasoning.")
                         except Exception as e_reason:
                              if verbose: rprint(f"[WARN] Could not check reasoning support for {model_name_litellm}: {e_reason}")

            # Add caching control per call if needed (example: force refresh)
            # litellm_kwargs["cache"] = {"no-cache": True}

            # --- 6. LLM Invocation ---
            try:
                start_time = time_module.time()
                # <<< EXPLICITLY ENABLE CACHING >>>
                litellm_kwargs["caching"] = True 
                if use_batch_mode:
                    if verbose: rprint(f"[INFO] Calling litellm.batch_completion for {model_name_litellm}...")
                    response = litellm.batch_completion(**litellm_kwargs)
                else:
                    if verbose: rprint(f"[INFO] Calling litellm.completion for {model_name_litellm}...")
                    response = litellm.completion(**litellm_kwargs)
                end_time = time_module.time()

                if verbose:
                    rprint(f"[SUCCESS] Invocation successful for {model_name_litellm} (took {end_time - start_time:.2f}s)")

                # --- 7. Process Response ---
                results = []
                total_cost = 0.0
                thinking_outputs = []

                response_list = response if use_batch_mode else [response]

                for i, resp_item in enumerate(response_list):
                    # Cost
                    item_cost = getattr(resp_item, 'cost', 0.0)
                    if item_cost is None: # Handle potential None cost
                         item_cost = 0.0
                         # Try calculating manually if needed and possible
                         # usage = getattr(resp_item, 'usage', None)
                         # if usage:
                         #    prompt_tokens = getattr(usage, 'prompt_tokens', 0)
                         #    completion_tokens = getattr(usage, 'completion_tokens', 0)
                         #    try:
                         #        item_cost = litellm.completion_cost(model=model_name_litellm, prompt_tokens=prompt_tokens, completion_tokens=completion_tokens)
                         #    except: pass # Ignore cost calculation errors
                    total_cost += item_cost

                    # Thinking Output
                    thinking = None
                    try:
                        # Access reasoning content if available in the response structure
                        thinking = resp_item.choices[0].message.get('reasoning_content')
                    except (AttributeError, IndexError, KeyError):
                        pass # Ignore if structure doesn't match
                    thinking_outputs.append(thinking)

                    # Result (String or Pydantic)
                    try:
                        raw_result = resp_item.choices[0].message.content
                        if output_pydantic:
                            try:
                                # If LiteLLM returned the parsed object directly
                                if isinstance(raw_result, output_pydantic):
                                     parsed_result = raw_result
                                # If LiteLLM returned a JSON string
                                elif isinstance(raw_result, str):
                                     parsed_result = output_pydantic.model_validate_json(raw_result)
                                else:
                                     # Try converting to dict first if it's dict-like
                                     parsed_result = output_pydantic.model_validate(raw_result)

                                results.append(parsed_result)
                            except (ValidationError, json.JSONDecodeError, TypeError) as parse_error:
                                rprint(f"[ERROR] Failed to parse response into Pydantic model {output_pydantic.__name__} for item {i}: {parse_error}")
                                rprint("[ERROR] Raw content:", raw_result)
                                # Append raw string or raise error depending on desired strictness
                                results.append(f"ERROR: Failed to parse Pydantic. Raw: {raw_result}")
                                # Or raise ValueError(f"Failed to parse response into Pydantic model: {parse_error}")
                        else:
                            results.append(raw_result) # String output
                    except (AttributeError, IndexError) as e:
                         rprint(f"[ERROR] Could not extract result content from response item {i}: {e}")
                         results.append(f"ERROR: Could not extract result content. Response: {resp_item}")


                final_result = results if use_batch_mode else results[0]
                final_thinking = thinking_outputs if use_batch_mode else thinking_outputs[0]

                # --- Verbose Output for Success ---
                if verbose:
                    # Get token usage from the *last* callback data (hacky, but per prompt)
                    # A better way is to get it directly from response if batch_completion provides aggregated usage
                    input_tokens = _LAST_CALLBACK_DATA["input_tokens"] # May not be accurate for batch
                    output_tokens = _LAST_CALLBACK_DATA["output_tokens"] # May not be accurate for batch
                    # Try getting from response directly (might be None or only for last item in batch)
                    try:
                         usage_obj = getattr(response_list[-1], 'usage', None)
                         if usage_obj:
                              input_tokens = getattr(usage_obj, 'prompt_tokens', input_tokens)
                              output_tokens = getattr(usage_obj, 'completion_tokens', output_tokens)
                    except: pass

                    cost_input_pm = model_info.get('input', 0.0) * 1_000_000 if pd.notna(model_info.get('input')) else 0.0
                    cost_output_pm = model_info.get('output', 0.0) * 1_000_000 if pd.notna(model_info.get('output')) else 0.0

                    rprint(f"[RESULT] Model Used: {model_name_litellm}")
                    rprint(f"[RESULT] Cost (Input): ${cost_input_pm:.2f}/M tokens")
                    rprint(f"[RESULT] Cost (Output): ${cost_output_pm:.2f}/M tokens")
                    rprint(f"[RESULT] Tokens (Prompt): {input_tokens}")
                    rprint(f"[RESULT] Tokens (Completion): {output_tokens}")
                    rprint(f"[RESULT] Total Cost: ${total_cost:.6f}") # Use cost from response
                    if final_thinking:
                        rprint("[RESULT] Thinking Output:")
                        rprint(final_thinking)
                    rprint("[RESULT] Final Output:")
                    try:
                        rprint(final_result)
                    except Exception:
                        print(final_result) # Fallback print

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
                    rprint(f"[AUTH ERROR] Authentication failed for {model_name_litellm} with the newly provided key for '{api_key_name}'. Please check the key and try again.")
                    # Invalidate the key in env for this session to force re-prompt on retry
                    if api_key_name in os.environ:
                         del os.environ[api_key_name]
                    retry_with_same_model = True # Set flag to retry the same model after re-prompt
                    # Go back to the start of the 'while retry_with_same_model' loop
                else:
                    rprint(f"[AUTH ERROR] Authentication failed for {model_name_litellm} using existing key '{api_key_name}'. Trying next model.")
                    break # Break inner loop, try next model candidate

            except (openai.RateLimitError, openai.APITimeoutError, openai.APIConnectionError,
                    openai.APIStatusError, openai.BadRequestError, openai.InternalServerError,
                    Exception) as e:
                last_exception = e
                error_type = type(e).__name__
                rprint(f"[ERROR] Invocation failed for {model_name_litellm} ({error_type}): {e}. Trying next model.")
                # Log more details in verbose mode
                if verbose:
                    import traceback
                    traceback.print_exc()
                break # Break inner loop, try next model candidate

        # If the inner loop was broken (not by success), continue to the next candidate model
        continue

    # --- 8. Handle Failure of All Candidates ---
    error_message = "All candidate models failed."
    if last_exception:
        error_message += f" Last error ({type(last_exception).__name__}): {last_exception}"
    rprint(f"[FATAL] {error_message}")
    raise RuntimeError(error_message) from last_exception

# --- Example Usage (Optional) ---
if __name__ == "__main__":
    # This block allows running the file directly for testing.
    # Ensure you have a ./data/llm_model.csv file and potentially a .env file.

    # Example 1: Simple text generation
    print("\n--- Example 1: Simple Text Generation ---")
    try:
        response = llm_invoke(
            prompt="Tell me a short joke about {topic}.",
            input_json={"topic": "programmers"},
            strength=0.5, # Use base model
            temperature=0.7,
            verbose=True
        )
        # rprint("Example 1 Response:", response)
    except Exception as e:
        rprint(f"Example 1 Failed: {e}")

    # Example 2: Structured output (requires a Pydantic model)
    print("\n--- Example 2: Structured Output (Pydantic) ---")
    class JokeStructure(BaseModel):
        setup: str
        punchline: str
        rating: Optional[int] = None

    try:
        # Use a model known to support structured output (check your CSV)
        # May need higher strength if base model doesn't support it well
        response_structured = llm_invoke(
            prompt="Create a joke about {topic}. Output as JSON with 'setup' and 'punchline'.",
            input_json={"topic": "data science"},
            strength=0.8, # Try a higher ELO model potentially better at JSON
            temperature=0.2,
            output_pydantic=JokeStructure,
            verbose=True
        )
        # rprint("Example 2 Response:", response_structured)
        if isinstance(response_structured.get('result'), JokeStructure):
             rprint("Pydantic object received successfully:", response_structured['result'].model_dump())
        else:
             rprint("Result was not the expected Pydantic object:", response_structured.get('result'))

    except Exception as e:
        rprint(f"Example 2 Failed: {e}")


    # Example 3: Batch processing
    print("\n--- Example 3: Batch Processing ---")
    try:
        batch_input = [
            {"animal": "cat", "adjective": "lazy"},
            {"animal": "dog", "adjective": "energetic"},
        ]
        response_batch = llm_invoke(
            prompt="Describe a {adjective} {animal} in one sentence.",
            input_json=batch_input,
            strength=0.3, # Cheaper model maybe
            temperature=0.5,
            use_batch_mode=True,
            verbose=True
        )
        # rprint("Example 3 Response:", response_batch)
    except Exception as e:
        rprint(f"Example 3 Failed: {e}")

    # Example 4: Using 'messages' input
    print("\n--- Example 4: Using 'messages' input ---")
    try:
        custom_messages = [
            {"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": "What is the capital of France?"}
        ]
        response_messages = llm_invoke(
            messages=custom_messages,
            strength=0.5,
            temperature=0.1,
            verbose=True
        )
        # rprint("Example 4 Response:", response_messages)
    except Exception as e:
        rprint(f"Example 4 Failed: {e}")

    # Example 5: Requesting thinking time (e.g., for Anthropic)
    print("\n--- Example 5: Requesting Thinking Time ---")
    try:
        # Ensure your CSV has max_reasoning_tokens for an Anthropic model
        response_thinking = llm_invoke(
            prompt="Explain the theory of relativity simply.",
            input_json={},
            strength=0.6, # Try to get a model that might support thinking
            temperature=0.0, # <<< SET TO 0 FOR DETERMINISM >>>
            verbose=True
        )
        # rprint("Example 5 Response:", response_thinking)
    except Exception as e:
        rprint(f"Example 5 Failed: {e}")

