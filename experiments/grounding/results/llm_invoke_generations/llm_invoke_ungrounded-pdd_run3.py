from __future__ import annotations

import json
import logging
import logging.handlers
import os
import re
import sys
import time as time_module
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

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
PDD_LOG_NAME = "pdd.llm_invoke"
console = Console()

# Global state for callback data
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Custom Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic/Schema validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud errors that should trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required - Do not fall back."""
    pass

# --- Logging Setup ---

def setup_file_logging() -> None:
    resolver = get_default_resolver()
    root = resolver.resolve_project_root()
    log_dir = root / "logs"
    log_dir.mkdir(exist_ok=True)
    
    logger = logging.getLogger("pdd")
    handler = logging.handlers.RotatingFileHandler(
        log_dir / "pdd.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(verbose: bool) -> None:
    level = logging.DEBUG if verbose else logging.INFO
    logging.getLogger(PDD_LOG_NAME).setLevel(level)
    if verbose:
        litellm.set_verbose = True

def _initialize_logging():
    pdd_level = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
    lite_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    
    if os.getenv("PDD_ENVIRONMENT") == "production":
        pdd_level = "WARNING"
        lite_level = "WARNING"
    
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        pdd_level = "DEBUG"
        lite_level = "DEBUG"

    logging.basicConfig(level=logging.WARNING)
    logging.getLogger(PDD_LOG_NAME).setLevel(pdd_level)
    logging.getLogger("litellm").setLevel(lite_level)

# --- Helper Functions ---

def _is_wsl() -> bool:
    return "microsoft" in open("/proc/version").read().lower() if Path("/proc/version").exists() else "WSL_DISTRO_NAME" in os.environ

def _sanitize_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _get_api_key_interactively(key_name: str, provider: str) -> str:
    if os.getenv("PDD_FORCE"):
        return ""
    
    console.print(f"[yellow]Missing API Key for {provider} ({key_name}).[/yellow]")
    key = input(f"Enter {key_name}: ").strip()
    if not key:
        return ""
    
    key = _sanitize_key(key)
    
    # Save to .env
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    env_path = project_root / ".env"
    
    # Handle .env update logic (remove old commented, set new)
    if env_path.exists():
        with open(env_path, "r") as f:
            lines = f.readlines()
        with open(env_path, "w") as f:
            for line in lines:
                if not line.startswith(f"#{key_name}") and not line.startswith(f"{key_name}="):
                    f.write(line)
    
    set_key(str(env_path), key_name, key)
    os.environ[key_name] = key
    console.print(f"[bold green]Key saved to {env_path}. Ensure this file is in .gitignore![/bold green]")
    return key

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
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

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        if "properties" in schema:
            for prop in schema["properties"].values():
                _add_additional_properties_false(prop)
    elif schema.get("type") == "array" and "items" in schema:
        _add_additional_properties_false(schema["items"])

    if "$defs" in schema:
        for definition in schema["$defs"].values():
            _add_additional_properties_false(definition)

def _repair_json_string(s: str) -> str:
    s = s.strip()
    # Try to find JSON block
    match = re.search(r"```json\s*(.*?)\s*```", s, re.DOTALL)
    if match:
        return match.group(1)
    
    # Simple balance check / repair
    if s.startswith("{") and not s.endswith("}"):
        s += "}"
    if s.startswith("[") and not s.endswith("]"):
        s += "]"
    return s

def _smart_unescape_code(code: str) -> str:
    # Fixes double escaped newlines in strings while preserving actual newlines
    return code.replace("\\n", "\n").replace("\\\"", "\"")

def _repair_python_syntax(code: str) -> str:
    # Very basic: fix trailing triple quotes or unclosed strings
    if code.count('"""') % 2 != 0:
        code += '"""'
    return code

# --- LiteLLM Callbacks ---

def _success_callback(kwargs, response_obj, start_time, end_time):
    try:
        model = kwargs.get("model", "unknown")
        usage = getattr(response_obj, "usage", None)
        cost = completion_cost(completion_response=response_obj)
        
        _LAST_CALLBACK_DATA.update({
            "cost": cost,
            "usage": usage,
            "finish_reason": response_obj.choices[0].finish_reason if hasattr(response_obj, "choices") else None
        })
    except Exception:
        pass

litellm.success_callback = [_success_callback]
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- Cloud Execution Logic ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    return schema

def _validate_with_pydantic(result: Any, pydantic_class: Type[BaseModel]) -> Any:
    if isinstance(result, str):
        try:
            result = json.loads(_repair_json_string(result))
        except:
            raise SchemaValidationError("Could not parse result string as JSON for validation.")
    return pydantic_class.model_validate(result)

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Optional[Union[Dict, List[Dict]]],
    messages: Optional[List[Dict]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str]
) -> Dict[str, Any]:
    # In a real implementation, this would handle Firebase JWT and requests to 'llmInvoke'
    # Mocking for architectural structure requirement
    cloud_url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    
    payload = {
        "prompt": prompt,
        "inputJson": input_json,
        "messages": messages,
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
        "outputSchema": output_schema,
        "useBatchMode": use_batch_mode,
        "language": language
    }
    
    try:
        # Use short timeout for meta-check, but long for LLM
        # Logic to get JWT would be here
        token = os.getenv("PDD_CLOUD_TOKEN")
        if not token:
            raise CloudFallbackError("No cloud token found")
            
        resp = requests.post(
            cloud_url, 
            json=payload, 
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        
        if resp.status_code == 402:
            raise InsufficientCreditsError("Insufficient credits on PDD Cloud.")
        if resp.status_code in [401, 403]:
            # Clear cache if implemented
            raise CloudFallbackError("Cloud authentication failure.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudInvocationError(f"Cloud request failed: {str(e)}")

# --- Main Invocation Function ---

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
    """Runs a prompt through LiteLLM with routing, retries, and key management."""
    
    logger = logging.getLogger(PDD_LOG_NAME)
    set_verbose_logging(verbose)
    
    # 1. Cloud Pre-check
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_use_cloud = False
    if use_cloud is True:
        should_use_cloud = True
    elif use_cloud is None and not force_local:
        # Check if cloud enabled (dummy check for this structure)
        if os.getenv("PDD_CLOUD_TOKEN"):
            should_use_cloud = True

    if should_use_cloud:
        try:
            effective_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
            cloud_res = _llm_invoke_cloud(
                prompt, input_json, cast(Optional[List[Dict]], messages), strength, 
                temperature, time, verbose, effective_schema, use_batch_mode, language
            )
            if output_pydantic:
                cloud_res["result"] = _validate_with_pydantic(cloud_res["result"], output_pydantic)
            return cloud_res
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 2. Local Setup
    resolver = get_default_resolver()
    load_dotenv(resolver.resolve_project_root() / ".env")
    _initialize_logging()
    
    # 3. Model Selection Logic
    csv_path = None
    priority_paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    for p in priority_paths:
        if p.exists():
            csv_path = p
            break
            
    if not csv_path:
        raise RuntimeError("Could not find llm_model.csv")

    df = pd.read_csv(csv_path)
    
    # Selection algorithm
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    available_df = df.copy()
    
    # Surrogate logic
    if base_model_name and base_model_name in available_df["model"].values:
        base_row = available_df[available_df["model"] == base_model_name].iloc[0]
    else:
        base_row = available_df.iloc[0]
        base_model_name = base_row["model"]

    # Filter and sort for interpolation
    if strength < 0.5:
        # Interpolate cost base down to cheapest
        candidates = available_df[available_df["input"] <= base_row["input"]].sort_values("input", ascending=False)
    elif strength > 0.5:
        # Interpolate ELO base up to highest
        candidates = available_df[available_df["coding_arena_elo"] >= base_row["coding_arena_elo"]].sort_values("coding_arena_elo")
    else:
        candidates = pd.DataFrame([base_row])

    # 4. Iterative Invocation
    last_error = None
    for _, row in candidates.iterrows():
        model_id = row["model"]
        provider = row["provider"]
        key_env = row["api_key"]
        
        # Key Management
        api_key = os.getenv(key_env)
        is_new_key = False
        if not api_key and key_env != "EXISTING_KEY":
            api_key = _get_api_key_interactively(key_env, provider)
            is_new_key = True
            
        if not api_key and key_env != "EXISTING_KEY" and "vertex" not in model_id:
            continue

        # Prepare parameters
        call_kwargs: Dict[str, Any] = {
            "model": model_id,
            "temperature": temperature,
            "timeout": LLM_CALL_TIMEOUT,
            "num_retries": 2,
        }
        
        if api_key: call_kwargs["api_key"] = api_key
        if pd.notna(row.get("base_url")): call_kwargs["base_url"] = row["base_url"]
        
        # Reasoning Config
        reasoning_type = row.get("reasoning_type", "none")
        max_r_tokens = row.get("max_reasoning_tokens", 0)
        
        if reasoning_type == "budget":
            budget = int(time * max_r_tokens)
            if budget > 0:
                if "claude" in model_id:
                    call_kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                    call_kwargs["temperature"] = 1.0 # Anthropic requirement
        elif reasoning_type == "effort":
            effort = "low" if time < 0.3 else "medium" if time < 0.7 else "high"
            if "gpt-5" in model_id:
                call_kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                call_kwargs["reasoning_effort"] = effort

        # Vertex Logic
        if "vertex_ai" in model_id or provider.lower() == "google":
            call_kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
            call_kwargs["vertex_location"] = row.get("location") or os.getenv("VERTEX_LOCATION", "us-central1")
            cred_path = os.getenv("VERTEX_CREDENTIALS")
            if cred_path and Path(cred_path).exists():
                call_kwargs["vertex_credentials"] = Path(cred_path).read_text()

        # Messages
        if messages:
            final_messages = messages
        else:
            prompt_str = prompt or "{input}"
            input_data = input_json or {}
            if isinstance(input_data, list):
                final_messages = [[{"role": "user", "content": prompt_str.format(**item)}] for item in input_data]
            else:
                final_messages = [{"role": "user", "content": prompt_str.format(**input_data)}]

        # Structured Output Config
        if output_pydantic or output_schema:
            s_schema = output_schema or _pydantic_to_json_schema(output_pydantic) # type: ignore
            if row.get("structured_output") is True:
                call_kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "schema": s_schema, "strict": True}
                }
            elif "lm_studio" in model_id:
                call_kwargs["extra_body"] = {"response_format": s_schema}
            elif "groq" in provider.lower():
                call_kwargs["response_format"] = {"type": "json_object"}
                # Instruct Groq in system prompt
                sys_msg = {"role": "system", "content": f"Return JSON matching: {json.dumps(s_schema)}"}
                if isinstance(final_messages[0], list):
                    for m_list in cast(List[List[Dict]], final_messages): m_list.insert(0, sys_msg)
                else:
                    cast(List[Dict], final_messages).insert(0, sys_msg)

        try:
            if "gpt-5" in model_id:
                # Use Responses API
                response = litellm.responses(**call_kwargs, messages=final_messages)
            elif use_batch_mode or isinstance(input_json, list):
                response = batch_completion(**call_kwargs, messages=final_messages)
            else:
                response = completion(**call_kwargs, messages=final_messages)

            # Process Response
            if isinstance(response, list):
                results = [r.choices[0].message.content for r in response]
                thinking = [getattr(r.choices[0].message, "reasoning_content", None) for r in response]
            else:
                raw_result = response.choices[0].message.content
                thinking = getattr(response.choices[0].message, "reasoning_content", None)
                
                # Truncation / Malformed JSON Retries
                if (output_pydantic or output_schema) and raw_result:
                    try:
                        processed_result = json.loads(_repair_json_string(raw_result))
                        if output_pydantic:
                            processed_result = output_pydantic.model_validate(processed_result)
                    except Exception as e:
                        # Logic for cache bypass retry would go here
                        raise SchemaValidationError(f"Validation failed: {e}")
                else:
                    processed_result = raw_result

                return {
                    "result": processed_result,
                    "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
                    "model_name": model_id,
                    "thinking_output": thinking
                }

        except Exception as e:
            last_error = e
            if "Authentication" in str(e) and is_new_key:
                # Re-prompt logic
                os.environ.pop(key_env, None)
                return llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic, output_schema, time, use_batch_mode, messages, language, use_cloud)
            
            if "SchemaValidationError" in str(type(e)):
                logger.warning(f"Schema validation failed for {model_id}, trying fallback.")
                continue
            
            logger.error(f"Error invoking {model_id}: {e}")
            continue

    raise RuntimeError(f"All model candidates failed. Last error: {last_error}")

if __name__ == "__main__":
    # Quick test
    # Note: This requires a valid llm_model.csv and environment setup to run
    try:
        print(llm_invoke(prompt="Say hello in {lang}", input_json={"lang": "Python"}))
    except Exception as e:
        print(f"Test failed (expected if environment not set): {e}")