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
from . import (
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    EXTRACTION_STRENGTH,
)
from .path_resolution import get_default_resolver

# --- Constants & Configuration ---
LLM_CALL_TIMEOUT = 120
PDD_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO").upper()
LITELLM_LOG_LEVEL = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
PDD_ENVIRONMENT = os.getenv("PDD_ENVIRONMENT", "production").lower()
PDD_VERBOSE_LOGGING = os.getenv("PDD_VERBOSE_LOGGING") == "1"

console = Console()
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}


class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic or JSON schema validation."""
    pass


class CloudFallbackError(Exception):
    """Recoverable errors that trigger local fallback (Network, Auth, 5xx)."""
    pass


class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass


class InsufficientCreditsError(Exception):
    """HTTP 402 - Payment Required."""
    pass


# --- Logging Setup ---

def setup_logging() -> None:
    """Configures hierarchical logging based on environment variables."""
    level = logging.DEBUG if PDD_VERBOSE_LOGGING else getattr(logging, PDD_LOG_LEVEL, logging.INFO)
    if PDD_ENVIRONMENT == "production" and not PDD_VERBOSE_LOGGING:
        level = max(level, logging.WARNING)

    logging.basicConfig(level=level, format="%(name)s - %(levelname)s - %(message)s")
    logger.setLevel(level)
    litellm_logger.setLevel(getattr(logging, LITELLM_LOG_LEVEL, logging.WARNING))
    
    # LiteLLM specifics
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    litellm.telemetry = False


def set_verbose_logging(enabled: bool = True) -> None:
    """Toggles DEBUG level logging."""
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    if enabled:
        litellm.set_verbose = True


# --- Cache & Provider Setup ---

def configure_litellm_cache(project_root: Path) -> None:
    """Configures GCS (S3-compatible) or SQLite caching."""
    if os.getenv("LITELLM_CACHE_DISABLE") == "1":
        return

    gcs_id = os.getenv("GCS_HMAC_ACCESS_KEY_ID")
    gcs_secret = os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
    bucket = os.getenv("GCS_BUCKET_NAME")

    if gcs_id and gcs_secret and bucket:
        # Targeting GCS via S3 implementation in LiteLLM
        litellm.cache = litellm.Cache(
            type="s3",
            s3_bucket_name=bucket,
            s3_region_name="us-east-1",  # Placeholder for GCS
            s3_api_version="v4",
            s3_endpoint_url="https://storage.googleapis.com",
            s3_access_key_id=gcs_id,
            s3_secret_access_key=gcs_secret
        )
    else:
        cache_path = project_root / "litellm_cache.sqlite"
        litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(cache_path))


def success_callback(kwargs: Dict[str, Any], response_obj: Any) -> None:
    """Captured usage data from LiteLLM successful calls."""
    global _LAST_CALLBACK_DATA
    try:
        cost = completion_cost(completion_response=response_obj)
        _LAST_CALLBACK_DATA = {
            "cost": cost or 0.0,
            "usage": getattr(response_obj, "usage", {}),
            "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None
        }
    except Exception:
        _LAST_CALLBACK_DATA = {"cost": 0.0}


litellm.success_callback = [success_callback]

# --- Helper Utilities ---

def _detect_wsl() -> bool:
    """Checks if running inside Windows Subsystem for Linux."""
    return "microsoft" in open("/proc/version", "r").read().lower() if Path("/proc/version").exists() else "WSL_DISTRO_NAME" in os.environ


def _sanitize_key(key: str) -> str:
    """Removes whitespace and control characters from API keys."""
    return key.strip().replace("\r", "").replace("\n", "")


def _get_env_path(project_root: Path) -> Path:
    """Locates or creates the .env file in the project root."""
    return project_root / ".env"


def _handle_missing_api_key(key_name: str, project_root: Path) -> bool:
    """Interactively fetches and saves missing API keys."""
    if os.getenv("PDD_FORCE"):
        return False

    console.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name}")
    raw_key = input(f"Please enter value for {key_name}: ")
    clean_key = _sanitize_key(raw_key)

    env_path = _get_env_path(project_root)
    if not env_path.exists():
        env_path.touch()

    set_key(str(env_path), key_name, clean_key)
    os.environ[key_name] = clean_key

    console.print(f"[green]Key saved to {env_path}[/green]")
    if _detect_wsl() and ("\r" in raw_key or "\n" in raw_key):
        console.print("[yellow]WSL Warning:[/yellow] Detected line endings in input. Sanitized.")
    
    return True


def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively enforces 'required' for all properties in JSON schema."""
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for val in props.values():
            _ensure_all_properties_required(val)
    elif schema.get("items"):
        _ensure_all_properties_required(schema["items"])


def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    """Recursively sets additionalProperties: false to enforce strict schemas."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        for val in schema.get("properties", {}).values():
            _add_additional_properties_false(val)
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _add_additional_properties_false(sub)


def _repair_json_truncation(json_str: str) -> str:
    """Attempts to close truncated JSON strings/objects."""
    json_str = json_str.strip()
    # Basic balancing
    open_braces = json_str.count("{") - json_str.count("}")
    open_brackets = json_str.count("[") - json_str.count("]")
    
    if open_braces > 0:
        json_str += "}" * open_braces
    if open_brackets > 0:
        json_str += "]" * open_brackets
    return json_str


def _smart_unescape_code(content: str) -> str:
    """Fixes double-escaped newlines in code blocks while preserving syntax."""
    return content.replace("\\n", "\n").replace("\\\"", "\"")


def _repair_python_syntax(code: str) -> str:
    """Simple heuristics to fix common LLM Python syntax errors."""
    code = code.strip()
    if (code.count('"""') % 2) != 0:
        code += '"""'
    if (code.count("'''") % 2) != 0:
        code += "'''"
    return code


# --- Cloud Invocation ---

def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    schema["title"] = pydantic_class.__name__
    return schema


def _llm_invoke_cloud(
    payload: Dict[str, Any],
    timeout: int = 300
) -> Dict[str, Any]:
    """Calls the PDD Cloud llmInvoke endpoint."""
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No PDD_CLOUD_TOKEN found")

    url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=timeout)
        if response.status_code == 402:
            raise InsufficientCreditsError("Insufficient PDD Cloud credits")
        if response.status_code in [401, 403]:
            # Token might be expired
            raise CloudFallbackError("Cloud authentication failed")
        if response.status_code >= 500:
            raise CloudFallbackError(f"Cloud server error: {response.status_code}")
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        raise CloudFallbackError(f"Cloud connection error: {str(e)}")


# --- Model Selection Logic ---

def _load_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root("pdd_path_then_marker_then_cwd")
    
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        project_root / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": float(row.get("input_cost_per_m", 0)),
                    "output": float(row.get("output_cost_per_m", 0))
                }
            return df
    raise FileNotFoundError("Could not locate llm_model.csv")


def _select_models(
    df: pd.DataFrame, 
    strength: float, 
    use_cloud_forced: Optional[bool]
) -> List[pd.Series]:
    """Filters and ranks models based on strength and availability."""
    # Filter by API key availability (unless forcing cloud)
    if not use_cloud_forced:
        def has_key(row):
            key = row.get("api_key")
            if not key or key == "EXISTING_KEY": return True
            return os.getenv(key) is not None
        available = df[df.apply(has_key, axis=1)].copy()
    else:
        available = df.copy()

    if available.empty:
        return [df.iloc[0]]

    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row = available[available["model"] == base_model_name]
    
    if base_row.empty:
        base_row = available.iloc[:1]
    
    base_val = base_row.iloc[0]
    
    if strength == 0.5:
        # Priority: Base, then higher ELO
        others = available[available["model"] != base_val["model"]].sort_values("coding_arena_elo", ascending=False)
        return [base_val] + [r for _, r in others.iterrows()]
    
    if strength < 0.5:
        # Interpolate by cost (cheapest to base)
        candidates = available[available["coding_arena_elo"] <= base_val["coding_arena_elo"]]
        candidates = candidates.sort_values("input_cost_per_m", ascending=True)
    else:
        # Interpolate by ELO (base to highest)
        candidates = available[available["coding_arena_elo"] >= base_val["coding_arena_elo"]]
        candidates = candidates.sort_values("coding_arena_elo", ascending=False)
        
    return [r for _, r in candidates.iterrows()]


# --- Core Function ---

def llm_invoke(
    prompt: Optional[str] = None,
    input_json: Optional[Union[Dict, List[Dict]]] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.1,
    verbose: bool = False,
    output_pydantic: Optional[Type[BaseModel]] = None,
    output_schema: Optional[Dict] = None,
    time: float = DEFAULT_TIME,
    use_batch_mode: bool = False,
    messages: Optional[Union[List[Dict], List[List[Dict]]]] = None,
    language: Optional[str] = None,
    use_cloud: Optional[bool] = None,
) -> Dict[str, Any]:
    """Runs a prompt with a given input using LiteLLM with fallback and reasoning support."""
    
    # 1. Initialization
    setup_logging()
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root("pdd_path_then_marker_then_cwd")
    load_dotenv(project_root / ".env")
    configure_litellm_cache(project_root)

    if verbose:
        set_verbose_logging(True)

    # 2. Cloud Execution Check
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    should_use_cloud = False
    if use_cloud is True:
        should_use_cloud = True
    elif use_cloud is None and not force_local:
        # Check if cloud is enabled via env/config (Simplified for this snippet)
        should_use_cloud = os.getenv("PDD_CLOUD_ENABLED") == "1"

    if should_use_cloud:
        payload = {
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
        try:
            cloud_res = _llm_invoke_cloud(payload)
            # Validate output if pydantic provided
            res_content = cloud_res["result"]
            if output_pydantic:
                res_content = output_pydantic.model_validate(res_content)
            
            return {
                "result": res_content,
                "cost": cloud_res.get("totalCost", 0.0),
                "model_name": cloud_res.get("modelName", "cloud-proxy"),
                "thinking_output": cloud_res.get("thinkingOutput")
            }
        except InsufficientCreditsError:
            raise
        except (CloudFallbackError, CloudInvocationError) as e:
            console.print(f"[yellow]Cloud failed, falling back to local: {str(e)}[/yellow]")

    # 3. Local Model Preparation
    df_models = _load_model_csv()
    candidate_rows = _select_models(df_models, strength, use_cloud)
    
    # Format messages if not provided
    if not messages:
        if not prompt:
            raise ValueError("Either 'prompt' or 'messages' must be provided.")
        
        # Simple placeholder replacement
        system_content = "You are a helpful assistant."
        user_content = prompt
        if input_json:
            if isinstance(input_json, dict):
                for k, v in input_json.items():
                    user_content = user_content.replace(f"{{{{{k}}}}}", str(v))
            elif isinstance(input_json, list) and not use_batch_mode:
                 user_content = user_content.replace("{{input}}", json.dumps(input_json))

        messages = [
            {"role": "system", "content": system_content},
            {"role": "user", "content": user_content}
        ]

    # 4. Iterative Invocation
    last_error = None
    newly_acquired_keys = set()

    for model_row in candidate_rows:
        model_name = model_row["model"]
        provider = model_row["provider"]
        api_key_env = model_row.get("api_key")
        
        # Key Management
        if api_key_env and api_key_env != "EXISTING_KEY":
            if not os.getenv(api_key_env):
                if _handle_missing_api_key(api_key_env, project_root):
                    newly_acquired_keys.add(api_key_env)
                else:
                    continue # Skip if key missing in non-interactive

        # Reasoning & Params
        kwargs: Dict[str, Any] = {
            "model": model_name,
            "messages": messages,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        # Reasoning Logic
        r_type = model_row.get("reasoning_type", "none")
        max_r_tokens = int(model_row.get("max_reasoning_tokens", 0))
        
        if r_type == "budget" and max_r_tokens > 0:
            budget = int(time * max_r_tokens)
            if "anthropic" in provider.lower():
                kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
                kwargs["temperature"] = 1.0 # Anthropic requirement
        elif r_type == "effort":
            effort = "medium"
            if time < 0.3: effort = "low"
            elif time > 0.7: effort = "high"
            
            if "gpt-5" in model_name: # Conceptual PDD requirement for future OpenAI
                kwargs["reasoning"] = {"effort": effort, "summary": "auto"}
            else:
                kwargs["reasoning_effort"] = effort

        # Structured Output Handling
        active_schema = output_schema or (_pydantic_to_json_schema(output_pydantic) if output_pydantic else None)
        if active_schema:
            if model_row.get("structured_output") == 1:
                kwargs["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "schema": active_schema, "strict": True}
                }
            elif "groq" in provider.lower():
                kwargs["response_format"] = {"type": "json_object"}
                messages[0]["content"] += f"\nReturn JSON matching this schema: {json.dumps(active_schema)}"

        # Vertex Specifics
        if "vertex" in provider.lower() or model_name.startswith("vertex"):
            kwargs["vertex_project"] = os.getenv("VERTEX_PROJECT")
            kwargs["vertex_location"] = model_row.get("location") or os.getenv("VERTEX_LOCATION", "us-central1")
            cred_path = os.getenv("VERTEX_CREDENTIALS")
            if cred_path and Path(cred_path).exists():
                kwargs["vertex_credentials"] = Path(cred_path).read_text()

        # LM Studio Overrides
        if provider.lower() == "lm_studio":
            kwargs["base_url"] = os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")
            kwargs["api_key"] = "lm-studio"
            if active_schema:
                kwargs["extra_body"] = {"guided_json": active_schema}

        # 5. Call LLM
        try:
            if "gpt-5" in model_name:
                # Use Responses API for reasoning-specific models if needed
                response = getattr(litellm, "responses", completion)(**kwargs)
            elif use_batch_mode and isinstance(messages, list) and isinstance(messages[0], list):
                response = batch_completion(**kwargs)
            else:
                response = completion(**kwargs)

            # 6. Response Parsing
            if use_batch_mode:
                results = []
                for res in response:
                    results.append(res.choices[0].message.content)
                return {"result": results, "cost": sum(getattr(r, "_cost", 0) for r in response), "model_name": model_name}

            content = response.choices[0].message.content
            if content is None:
                # Handle null content with cache bypass retry
                kwargs["extra_headers"] = {"Cache-Control": "no-cache"}
                response = completion(**kwargs)
                content = response.choices[0].message.content or ""

            # Extract thinking
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            if not thinking and hasattr(response, "_hidden_params"):
                 thinking = response._hidden_params.get("thinking")

            # JSON Parsing & Validation
            result_obj: Any = content
            if active_schema:
                try:
                    # Clean up the string
                    json_str = content.strip()
                    if "```json" in json_str:
                        json_str = json_str.split("```json")[1].split("```")[0].strip()
                    
                    try:
                        parsed = json.loads(json_str)
                    except json.JSONDecodeError:
                        json_str = _repair_json_truncation(json_str)
                        parsed = json.loads(json_str)
                    
                    # Code field unescaping
                    if isinstance(parsed, dict):
                        for k, v in parsed.items():
                            if isinstance(v, str) and any(x in k.lower() for x in ["code", "script", "program"]):
                                parsed[k] = _smart_unescape_code(v)
                                if language in ["python", None]:
                                    parsed[k] = _repair_python_syntax(parsed[k])

                    if output_pydantic:
                        result_obj = output_pydantic.model_validate(parsed)
                    else:
                        result_obj = parsed
                        
                except Exception as e:
                    logger.warning(f"Schema validation failed for {model_name}: {str(e)}")
                    raise SchemaValidationError(str(e))

            cost = _LAST_CALLBACK_DATA.get("cost", 0.0)
            if cost == 0 and model_name in _MODEL_RATE_MAP:
                usage = _LAST_CALLBACK_DATA.get("usage", {})
                in_tokens = usage.get("prompt_tokens", 0)
                out_tokens = usage.get("completion_tokens", 0)
                rates = _MODEL_RATE_MAP[model_name]
                cost = (in_tokens * rates["input"] + out_tokens * rates["output"]) / 1_000_000

            return {
                "result": result_obj,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except litellm.AuthenticationError as e:
            if api_key_env in newly_acquired_keys:
                console.print(f"[red]Authentication failed with new key {api_key_env}. Re-prompting...[/red]")
                _handle_missing_api_key(api_key_env, project_root)
                # Recurse once for the same model
                return llm_invoke(**locals()) 
            last_error = e
            continue
        except SchemaValidationError as e:
            last_error = e
            continue # Fallback to next model
        except Exception as e:
            if "anthropic" in provider.lower() and "temperature" in str(e).lower():
                kwargs["temperature"] = 1.0
                # retry once immediately
                try:
                    response = completion(**kwargs)
                    # (Process response similar to above - simplified for flow)
                except: pass
            logger.error(f"Error calling {model_name}: {str(e)}")
            last_error = e
            continue

    raise RuntimeError(f"All models failed. Last error: {str(last_error)}")


if __name__ == "__main__":
    # Example execution
    try:
        res = llm_invoke(prompt="Write a hello world in {{lang}}", input_json={"lang": "python"}, strength=0.5)
        console.print(res)
    except Exception as err:
        console.print(f"[bold red]Failed:[/bold red] {err}")