from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, cast

import litellm
import pandas as pd
from dotenv import load_dotenv, set_key
from litellm import batch_completion, completion, completion_cost
from pydantic import BaseModel
from rich.console import Console

# Internal relative imports as per requirements
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

# Global Configuration
CONSOLE = Console()
LOGGER = logging.getLogger("pdd.llm_invoke")
LITELLM_LOGGER = logging.getLogger("litellm")

_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}

# --- Exceptions ---

class SchemaValidationError(Exception):
    """Raised when LLM output fails Pydantic validation."""
    pass

class CloudFallbackError(Exception):
    """Recoverable cloud error (timeout, network, auth)."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud error."""
    pass

class InsufficientCreditsError(Exception):
    """402 Payment Required."""
    pass

# --- Logging & Initialization ---

def setup_file_logging() -> None:
    from logging.handlers import RotatingFileHandler
    resolver = get_default_resolver()
    log_dir = resolver.resolve_project_root() / "logs"
    log_dir.mkdir(exist_ok=True)
    handler = RotatingFileHandler(
        log_dir / "pdd.log", maxBytes=10 * 1024 * 1024, backupCount=5
    )
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    LOGGER.addHandler(handler)

def set_verbose_logging(enabled: bool) -> None:
    level = logging.DEBUG if enabled else logging.INFO
    LOGGER.setLevel(level)

def _init_litellm_cache() -> None:
    if os.getenv("LITELLM_CACHE_DISABLE") == "1":
        return
    
    if os.getenv("GCS_BUCKET_NAME"):
        # S3-compatible cache targeting GCS via HMAC
        litellm.cache = litellm.Cache(
            type="s3",
            s3_bucket=os.getenv("GCS_BUCKET_NAME"),
            s3_region_name="us-central1",
            s3_api_version="s3v4",
            s3_endpoint_url="https://storage.googleapis.com"
        )
    else:
        # Fallback to local SQLite
        resolver = get_default_resolver()
        cache_path = resolver.resolve_project_root() / "litellm_cache.sqlite"
        litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(cache_path))

def _litellm_success_callback(kwargs: Dict, response_obj: Any) -> None:
    """Capture usage and cost info."""
    try:
        cost = completion_cost(completion_response=response_obj)
        usage = getattr(response_obj, "usage", {})
        _LAST_CALLBACK_DATA["cost"] = cost
        _LAST_CALLBACK_DATA["usage"] = usage
    except Exception:
        pass

litellm.success_callback = [_litellm_success_callback]
litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"

# --- API Key Management ---

def _manage_api_key(provider: str, key_name: str) -> bool:
    """Interactively fetch and save missing API keys."""
    current_val = os.getenv(key_name)
    if current_val and current_val not in ["", "EXISTING_KEY", "lm-studio"]:
        return True
    
    if os.getenv("PDD_FORCE") == "1":
        return False

    CONSOLE.print(f"[bold yellow]Missing API Key for {provider} ({key_name}).[/bold yellow]")
    new_key = input(f"Enter {key_name}: ").strip()
    
    # WSL Sanitization
    is_wsl = "wsl" in os.getenv("WSL_DISTRO_NAME", "").lower() or Path("/proc/version").read_text().lower().find("microsoft") != -1
    if is_wsl:
        new_key = "".join(c for c in new_key if ord(c) >= 32)

    if new_key:
        resolver = get_default_resolver()
        env_path = resolver.resolve_project_root() / ".env"
        set_key(str(env_path), key_name, new_key)
        os.environ[key_name] = new_key
        CONSOLE.print(f"[green]Key saved to {env_path}.[/green] [red]Security Warning: Keep this file private![/red]")
        return True
    return False

# --- Model Selection Logic ---

def _get_model_candidates() -> pd.DataFrame:
    resolver = get_default_resolver()
    paths = [
        Path.home() / ".pdd" / "llm_model.csv",
        resolver.resolve_project_root() / ".pdd" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
        Path(__file__).parent / "data" / "llm_model.csv"
    ]
    for p in paths:
        if p.exists():
            df = pd.read_csv(p)
            for _, row in df.iterrows():
                _MODEL_RATE_MAP[row["model"]] = {
                    "input": row.get("input_cost", 0),
                    "output": row.get("output_cost", 0)
                }
            return df
    raise RuntimeError("llm_model.csv not found.")

def _select_model(strength: float) -> str:
    df = _get_model_candidates()
    # Filter by API key availability
    df = df[df.apply(lambda r: os.getenv(str(r["api_key"])) is not None or r["api_key"] == "lm-studio", axis=1)]
    
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_model = df[df["model"] == base_model_name].iloc[0] if base_model_name in df["model"].values else df.iloc[0]

    if strength == 0.5:
        return cast(str, base_model["model"])
    
    if strength < 0.5:
        # Interpolate by cost (base -> cheapest)
        df["total_cost"] = df["input_cost"] + df["output_cost"]
        candidates = df[df["total_cost"] <= (base_model["input_cost"] + base_model["output_cost"])]
        candidates = candidates.sort_values("total_cost")
    else:
        # Interpolate by ELO (base -> highest)
        candidates = df[df["coding_arena_elo"] >= base_model["coding_arena_elo"]]
        candidates = candidates.sort_values("coding_arena_elo", ascending=False)
    
    idx = int(abs(strength - 0.5) * 2 * (len(candidates) - 1))
    return cast(str, candidates.iloc[idx]["model"])

# --- JSON/Python Repair Utilities ---

def _repair_json(raw: str) -> str:
    # Handle fenced blocks
    match = re.search(r"```json\s*(.*?)\s*```", raw, re.DOTALL)
    if match: return match.group(1)
    # Balanced braces extraction
    start = raw.find('{')
    if start != -1:
        count = 0
        for i, char in enumerate(raw[start:], start):
            if char == '{': count += 1
            elif char == '}': count -= 1
            if count == 0: return raw[start:i+1]
    return raw

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        if "properties" in schema:
            schema["required"] = list(schema["properties"].keys())
            for prop in schema["properties"].values():
                _ensure_all_properties_required(prop)
        schema["additionalProperties"] = False
    elif schema.get("type") == "array" and "items" in schema:
        _ensure_all_properties_required(schema["items"])

# --- LLM Invoke Main Function ---

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
    """Execute LLM call via LiteLLM with fallback, key management, and cloud support."""
    load_dotenv()
    set_verbose_logging(verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1")
    _init_litellm_cache()

    # Cloud Execution Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is True or (use_cloud is None and not force_local):
        try:
            # Placeholder for _llm_invoke_cloud logic
            # return _llm_invoke_cloud(...)
            pass
        except CloudFallbackError as e:
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")

    # Local Model Selection
    model_name = _select_model(strength)
    df = _get_model_candidates()
    model_row = df[df["model"] == model_name].iloc[0]
    
    # Prepare Messages
    final_messages = messages
    if not final_messages:
        if not prompt: raise ValueError("Prompt required if messages not provided.")
        text_content = prompt
        if input_json:
            # Simple template replacement
            for k, v in (input_json if isinstance(input_json, dict) else {}).items():
                text_content = text_content.replace(f"{{{{{k}}}}}", str(v))
        final_messages = [{"role": "user", "content": text_content}]

    # Reasoning Config
    extra_params = {}
    rtype = model_row.get("reasoning_type", "none")
    max_rt = int(model_row.get("max_reasoning_tokens", 0))
    if rtype == "budget":
        extra_params["thinking"] = {"type": "enabled", "budget_tokens": int(time * max_rt)}
        temperature = 1.0 # Anthropic requirement
    elif rtype == "effort":
        effort = "low" if time < 0.3 else "medium" if time < 0.7 else "high"
        extra_params["reasoning_effort"] = effort

    # Structured Output Config
    if output_pydantic or output_schema:
        schema = output_schema or output_pydantic.model_json_schema() # type: ignore
        _ensure_all_properties_required(schema)
        if model_row.get("structured_output") == 1:
            extra_params["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "output", "schema": schema, "strict": True}
            }

    # API Execution
    try:
        if use_batch_mode:
            response = batch_completion(
                model=model_name,
                messages=final_messages, # type: ignore
                temperature=temperature,
                **extra_params
            )
            result = [r.choices[0].message.content for r in response]
        else:
            # Handle gpt-5 or specific reasoning models via litellm.responses if needed
            response = completion(
                model=model_name,
                messages=final_messages, # type: ignore
                temperature=temperature,
                num_retries=2,
                timeout=120,
                **extra_params
            )
            result = response.choices[0].message.content

        # Post-processing
        thinking = response.choices[0].message.get("reasoning_content") or \
                   getattr(response, "_hidden_params", {}).get("thinking")
        
        final_result = result
        if (output_pydantic or output_schema) and isinstance(result, str):
            cleaned = _repair_json(result)
            final_result = json.loads(cleaned)
            if output_pydantic:
                final_result = output_pydantic.model_validate(final_result)

        return {
            "result": final_result,
            "cost": _LAST_CALLBACK_DATA.get("cost", 0.0),
            "model_name": model_name,
            "thinking_output": thinking
        }

    except Exception as e:
        LOGGER.error(f"LLM call failed: {e}")
        # Auth retry or model fallback logic would go here
        raise RuntimeError(f"Failed to invoke LLM: {e}")

if __name__ == "__main__":
    # Test call
    res = llm_invoke(prompt="Hello, who are you?", strength=0.5)
    CONSOLE.print(res)