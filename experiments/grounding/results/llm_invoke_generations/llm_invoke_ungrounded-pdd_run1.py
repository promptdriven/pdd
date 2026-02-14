from __future__ import annotations

import os
import json
import logging
import platform
import re
import ast
from pathlib import Path
from typing import Any, Dict, List, Optional, Type, Union, TYPE_CHECKING
from logging.handlers import RotatingFileHandler

import pandas as pd
import litellm
import requests
from dotenv import load_dotenv, set_key
from rich.console import Console
from pydantic import BaseModel

# Internal imports (relative per requirement)
from . import (
    EXTRACTION_STRENGTH,
    DEFAULT_STRENGTH,
    DEFAULT_TIME,
    LLM_CALL_TIMEOUT,
)
from .path_resolution import get_default_resolver

if TYPE_CHECKING:
    from litellm.utils import ModelResponse

# --- Constants & Configuration ---
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Dict[str, float]] = {}
CONSOLE = Console()

# Logging
logger = logging.getLogger("pdd.llm_invoke")
litellm_logger = logging.getLogger("litellm")

# Exception Classes
class SchemaValidationError(Exception):
    """Raised when the LLM output fails Pydantic validation or JSON parsing."""
    pass

class CloudFallbackError(Exception):
    """Recoverable errors that should trigger local fallback."""
    pass

class CloudInvocationError(Exception):
    """Non-recoverable cloud errors."""
    pass

class InsufficientCreditsError(Exception):
    """Raised on 402 Payment Required. No fallback."""
    pass

# --- Helper Functions ---

def setup_file_logging(log_path: str = "pdd_llm.log") -> None:
    handler = RotatingFileHandler(log_path, maxBytes=10 * 1024 * 1024, backupCount=5)
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)

def set_verbose_logging(enabled: bool) -> None:
    level = logging.DEBUG if enabled else logging.INFO
    logger.setLevel(level)
    if enabled:
        litellm.set_verbose = True

def _is_wsl() -> bool:
    if platform.system() == "Linux":
        if "microsoft" in platform.release().lower():
            return True
        try:
            with open("/proc/version", "r") as f:
                if "microsoft" in f.read().lower():
                    return True
        except FileNotFoundError:
            pass
    return "WSL_DISTRO_NAME" in os.environ

def _sanitize_key(key: str) -> str:
    return key.strip().replace("\r", "").replace("\n", "")

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    """Recursively ensures all properties in a JSON schema are marked as required."""
    if schema.get("type") == "object":
        props = schema.get("properties", {})
        if props:
            schema["required"] = list(props.keys())
        for prop in props.values():
            _ensure_all_properties_required(prop)
    
    # Handle containers
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _ensure_all_properties_required(sub)
    if "items" in schema:
        _ensure_all_properties_required(schema["items"])
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _ensure_all_properties_required(sub)

def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    """Recursively sets additionalProperties: false on all object schemas."""
    if schema.get("type") == "object":
        schema["additionalProperties"] = False
        props = schema.get("properties", {})
        for prop in props.values():
            _add_additional_properties_false(prop)
    
    for key in ["anyOf", "oneOf", "allOf"]:
        if key in schema:
            for sub in schema[key]:
                _add_additional_properties_false(sub)
    if "items" in schema:
        _add_additional_properties_false(schema["items"])
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            _add_additional_properties_false(sub)

def _repair_python_syntax(code: str) -> str:
    """Fixes common LLM truncation issues in Python code."""
    code = code.strip()
    # Simple fix for trailing quotes/unfinished blocks
    if code.count('"""') % 2 != 0:
        code += '\n"""'
    if code.count("'''") % 2 != 0:
        code += "\n'''"
    return code

def _smart_unescape_code(json_str: str) -> str:
    """Unescapes double-escaped newlines while preserving literals."""
    return json_str.replace("\\\\n", "\\n")

def _parse_llm_json(content: str) -> Any:
    """Parses JSON from LLM response with multiple fallback strategies."""
    # 1. Try regex for markdown block
    match = re.search(r"```json\s*(.*?)\s*```", content, re.DOTALL)
    if match:
        content = match.group(1)
    
    # 2. Try simple load
    try:
        return json.loads(content)
    except json.JSONDecodeError:
        pass

    # 3. Balanced brace extraction
    start = content.find("{")
    end = content.rfind("}")
    if start != -1 and end != -1:
        try:
            return json.loads(content[start:end+1])
        except json.JSONDecodeError:
            pass
            
    # 4. Truncation repair (naive)
    if content.strip().startswith("{") and not content.strip().endswith("}"):
        try:
            return json.loads(content + '}')
        except:
            pass
            
    raise SchemaValidationError("Could not parse JSON from response content.")

# --- LiteLLM Callbacks ---
def _success_callback(kwargs, response_obj: "ModelResponse"):
    global _LAST_CALLBACK_DATA
    _LAST_CALLBACK_DATA = {
        "usage": getattr(response_obj, "usage", {}),
        "finish_reason": response_obj.choices[0].finish_reason if response_obj.choices else None,
        "model": kwargs.get("model")
    }

litellm.success_callback = [_success_callback]

# --- Core Logic ---

def _get_api_key_interactively(key_name: str, model_row: pd.Series) -> str:
    """Fetches key from env or prompts user and saves to .env."""
    key = os.getenv(key_name)
    if key:
        return key

    if os.getenv("PDD_FORCE") == "1":
        logger.debug(f"PDD_FORCE enabled, skipping interactive prompt for {key_name}")
        return ""

    CONSOLE.print(f"[bold yellow]Missing API Key:[/bold yellow] {key_name} for model {model_row['model']}")
    new_key = input(f"Please enter your {key_name}: ").strip()
    new_key = _sanitize_key(new_key)
    
    if not new_key:
        return ""

    # Save to .env at project root
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    env_path = project_root / ".env"
    
    set_key(str(env_path), key_name, new_key)
    os.environ[key_name] = new_key
    
    CONSOLE.print(f"[bold green]Success:[/bold green] Key saved to {env_path}")
    logger.warning(f"Security: API key {key_name} was saved to {env_path}")
    
    return new_key

def _resolve_model_csv() -> pd.DataFrame:
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    
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
                    "input": float(row["input"]),
                    "output": float(row["output"])
                }
            return df
    raise RuntimeError("Could not find llm_model.csv")

def _select_model_candidates(strength: float) -> List[pd.Series]:
    df = _resolve_model_csv()
    base_name = os.getenv("PDD_MODEL_DEFAULT")
    
    # Selection logic
    if base_name and base_name in df["model"].values:
        base_model = df[df["model"] == base_name].iloc[0]
    else:
        base_model = df.iloc[0] # Surrogate

    if strength == 0.5:
        candidates = [base_model]
        others = df[df["model"] != base_model["model"]].sort_values("coding_arena_elo", ascending=False)
        return candidates + [row for _, row in others.iterrows()]
    
    if strength < 0.5:
        # Interpolate by cost (base down to cheapest)
        filtered = df[df["input"] <= base_model["input"]]
        candidates = filtered.sort_values("input", ascending=False)
    else:
        # Interpolate by ELO (base up to highest)
        filtered = df[df["coding_arena_elo"] >= base_model["coding_arena_elo"]]
        candidates = filtered.sort_values("coding_arena_elo", ascending=True)

    return [row for _, row in candidates.iterrows()]

def _prepare_reasoning_params(model_row: pd.Series, time_val: float) -> Dict[str, Any]:
    r_type = str(model_row.get("reasoning_type", "none")).lower()
    max_tokens = int(model_row.get("max_reasoning_tokens", 0))
    
    params = {}
    if r_type == "budget" and max_tokens > 0:
        params["thinking"] = {
            "type": "enabled",
            "budget_tokens": int(time_val * max_tokens)
        }
    elif r_type == "effort":
        effort = "low" if time_val < 0.33 else "medium" if time_val < 0.66 else "high"
        # Check for OpenAI gpt-5 or specific reasoning models
        if "gpt-5" in str(model_row["model"]):
            params["reasoning"] = {"effort": effort, "summary": "auto"}
        else:
            params["reasoning_effort"] = effort
    return params

def _llm_invoke_cloud(
    prompt: Optional[str],
    input_json: Any,
    messages: Optional[List[Dict]],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    output_schema: Optional[Dict],
    use_batch_mode: bool,
    language: Optional[str],
) -> Dict[str, Any]:
    # Placeholder for cloud URL - usually retrieved from a config
    cloud_url = "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke"
    
    # Get Auth token (Mock logic for this exercise)
    token = os.getenv("PDD_CLOUD_TOKEN")
    if not token:
        raise CloudFallbackError("No cloud token found.")

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
        "language": language,
        "use_cloud": False # Prevent recursion
    }

    try:
        resp = requests.post(
            cloud_url,
            json=payload,
            headers={"Authorization": f"Bearer {token}"},
            timeout=300
        )
        if resp.status_code == 402:
            raise InsufficientCreditsError("PDD Cloud: Insufficient Credits.")
        if resp.status_code in [401, 403]:
            # Clear cache logic here if needed
            raise CloudFallbackError("Authentication failed on cloud.")
        if resp.status_code >= 500:
            raise CloudFallbackError(f"Cloud Server Error: {resp.status_code}")
        
        resp.raise_for_status()
        return resp.json()
    except requests.exceptions.RequestException as e:
        raise CloudInvocationError(f"Cloud request failed: {e}")

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
    """Execute an LLM prompt with automated model selection, key management, and cloud fallback."""
    
    # 1. Startup & Environment
    resolver = get_default_resolver()
    project_root = resolver.resolve_project_root()
    load_dotenv(project_root / ".env")
    
    set_verbose_logging(verbose or os.getenv("PDD_VERBOSE_LOGGING") == "1")
    
    # 2. Cloud Path
    force_local = os.getenv("PDD_FORCE_LOCAL") == "1"
    if use_cloud is True or (use_cloud is None and not force_local):
        try:
            # We must convert Pydantic to Schema for transport
            schema = output_schema
            if output_pydantic:
                schema = output_pydantic.model_json_schema()
                _ensure_all_properties_required(schema)
            
            res = _llm_invoke_cloud(
                prompt, input_json, messages, strength, temperature, 
                time, verbose, schema, use_batch_mode, language
            )
            # Validate result if local pydantic provided
            if output_pydantic and "result" in res:
                if isinstance(res["result"], dict):
                    res["result"] = output_pydantic.model_validate(res["result"])
            return res
        except (CloudFallbackError, CloudInvocationError) as e:
            CONSOLE.print(f"[yellow]Cloud execution failed, falling back to local: {e}[/yellow]")
        except InsufficientCreditsError:
            raise

    # 3. Local Execution Path
    candidates = _select_model_candidates(strength)
    
    # Litellm config
    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "True").lower() == "true"
    
    # Cache Configuration
    if os.getenv("LITELLM_CACHE_DISABLE") != "1":
        if os.getenv("GCS_BUCKET_NAME"):
            litellm.cache = litellm.Cache(
                type="s3",
                s3_bucket_name=os.getenv("GCS_BUCKET_NAME"),
                s3_region_name="auto",
                s3_api_base="https://storage.googleapis.com",
                s3_access_key_id=os.getenv("GCS_HMAC_ACCESS_KEY_ID"),
                s3_secret_access_key=os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
            )
        else:
            litellm.cache = litellm.Cache(type="disk", disk_cache_dir=str(project_root / "litellm_cache"))

    for model_row in candidates:
        model_name = model_row["model"]
        provider = model_row["provider"]
        api_key_name = model_row["api_key"]
        
        # Key Management
        api_key = ""
        if api_key_name and api_key_name not in ["", "EXISTING_KEY", "VERTEX_CREDENTIALS"]:
            api_key = _get_api_key_interactively(api_key_name, model_row)
            if not api_key:
                continue

        # Prepare Params
        call_params = {
            "model": model_name,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
            "api_key": api_key if api_key else None
        }

        # Vertex AI Special Handling
        if provider == "Google" or "vertex_ai" in model_name:
            creds_path = os.getenv("VERTEX_CREDENTIALS")
            if creds_path and Path(creds_path).exists():
                with open(creds_path, "r") as f:
                    call_params["vertex_credentials"] = f.read()
            call_params["vertex_project"] = os.getenv("VERTEX_PROJECT")
            call_params["vertex_location"] = model_row.get("location") or os.getenv("VERTEX_LOCATION")

        # Reasoning / Thinking
        reasoning_params = _prepare_reasoning_params(model_row, time)
        call_params.update(reasoning_params)
        
        # Anthropic thinking requirement
        if "thinking" in reasoning_params and "anthropic" in model_name:
            call_params["temperature"] = 1.0

        # Build Messages
        if messages:
            final_messages = messages
        else:
            # Simple format if input_json is dict, batch if list
            # For this simplified script, we assume a single turn
            content = prompt.format(**input_json) if input_json and isinstance(input_json, dict) else prompt
            final_messages = [{"role": "user", "content": content}]

        # Structured Output Setup
        if output_pydantic or output_schema:
            schema = output_schema or output_pydantic.model_json_schema()
            _ensure_all_properties_required(schema)
            _add_additional_properties_false(schema)
            
            if model_row.get("structured_output") == True:
                call_params["response_format"] = {
                    "type": "json_schema",
                    "json_schema": {"name": "pdd_output", "schema": schema, "strict": True}
                }
            
            # Provider overrides
            if "lm_studio" in provider.lower():
                call_params["extra_body"] = {"response_format": call_params.get("response_format")}
            elif "groq" in provider.lower():
                call_params["response_format"] = {"type": "json_object"}
                final_messages.insert(0, {"role": "system", "content": f"Output JSON matching: {json.dumps(schema)}"})

        # Invoke
        try:
            if "gpt-5" in model_name:
                # Use litellm.responses for OpenAI gpt-5/Reasoning models per reqs
                response = litellm.responses(**call_params, messages=final_messages)
            elif use_batch_mode or isinstance(input_json, list):
                response = litellm.batch_completion(**call_params, messages=final_messages)
            else:
                response = litellm.completion(**call_params, messages=final_messages)

            # Process Response
            raw_content = response.choices[0].message.content or ""
            thinking = getattr(response.choices[0].message, "reasoning_content", None)
            
            # Post-processing JSON
            result = raw_content
            if output_pydantic or output_schema:
                parsed = _parse_llm_json(raw_content)
                if output_pydantic:
                    # Repair Python syntax in code fields if needed
                    if isinstance(parsed, dict):
                        for k, v in parsed.items():
                            if isinstance(v, str) and (language == "python" or language is None):
                                parsed[k] = _repair_python_syntax(_smart_unescape_code(v))
                    result = output_pydantic.model_validate(parsed)
                else:
                    result = parsed

            # Cost calculation
            cost = litellm.completion_cost(response)
            if cost == 0:
                # Fallback to CSV rates
                rates = _MODEL_RATE_MAP.get(model_name, {"input": 0, "output": 0})
                usage = getattr(response, "usage", {})
                cost = (usage.get("prompt_tokens", 0) * rates["input"] + 
                        usage.get("completion_tokens", 0) * rates["output"]) / 1_000_000

            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking
            }

        except Exception as e:
            logger.error(f"Error invoking {model_name}: {e}")
            if _is_wsl() and "401" in str(e):
                CONSOLE.print("[bold red]WSL Auth Warning:[/bold red] Check for carriage returns in your API keys.")
            # Continue to next candidate
            continue

    raise RuntimeError("All LLM model candidates failed.")

if __name__ == "__main__":
    # Example usage
    try:
        res = llm_invoke(prompt="Hello, who are you?", input_json={})
        CONSOLE.print(res)
    except Exception as e:
        CONSOLE.print(f"Final Error: {e}")