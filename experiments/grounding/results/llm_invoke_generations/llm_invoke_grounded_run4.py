from __future__ import annotations

import os

import re

import io

import json

import logging

import platform

import warnings

import time as time_module

import importlib.resources

from pathlib import Path

from typing import Any, Dict, List, Optional, Type, Union, Tuple



import pandas as pd

import litellm

import requests

from dotenv import load_dotenv

from pydantic import BaseModel, ValidationError

from rich.console import Console

from litellm.caching.caching import Cache



from .path_resolution import get_default_resolver



# --- Constants ---

LLM_CALL_TIMEOUT = 120

DEFAULT_LOG_LEVEL = os.getenv("PDD_LOG_LEVEL", "INFO")

PRODUCTION_MODE = os.getenv("PDD_ENVIRONMENT") == "production"

CONSOLE = Console()



# --- Logging Configuration ---

logger = logging.getLogger("pdd.llm_invoke")

litellm_logger = logging.getLogger("litellm")



if PRODUCTION_MODE:

    logger.setLevel(logging.WARNING)

    litellm_logger.setLevel(logging.WARNING)

else:

    logger.setLevel(getattr(logging, DEFAULT_LOG_LEVEL, logging.INFO))

    litellm_logger.setLevel(logging.WARNING)



litellm.set_verbose = False

litellm.suppress_debug_info = True

litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() in ("true", "1", "yes")



def setup_file_logging(log_file_path: str | None = None) -> None:

    if not log_file_path:

        return

    from logging.handlers import RotatingFileHandler

    handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)

    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')

    handler.setFormatter(formatter)

    logger.addHandler(handler)

    litellm_logger.addHandler(handler)



def set_verbose_logging(enabled: bool = False) -> None:

    level = logging.DEBUG if (enabled or os.getenv("PDD_VERBOSE_LOGGING") == "1") else logging.INFO

    logger.setLevel(level)

    if level == logging.DEBUG:

        litellm.set_verbose = True

        litellm.suppress_debug_info = False



# --- Path Resolution & Initialization ---

resolver = get_default_resolver()

PROJECT_ROOT = resolver.resolve_project_root()



def _resolve_csv_path() -> Path | None:

    candidates = [

        Path.home() / ".pdd" / "llm_model.csv",

        PROJECT_ROOT / ".pdd" / "llm_model.csv",

        Path.cwd() / ".pdd" / "llm_model.csv"

    ]

    for c in candidates:

        if c.is_file():

            return c

    return None



LLM_MODEL_CSV_PATH = _resolve_csv_path()

load_dotenv(PROJECT_ROOT / ".env")

DEFAULT_BASE_MODEL = os.getenv("PDD_MODEL_DEFAULT")



# --- Custom Exceptions ---

class SchemaValidationError(Exception):

    def __init__(self, message: str, raw_response: Any = None):

        super().__init__(message)

        self.raw_response = raw_response



class CloudFallbackError(Exception): pass

class CloudInvocationError(Exception): pass

class InsufficientCreditsError(Exception): pass



# --- Global State for Cost Tracking ---

_LAST_CALLBACK_DATA: Dict[str, Any] = {"cost": 0.0, "input_tokens": 0, "output_tokens": 0}

_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}



def _litellm_success_callback(kwargs, completion_response, start_time, end_time):

    global _LAST_CALLBACK_DATA

    try:

        cost = litellm.completion_cost(completion_response=completion_response) or 0.0

    except:

        model = kwargs.get("model", "")

        usage = completion_response.usage

        rates = _MODEL_RATE_MAP.get(model, (0.0, 0.0))

        cost = (usage.prompt_tokens * rates[0] + usage.completion_tokens * rates[1]) / 1_000_000

    

    _LAST_CALLBACK_DATA = {

        "cost": cost,

        "input_tokens": completion_response.usage.prompt_tokens,

        "output_tokens": completion_response.usage.completion_tokens,

        "finish_reason": completion_response.choices[0].finish_reason

    }



litellm.success_callback = [_litellm_success_callback]



# --- Structured Output Helpers ---

def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:

    if not isinstance(schema, dict): return

    if schema.get("type") == "object" and "properties" in schema:

        schema["required"] = list(schema["properties"].keys())

        for sub in schema["properties"].values():

            _ensure_all_properties_required(sub)

    if "items" in schema: _ensure_all_properties_required(schema["items"])

    for k in ("anyOf", "oneOf", "allOf"):

        if k in schema:

            for sub in schema[k]: _ensure_all_properties_required(sub)

    if "$defs" in schema:

        for sub in schema["$defs"].values(): _ensure_all_properties_required(sub)



def _add_additional_properties_false(schema: Dict[str, Any]) -> None:

    if not isinstance(schema, dict): return

    if schema.get("type") == "object":

        schema["additionalProperties"] = False

        if "properties" in schema:

            for sub in schema["properties"].values(): _add_additional_properties_false(sub)

    if "items" in schema: _add_additional_properties_false(schema["items"])

    for k in ("anyOf", "oneOf", "allOf", "$defs"):

        if k in schema:

            target = schema[k]

            iterable = target.values() if isinstance(target, dict) else target

            for sub in iterable: _add_additional_properties_false(sub)



# --- Python Code Repair Helpers ---

def _repair_python_syntax(code: str) -> str:

    import ast

    code = code.strip()

    try:

        ast.parse(code)

        return code

    except SyntaxError:

        for q in ('"', "'"):

            if code.endswith(q):

                try:

                    ast.parse(code[:-1])

                    return code[:-1]

                except:

                    continue

    return code



def _smart_unescape_code(code: str) -> str:

    if r"\n" not in code: return code

    # Simple balanced quote detection to avoid unescaping \n inside string literals

    parts = re.split(r'("""|\'\'\'|"|\')', code)

    new_code = []

    in_str = False

    quote_char = None

    for p in parts:

        if p in ('"', "'", '"""', "'''"):

            if not in_str:

                in_str, quote_char = True, p

            elif p == quote_char:

                in_str, quote_char = False, None

            new_code.append(p)

        else:

            new_code.append(p if in_str else p.replace(r"\n", "\n"))

    return "".join(new_code)



def _is_prose_field(name: str) -> bool:

    return name.lower() in ("reasoning", "explanation", "analysis", "thought", "summary")



# --- Core Functionality ---

def _load_model_data() -> pd.DataFrame:

    if LLM_MODEL_CSV_PATH:

        df = pd.read_csv(LLM_MODEL_CSV_PATH)

    else:

        csv_text = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()

        df = pd.read_csv(io.StringIO(csv_text))

    

    for col in ("input", "output", "coding_arena_elo", "max_reasoning_tokens"):

        df[col] = pd.to_numeric(df[col], errors='coerce').fillna(0)

    df["structured_output"] = df["structured_output"].astype(str).str.lower() == "true"

    return df



def _ensure_api_key(model_info: Dict[str, Any]) -> str | None:

    key_name = model_info["api_key"]

    if not key_name or key_name == "EXISTING_KEY": return "lm-studio" if "lm_studio" in str(model_info['model']) else "dummy"

    

    val = os.getenv(key_name)

    if val: return val.strip()

    

    if os.getenv("PDD_FORCE"): return None

    

    new_key = input(f"Enter API key for {key_name}: ").strip()

    if not new_key: return None

    

    os.environ[key_name] = new_key

    _save_key_to_env(key_name, new_key)

    logger.warning(f"Key saved to {PROJECT_ROOT}/.env")

    return new_key



def _save_key_to_env(name: str, val: str):

    env_file = PROJECT_ROOT / ".env"

    lines = env_file.read_text().splitlines() if env_file.exists() else []

    new_lines = [l for p in [f"{name}=", f"# {name}="] for l in lines if not l.strip().startswith(p)]

    new_lines.append(f'{name}="{val}"')

    env_file.write_text("\n".join(new_lines) + "\n")



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

    

    if use_cloud is None:

        use_cloud = not os.getenv("PDD_FORCE_LOCAL")

    

    if use_cloud:

        try:

            # Placeholder for cloud logic implementation

            return _llm_invoke_cloud(prompt, input_json, strength, temperature, verbose, output_pydantic, output_schema, time, use_batch_mode, messages, language)

        except CloudFallbackError:

            CONSOLE.print("[yellow]Cloud failed, falling back to local...[/yellow]")



    df = _load_model_data()

    global _MODEL_RATE_MAP

    _MODEL_RATE_MAP = {r['model']: (r['input'], r['output']) for _, r in df.iterrows()}

    

    # Model Selection logic

    base_name = DEFAULT_BASE_MODEL or df.iloc[0]['model']

    base_row = df[df['model'] == base_name].iloc[0] if base_name in df['model'].values else df.iloc[0]

    

    df['avg_cost'] = (df['input'] + df['output']) / 2

    if strength < 0.5:

        candidates = df[df['avg_cost'] <= base_row['avg_cost']].sort_values('avg_cost', ascending=False)

    elif strength > 0.5:

        candidates = df[df['coding_arena_elo'] >= base_row['coding_arena_elo']].sort_values('coding_arena_elo')

    else:

        candidates = pd.DataFrame([base_row])



    last_err = None

    for _, m_info in candidates.iterrows():

        key = _ensure_api_key(m_info.to_dict())

        if not key: continue

        

        try:

            call_params = _prep_call(m_info, prompt, input_json, messages, temperature, time, output_pydantic, output_schema, use_batch_mode)

            

            if "gpt-5" in m_info['model'].lower():

                resp = litellm.responses(**call_params)

                content = resp.output[0].content[0].text

            else:

                func = litellm.batch_completion if use_batch_mode else litellm.completion

                resp = func(**call_params)

                content = resp.choices[0].message.content if not use_batch_mode else [r.choices[0].message.content for r in resp]



            # Post-processing

            result = _process_content(content, output_pydantic, output_schema, language)

            

            thinking = ""

            if not use_batch_mode:

                thinking = getattr(resp.choices[0].message, "reasoning_content", "") or resp._hidden_params.get("thinking", "")



            return {

                "result": result,

                "cost": _LAST_CALLBACK_DATA["cost"],

                "model_name": m_info['model'],

                "thinking_output": thinking

            }

        except Exception as e:

            last_err = e

            continue

            

    raise RuntimeError(f"All models failed. Last error: {last_err}")



def _prep_call(m_info, prompt, input_json, messages, temp, time_val, out_p, out_s, batch):

    model = m_info['model']

    params = {"model": model, "temperature": temp, "messages": messages or []}

    

    if not messages:

        if batch:

            params["messages"] = [[{"role": "user", "content": prompt.format(**ij)}] for ij in input_json]

        else:

            params["messages"] = [{"role": "user", "content": prompt.format(**input_json)}]



    # Reasoning

    r_type = m_info['reasoning_type']

    if r_type == 'budget':

        params["thinking"] = {"type": "enabled", "budget_tokens": int(time_val * m_info['max_reasoning_tokens'])}

        params["temperature"] = 1.0

    elif r_type == 'effort':

        params["reasoning_effort"] = "high" if time_val > 0.7 else "medium" if time_val > 0.3 else "low"



    # Structured Output

    if (out_p or out_s) and m_info['structured_output']:

        schema = out_p.model_json_schema() if out_p else out_s

        _ensure_all_properties_required(schema)

        _add_additional_properties_false(schema)

        params["response_format"] = {

            "type": "json_schema",

            "json_schema": {"name": out_p.__name__ if out_p else "output", "schema": schema, "strict": True}

        }

    

    return params



def _process_content(content, out_p, out_s, lang):

    if not out_p and not out_s: return content

    

    # Batch handling

    if isinstance(content, list):

        return [_process_content(c, out_p, out_s, lang) for c in content]



    # JSON extraction

    json_str = content

    match = re.search(r"```json\s*(\{.*?\})\s*```", content, re.DOTALL)

    if match: json_str = match.group(1)

    else:

        # Balanced brace extraction

        braces = 0

        start = 0

        for i, char in enumerate(content):

            if char == '{':

                if braces == 0: start = i

                braces += 1

            elif char == '}':

                braces -= 1

                if braces == 0:

                    json_str = content[start:i+1]

                    break



    data = json.loads(json_str)

    

    # Repair code fields

    for k, v in data.items():

        if isinstance(v, str) and not _is_prose_field(k):

            data[k] = _repair_python_syntax(_smart_unescape_code(v))

            

    return out_p.model_validate(data) if out_p else data



def _llm_invoke_cloud(*args, **kwargs):

    # Implementation follows the % Cloud Execution requirement

    raise CloudFallbackError("Cloud not implemented in this stub")