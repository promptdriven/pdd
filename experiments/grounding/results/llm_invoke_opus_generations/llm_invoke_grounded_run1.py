from __future__ import annotations

import json
import logging
import os
import re
import sys
import time as _time
from dataclasses import dataclass
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Type, Union

import pandas as pd
import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError
from rich.console import Console

import litellm

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .path_resolution import get_default_resolver

console = Console()

LLM_CALL_TIMEOUT = 120

_LOGGER = logging.getLogger("pdd.llm_invoke")
_LITELLM_LOGGER = logging.getLogger("litellm")
_LAST_CALLBACK_DATA: Dict[str, Any] = {}
_MODEL_RATE_MAP: Dict[str, Tuple[float, float]] = {}


class SchemaValidationError(RuntimeError):
    pass


class CloudFallbackError(RuntimeError):
    pass


class CloudInvocationError(RuntimeError):
    pass


class InsufficientCreditsError(RuntimeError):
    pass


def _get_log_level(default: str) -> int:
    value = os.getenv("PDD_LOG_LEVEL", default).upper()
    if os.getenv("PDD_VERBOSE_LOGGING") == "1":
        value = "DEBUG"
    if os.getenv("PDD_ENVIRONMENT", "production").lower() == "production":
        if value == "DEBUG":
            value = "WARNING"
    return getattr(logging, value, logging.INFO)


def setup_file_logging(log_path: Path) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(log_path, maxBytes=10 * 1024 * 1024, backupCount=5)
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )
    handler.setFormatter(formatter)
    _LOGGER.addHandler(handler)


def set_verbose_logging(enabled: bool) -> None:
    if enabled:
        _LOGGER.setLevel(logging.DEBUG)
        _LITELLM_LOGGER.setLevel(logging.DEBUG)


def _setup_logging() -> None:
    level = _get_log_level("INFO")
    logging.basicConfig(level=level)
    _LOGGER.setLevel(level)
    litellm_level = os.getenv("LITELLM_LOG_LEVEL", "WARNING").upper()
    _LITELLM_LOGGER.setLevel(getattr(logging, litellm_level, logging.WARNING))


def _is_wsl() -> bool:
    if os.getenv("WSL_DISTRO_NAME"):
        return True
    try:
        return "microsoft" in Path("/proc/version").read_text().lower()
    except Exception:
        return False


def _sanitize_api_key(value: str) -> str:
    return re.sub(r"[\s\r\n\t]+", "", value).strip().strip('"').strip("'")


def _update_env_file(env_path: Path, key: str, value: str) -> None:
    lines: List[str] = []
    if env_path.exists():
        lines = env_path.read_text().splitlines()
    new_lines: List[str] = []
    for line in lines:
        if line.lstrip().startswith(f"{key}="):
            continue
        if line.lstrip().startswith(f"#{key}="):
            continue
        new_lines.append(line)
    new_lines.append(f"{key}={value}")
    env_path.write_text("\n".join(new_lines) + "\n")


def _ensure_api_key(key_name: str, env_path: Path) -> Tuple[Optional[str], bool]:
    existing = os.getenv(key_name)
    if existing:
        return existing, False
    if os.getenv("PDD_FORCE"):
        return None, False
    console.print(
        f"[bold yellow]API key '{key_name}' is required for this model.[/bold yellow]"
    )
    key = input(f"Enter {key_name}: ").strip()
    key = _sanitize_api_key(key)
    if not key:
        return None, False
    os.environ[key_name] = key
    _update_env_file(env_path, key_name, key)
    console.print(
        "[bold red]Warning:[/bold red] API key saved to .env file."
    )
    return key, True


def _resolve_project_root() -> Path:
    resolver = get_default_resolver()
    return resolver.resolve_project_root(
        profile="pdd_path_then_marker_then_cwd"
    )


def _resolve_model_csv(project_root: Path) -> Path:
    home_csv = Path.home() / ".pdd" / "llm_model.csv"
    if home_csv.exists():
        return home_csv
    pdd_path = os.getenv("PDD_PATH")
    if pdd_path:
        pdd_candidate = Path(pdd_path) / ".pdd" / "llm_model.csv"
        if pdd_candidate.exists():
            return pdd_candidate
    cwd_candidate = Path.cwd() / ".pdd" / "llm_model.csv"
    if cwd_candidate.exists():
        return cwd_candidate
    resolver = get_default_resolver()
    return resolver.resolve_data_file("llm_model.csv")


def _load_model_df(csv_path: Path) -> pd.DataFrame:
    df = pd.read_csv(csv_path)
    df.fillna("", inplace=True)
    for _, row in df.iterrows():
        try:
            _MODEL_RATE_MAP[str(row["model"])] = (
                float(row.get("input_cost", 0) or 0.0),
                float(row.get("output_cost", 0) or 0.0),
            )
        except Exception:
            continue
    return df


def _pydantic_to_json_schema(pydantic_class: Type[BaseModel]) -> Dict[str, Any]:
    schema = pydantic_class.model_json_schema()
    schema["__pydantic_class_name__"] = pydantic_class.__name__
    _ensure_all_properties_required(schema)
    _add_additional_properties_false(schema)
    return schema


def _validate_with_pydantic(
    result: Union[Dict[str, Any], str], pydantic_class: Type[BaseModel]
) -> Any:
    if isinstance(result, str):
        data = json.loads(result)
    else:
        data = result
    return pydantic_class.model_validate(data)


def _ensure_all_properties_required(schema: Dict[str, Any]) -> None:
    if "properties" in schema:
        props = schema["properties"]
        required = set(schema.get("required", []))
        required.update(props.keys())
        schema["required"] = list(required)
        for _, sub in props.items():
            if isinstance(sub, dict):
                _ensure_all_properties_required(sub)
    for key in ("items", "anyOf", "oneOf", "allOf"):
        if key in schema:
            subs = schema[key]
            if isinstance(subs, list):
                for sub in subs:
                    if isinstance(sub, dict):
                        _ensure_all_properties_required(sub)
            elif isinstance(subs, dict):
                _ensure_all_properties_required(subs)
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            if isinstance(sub, dict):
                _ensure_all_properties_required(sub)


def _add_additional_properties_false(schema: Dict[str, Any]) -> None:
    if schema.get("type") == "object":
        schema.setdefault("additionalProperties", False)
    if "properties" in schema:
        for sub in schema["properties"].values():
            if isinstance(sub, dict):
                _add_additional_properties_false(sub)
    for key in ("items", "anyOf", "oneOf", "allOf"):
        if key in schema:
            subs = schema[key]
            if isinstance(subs, list):
                for sub in subs:
                    if isinstance(sub, dict):
                        _add_additional_properties_false(sub)
            elif isinstance(subs, dict):
                _add_additional_properties_false(subs)
    if "$defs" in schema:
        for sub in schema["$defs"].values():
            if isinstance(sub, dict):
                _add_additional_properties_false(sub)


def _extract_json(text: str) -> str:
    fenced = re.search(r"```json(.*?)```", text, re.DOTALL | re.IGNORECASE)
    if fenced:
        return fenced.group(1).strip()
    match = re.search(r"\{.*\}", text, re.DOTALL)
    if match:
        return match.group(0)
    return text.strip()


def _parse_json_from_text(text: str) -> Any:
    candidate = _extract_json(text)
    try:
        return json.loads(candidate)
    except Exception:
        # Attempt to fix truncated JSON
        for closer in ("}", "}}", "]", "}]"):
            try:
                return json.loads(candidate + closer)
            except Exception:
                continue
    raise ValueError("Unable to parse JSON from LLM response.")


def _build_reasoning_params(
    reasoning_type: str, max_reasoning_tokens: Any, time_budget: float
) -> Dict[str, Any]:
    params: Dict[str, Any] = {}
    if reasoning_type == "budget":
        try:
            max_tokens = int(max_reasoning_tokens or 0)
        except Exception:
            max_tokens = 0
        budget = int(time_budget * max_tokens)
        if budget > 0:
            params["thinking"] = {"type": "enabled", "budget_tokens": budget}
    elif reasoning_type == "effort":
        if time_budget <= 0.33:
            effort = "low"
        elif time_budget <= 0.66:
            effort = "medium"
        else:
            effort = "high"
        params["reasoning_effort"] = effort
    return params


def _litellm_success_callback(
    response: Any, request_kwargs: Dict[str, Any], start_time: float, end_time: float
) -> None:
    global _LAST_CALLBACK_DATA
    try:
        usage = getattr(response, "usage", None)
        _LAST_CALLBACK_DATA = {
            "usage": usage,
            "model": request_kwargs.get("model"),
            "end_time": end_time,
            "start_time": start_time,
        }
    except Exception:
        _LAST_CALLBACK_DATA = {}


def _configure_cache(project_root: Path) -> None:
    if os.getenv("LITELLM_CACHE_DISABLE") == "1":
        litellm.cache = None
        return
    try:
        from litellm.caching import Cache

        if (
            os.getenv("GCS_HMAC_ACCESS_KEY_ID")
            and os.getenv("GCS_HMAC_SECRET_ACCESS_KEY")
            and os.getenv("GCS_BUCKET_NAME")
        ):
            litellm.cache = Cache(
                type="s3",
                s3_bucket_name=os.getenv("GCS_BUCKET_NAME"),
                s3_region_name="auto",
                s3_access_key_id=os.getenv("GCS_HMAC_ACCESS_KEY_ID"),
                s3_secret_access_key=os.getenv("GCS_HMAC_SECRET_ACCESS_KEY"),
            )
        else:
            litellm.cache = Cache(type="disk", disk_cache_dir=project_root)
    except Exception:
        litellm.cache = None


def _get_candidate_models(
    df: pd.DataFrame, strength: float
) -> List[Dict[str, Any]]:
    rows = df.to_dict(orient="records")
    if not rows:
        return []
    base_model_name = os.getenv("PDD_MODEL_DEFAULT")
    base_row = None
    if base_model_name:
        for r in rows:
            if r.get("model") == base_model_name:
                base_row = r
                break
    if base_row is None:
        base_row = rows[0]

    def cost_key(r: Dict[str, Any]) -> float:
        try:
            return float(r.get("input_cost", 0)) + float(r.get("output_cost", 0))
        except Exception:
            return 0.0

    def elo_key(r: Dict[str, Any]) -> float:
        try:
            return float(r.get("coding_arena_elo", 0))
        except Exception:
            return 0.0

    if strength < 0.5:
        sorted_rows = sorted(rows, key=cost_key)
        idx = sorted_rows.index(base_row) if base_row in sorted_rows else 0
        target_idx = int((1 - (strength / 0.5)) * idx)
        selected = sorted_rows[target_idx]
        remaining = [r for r in sorted_rows if r is not selected]
    elif strength > 0.5:
        sorted_rows = sorted(rows, key=elo_key)
        idx = sorted_rows.index(base_row) if base_row in sorted_rows else 0
        top_idx = len(sorted_rows) - 1
        frac = (strength - 0.5) / 0.5
        target_idx = int(idx + frac * (top_idx - idx))
        selected = sorted_rows[target_idx]
        remaining = [r for r in sorted_rows if r is not selected]
        remaining = list(reversed(remaining))
    else:
        selected = base_row
        remaining = sorted(rows, key=elo_key, reverse=True)
        remaining = [r for r in remaining if r is not selected]

    return [selected] + remaining


@dataclass
class CloudConfig:
    @staticmethod
    def is_cloud_enabled() -> bool:
        return os.getenv("PDD_CLOUD_ENABLED", "").lower() in (
            "1",
            "true",
            "yes",
        ) or bool(os.getenv("PDD_CLOUD_URL"))


def _llm_invoke_cloud(
    payload: Dict[str, Any],
) -> Dict[str, Any]:
    url = os.getenv(
        "PDD_CLOUD_URL",
        "https://us-central1-prompt-driven-development.cloudfunctions.net/llmInvoke",
    )
    token = os.getenv("PDD_CLOUD_JWT")
    if not token:
        raise CloudInvocationError("Missing cloud auth token (PDD_CLOUD_JWT).")
    headers = {"Authorization": f"Bearer {token}"}
    try:
        response = requests.post(
            url, json=payload, headers=headers, timeout=300
        )
    except requests.RequestException as e:
        raise CloudFallbackError(str(e)) from e
    if response.status_code == 402:
        raise InsufficientCreditsError("Insufficient credits.")
    if response.status_code in (401, 403):
        raise CloudFallbackError("Authentication error.")
    if response.status_code >= 500:
        raise CloudFallbackError("Server error.")
    if response.status_code >= 400:
        raise CloudInvocationError(response.text)
    return response.json()


def _prepare_messages(
    prompt: Optional[str],
    input_json: Optional[Union[Dict[str, Any], List[Dict[str, Any]]]],
    messages: Optional[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]]],
) -> Tuple[Union[List[Dict[str, Any]], List[List[Dict[str, Any]]]], bool]:
    if messages is not None:
        if isinstance(messages, list) and messages and isinstance(messages[0], list):
            return messages, True
        return messages, False
    if prompt is None or input_json is None:
        raise ValueError("prompt and input_json are required when messages not provided.")
    if isinstance(input_json, list):
        batch: List[List[Dict[str, Any]]] = []
        for item in input_json:
            batch.append([{"role": "user", "content": prompt.format(**item)}])
        return batch, True
    return [{"role": "user", "content": prompt.format(**input_json)}], False


def _extract_thinking_output(response: Any) -> Optional[str]:
    try:
        hidden = getattr(response, "_hidden_params", None)
        if hidden and isinstance(hidden, dict):
            if "thinking" in hidden:
                return hidden["thinking"]
    except Exception:
        pass
    try:
        return response.choices[0].message.reasoning_content
    except Exception:
        return None


def _calculate_cost(model_name: str, response: Any) -> float:
    try:
        return float(litellm.completion_cost(response))
    except Exception:
        rates = _MODEL_RATE_MAP.get(model_name)
        if not rates:
            return 0.0
        usage = getattr(response, "usage", None)
        if not usage:
            return 0.0
        input_cost, output_cost = rates
        prompt_tokens = getattr(usage, "prompt_tokens", 0) or 0
        completion_tokens = getattr(usage, "completion_tokens", 0) or 0
        return (prompt_tokens * input_cost + completion_tokens * output_cost) / 1_000_000


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
    _setup_logging()
    if verbose:
        set_verbose_logging(True)

    project_root = _resolve_project_root()
    load_dotenv(project_root / ".env")

    if output_pydantic and output_schema:
        raise ValueError("Specify output_pydantic OR output_schema, not both.")

    if use_cloud is None:
        if os.getenv("PDD_FORCE_LOCAL") != "1" and CloudConfig.is_cloud_enabled():
            use_cloud = True
        else:
            use_cloud = False

    if use_cloud:
        payload: Dict[str, Any] = {
            "prompt": prompt,
            "inputJson": input_json,
            "messages": messages,
            "strength": strength,
            "temperature": temperature,
            "time": time,
            "verbose": verbose,
            "outputSchema": _pydantic_to_json_schema(output_pydantic)
            if output_pydantic
            else output_schema,
            "useBatchMode": use_batch_mode,
            "language": language,
        }
        try:
            cloud_res = _llm_invoke_cloud(payload)
            result = cloud_res.get("result")
            if output_pydantic:
                result = _validate_with_pydantic(result, output_pydantic)
            return {
                "result": result,
                "cost": cloud_res.get("totalCost", 0),
                "model_name": cloud_res.get("modelName"),
                "thinking_output": cloud_res.get("thinkingOutput"),
            }
        except CloudFallbackError as e:
            console.print(f"[yellow]Cloud fallback:[/yellow] {e}")
            _LOGGER.warning("Cloud fallback: %s", e)
        except CloudInvocationError as e:
            console.print(f"[yellow]Cloud error:[/yellow] {e}")
            _LOGGER.warning("Cloud error: %s", e)
        except InsufficientCreditsError:
            raise

    csv_path = _resolve_model_csv(project_root)
    df = _load_model_df(csv_path)
    candidates = _get_candidate_models(df, strength)

    litellm.drop_params = os.getenv("LITELLM_DROP_PARAMS", "true").lower() != "false"
    litellm.success_callback = [_litellm_success_callback]

    _configure_cache(project_root)

    prepared_messages, is_batch = _prepare_messages(prompt, input_json, messages)
    if use_batch_mode:
        is_batch = True

    if output_pydantic:
        output_schema = _pydantic_to_json_schema(output_pydantic)
    if output_schema:
        _ensure_all_properties_required(output_schema)
        _add_additional_properties_false(output_schema)

    last_error: Optional[Exception] = None
    env_path = project_root / ".env"

    for model_row in candidates:
        model_name = str(model_row.get("model"))
        provider = str(model_row.get("provider", ""))
        api_key_env = str(model_row.get("api_key", "")).strip()
        base_url = str(model_row.get("base_url", "")).strip() or None
        structured_output = str(model_row.get("structured_output", "")).lower() in (
            "1",
            "true",
            "yes",
        )
        reasoning_type = str(model_row.get("reasoning_type", "none"))
        max_reasoning_tokens = model_row.get("max_reasoning_tokens", 0)

        key_value: Optional[str] = None
        new_key = False
        if api_key_env and api_key_env != "EXISTING_KEY":
            key_value, new_key = _ensure_api_key(api_key_env, env_path)
            if not key_value:
                continue

        params: Dict[str, Any] = {
            "model": model_name,
            "temperature": temperature,
            "num_retries": 2,
            "timeout": LLM_CALL_TIMEOUT,
        }

        if key_value:
            params["api_key"] = key_value
        if base_url:
            params["base_url"] = base_url

        if "lm-studio" in provider.lower() or "lmstudio" in model_name.lower():
            params["base_url"] = os.getenv(
                "LM_STUDIO_API_BASE", "http://localhost:1234/v1"
            )
            params["api_key"] = "lm-studio"

        if "vertex" in provider.lower() or model_name.lower().startswith("vertex"):
            params["vertex_project"] = os.getenv("VERTEX_PROJECT")
            params["vertex_location"] = (
                str(model_row.get("location", "")).strip()
                or os.getenv("VERTEX_LOCATION")
            )
            creds_path = os.getenv("VERTEX_CREDENTIALS")
            if creds_path and Path(creds_path).exists():
                params["vertex_credentials"] = Path(creds_path).read_text()

        params.update(_build_reasoning_params(reasoning_type, max_reasoning_tokens, time))

        try:
            if output_schema and structured_output:
                response_format = {
                    "type": "json_schema",
                    "json_schema": {
                        "name": "response",
                        "schema": output_schema,
                        "strict": True,
                    },
                }
                params["response_format"] = response_format
            elif output_schema:
                # fallback: schema in system prompt
                params.setdefault("messages", [])
                sys_msg = {
                    "role": "system",
                    "content": "Return valid JSON matching this schema:\n"
                    + json.dumps(output_schema),
                }
                if is_batch:
                    for msg_list in prepared_messages:
                        msg_list.insert(0, sys_msg)
                else:
                    prepared_messages.insert(0, sys_msg)

            if model_name.startswith("gpt-5"):
                # Responses API
                params.pop("temperature", None)
                response = litellm.responses(
                    input=prepared_messages if not is_batch else prepared_messages,
                    **params,
                )
            else:
                if is_batch:
                    response = litellm.batch_completion(
                        messages=prepared_messages, **params
                    )
                else:
                    response = litellm.completion(messages=prepared_messages, **params)

            thinking = _extract_thinking_output(response)

            def _extract_content(resp: Any) -> Any:
                try:
                    return resp.choices[0].message.content
                except Exception:
                    return str(resp)

            if is_batch:
                contents = [_extract_content(r) for r in response]
            else:
                contents = _extract_content(response)

            result: Any = contents
            if output_schema:
                if is_batch:
                    result = [_parse_json_from_text(c or "") for c in contents]  # type: ignore
                else:
                    result = _parse_json_from_text(contents or "")
            if output_pydantic:
                if is_batch:
                    result = [_validate_with_pydantic(r, output_pydantic) for r in result]  # type: ignore
                else:
                    result = _validate_with_pydantic(result, output_pydantic)
            cost = _calculate_cost(model_name, response)

            return {
                "result": result,
                "cost": cost,
                "model_name": model_name,
                "thinking_output": thinking,
            }
        except ValidationError as e:
            last_error = e
            _LOGGER.warning("Schema validation failed: %s", e)
            continue
        except Exception as e:
            msg = str(e).lower()
            if ("unauthorized" in msg or "401" in msg) and new_key:
                key_value, _ = _ensure_api_key(api_key_env, env_path)
                if key_value:
                    continue
            if _is_wsl() and ("api key" in msg or "unauthorized" in msg):
                console.print(
                    "[yellow]WSL detected. Check for carriage returns in API keys.[/yellow]"
                )
            last_error = e
            _LOGGER.warning("Model %s failed: %s", model_name, e)
            continue

    raise RuntimeError(f"All models failed. Last error: {last_error}")


if __name__ == "__main__":
    # simple test
    try:
        res = llm_invoke(
            prompt="Say hello to {name}",
            input_json={"name": "world"},
            strength=0.5,
        )
        console.print(res)
    except Exception as exc:
        console.print(f"[red]{exc}[/red]")