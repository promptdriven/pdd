"""
llm_client - A self-contained LLM client simulator.

Handles model selection, retry logic, cost tracking, structured output parsing,
and provider abstraction. No external dependencies beyond the Python stdlib.
"""

import copy
import csv
import hashlib
import io
import json
import logging
import math
import random
import re
import time
import threading
from collections import OrderedDict
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, List, Optional, Tuple, Union


logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class Provider(Enum):
    OPENAI = "openai"
    ANTHROPIC = "anthropic"
    GOOGLE = "google"


class ReasoningType(Enum):
    NONE = "none"
    CHAIN_OF_THOUGHT = "chain_of_thought"
    EXTENDED_THINKING = "extended_thinking"


class ErrorCategory(Enum):
    TRANSIENT = auto()
    RATE_LIMIT = auto()
    TIMEOUT = auto()
    SERVER_ERROR = auto()
    AUTH_ERROR = auto()
    CONTEXT_OVERFLOW = auto()
    INVALID_REQUEST = auto()
    CONTENT_FILTER = auto()
    MODEL_OVERLOADED = auto()


class CacheStrategy(Enum):
    LRU = "lru"
    NONE = "none"


class TokenEstimationMethod(Enum):
    WHITESPACE = "whitespace"
    CHARACTER = "character"
    HYBRID = "hybrid"


class InvocationState(Enum):
    PENDING = auto()
    SELECTING_MODEL = auto()
    VALIDATING_CONTEXT = auto()
    CHECKING_CACHE = auto()
    FORMATTING_REQUEST = auto()
    SENDING = auto()
    RETRYING = auto()
    PARSING_RESPONSE = auto()
    VALIDATING_OUTPUT = auto()
    COMPLETE = auto()
    FAILED = auto()


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------

class LLMClientError(Exception):
    pass


class TransientError(LLMClientError):
    def __init__(self, message: str, category: ErrorCategory = ErrorCategory.TRANSIENT):
        super().__init__(message)
        self.category = category


class RateLimitError(TransientError):
    def __init__(self, message: str = "Rate limit exceeded", retry_after: Optional[float] = None):
        super().__init__(message, ErrorCategory.RATE_LIMIT)
        self.retry_after = retry_after


class TimeoutError(TransientError):
    def __init__(self, message: str = "Request timed out"):
        super().__init__(message, ErrorCategory.TIMEOUT)


class ServerError(TransientError):
    def __init__(self, message: str = "Internal server error", status_code: int = 500):
        super().__init__(message, ErrorCategory.SERVER_ERROR)
        self.status_code = status_code


class ModelOverloadedError(TransientError):
    def __init__(self, message: str = "Model is overloaded"):
        super().__init__(message, ErrorCategory.MODEL_OVERLOADED)


class AuthenticationError(LLMClientError):
    pass


class ContextOverflowError(LLMClientError):
    def __init__(self, prompt_tokens: int, context_limit: int):
        super().__init__(
            f"Prompt ({prompt_tokens} tokens) exceeds context limit ({context_limit} tokens)"
        )
        self.prompt_tokens = prompt_tokens
        self.context_limit = context_limit


class InvalidRequestError(LLMClientError):
    pass


class ContentFilterError(LLMClientError):
    pass


class SchemaValidationError(LLMClientError):
    def __init__(self, message: str, path: str = "", value: Any = None):
        super().__init__(message)
        self.path = path
        self.value = value


class JSONRepairError(LLMClientError):
    pass


# ---------------------------------------------------------------------------
# Model configuration
# ---------------------------------------------------------------------------

MODELS_CSV = """name,provider,input_cost_per_m,output_cost_per_m,elo,context_limit,supports_structured,reasoning_type
gpt-4o-mini,openai,0.15,0.60,1100,128000,true,none
gpt-4o,openai,2.50,10.00,1280,128000,true,none
gpt-4-turbo,openai,10.00,30.00,1250,128000,true,none
o1-mini,openai,3.00,12.00,1300,128000,false,chain_of_thought
o1,openai,15.00,60.00,1350,200000,false,chain_of_thought
o3-mini,openai,1.10,4.40,1320,200000,true,chain_of_thought
claude-3-haiku,anthropic,0.25,1.25,1150,200000,true,none
claude-3.5-sonnet,anthropic,3.00,15.00,1300,200000,true,none
claude-3-opus,anthropic,15.00,75.00,1320,200000,true,extended_thinking
claude-3.5-haiku,anthropic,1.00,5.00,1230,200000,true,none
claude-4-sonnet,anthropic,3.00,15.00,1380,200000,true,extended_thinking
gemini-1.5-flash,google,0.075,0.30,1050,1000000,true,none
gemini-1.5-pro,google,1.25,5.00,1220,2000000,true,none
gemini-2.0-flash,google,0.10,0.40,1180,1000000,true,none
gemini-2.5-pro,google,1.25,10.00,1360,1000000,true,chain_of_thought
"""


@dataclass(frozen=True)
class ModelConfig:
    name: str
    provider: Provider
    input_cost_per_million: float
    output_cost_per_million: float
    elo: int
    context_limit: int
    supports_structured_output: bool
    reasoning_type: ReasoningType

    @property
    def effective_cost(self) -> float:
        return (self.input_cost_per_million + self.output_cost_per_million) / 2.0

    @property
    def is_reasoning_model(self) -> bool:
        return self.reasoning_type != ReasoningType.NONE

    @property
    def cost_efficiency(self) -> float:
        if self.effective_cost == 0:
            return float('inf')
        return self.elo / self.effective_cost


def _parse_bool(val: str) -> bool:
    return val.strip().lower() in ("true", "1", "yes")


def _parse_reasoning_type(val: str) -> ReasoningType:
    val = val.strip().lower()
    mapping = {
        "none": ReasoningType.NONE,
        "chain_of_thought": ReasoningType.CHAIN_OF_THOUGHT,
        "extended_thinking": ReasoningType.EXTENDED_THINKING,
    }
    return mapping.get(val, ReasoningType.NONE)


def _parse_provider(val: str) -> Provider:
    val = val.strip().lower()
    mapping = {
        "openai": Provider.OPENAI,
        "anthropic": Provider.ANTHROPIC,
        "google": Provider.GOOGLE,
    }
    if val not in mapping:
        raise ValueError(f"Unknown provider: {val}")
    return mapping[val]


def load_models(csv_text: Optional[str] = None) -> List[ModelConfig]:
    if csv_text is None:
        csv_text = MODELS_CSV
    reader = csv.DictReader(io.StringIO(csv_text.strip()))
    models = []
    for row in reader:
        try:
            config = ModelConfig(
                name=row["name"].strip(),
                provider=_parse_provider(row["provider"]),
                input_cost_per_million=float(row["input_cost_per_m"]),
                output_cost_per_million=float(row["output_cost_per_m"]),
                elo=int(row["elo"]),
                context_limit=int(row["context_limit"]),
                supports_structured_output=_parse_bool(row["supports_structured"]),
                reasoning_type=_parse_reasoning_type(row["reasoning_type"]),
            )
            models.append(config)
        except (KeyError, ValueError) as exc:
            logger.warning("Skipping malformed model row %s: %s", row, exc)
    models.sort(key=lambda m: m.elo)
    return models


def _model_score(model: ModelConfig) -> float:
    return model.elo + model.effective_cost * 10


def select_model(
    models: List[ModelConfig],
    strength: float,
    require_structured: bool = False,
    require_reasoning: bool = False,
    preferred_provider: Optional[Provider] = None,
    min_context: int = 0,
) -> ModelConfig:
    if not models:
        raise InvalidRequestError("No models available")
    strength = max(0.0, min(1.0, strength))
    candidates = list(models)
    if require_structured:
        candidates = [m for m in candidates if m.supports_structured_output]
    if require_reasoning:
        candidates = [m for m in candidates if m.is_reasoning_model]
    if min_context > 0:
        candidates = [m for m in candidates if m.context_limit >= min_context]
    if preferred_provider is not None:
        provider_candidates = [m for m in candidates if m.provider == preferred_provider]
        if provider_candidates:
            candidates = provider_candidates
    if not candidates:
        candidates = list(models)
        logger.warning("Filters eliminated all models; falling back to full list")
    candidates.sort(key=_model_score)
    if len(candidates) == 1:
        return candidates[0]
    idx_float = strength * (len(candidates) - 1)
    idx_low = int(math.floor(idx_float))
    idx_high = min(idx_low + 1, len(candidates) - 1)
    frac = idx_float - idx_low
    score_low = _model_score(candidates[idx_low])
    score_high = _model_score(candidates[idx_high])
    target = score_low + frac * (score_high - score_low)
    best = None
    best_dist = float('inf')
    for m in candidates:
        dist = abs(_model_score(m) - target)
        if dist < best_dist:
            best_dist = dist
            best = m
    return best


def select_model_by_budget(
    models: List[ModelConfig],
    max_cost_per_million: float,
    prefer_capability: bool = True,
) -> ModelConfig:
    affordable = [
        m for m in models if m.effective_cost <= max_cost_per_million
    ]
    if not affordable:
        affordable = sorted(models, key=lambda m: m.effective_cost)
        return affordable[0]
    if prefer_capability:
        affordable.sort(key=lambda m: m.elo, reverse=True)
    else:
        affordable.sort(key=lambda m: m.effective_cost)
    return affordable[0]


# ---------------------------------------------------------------------------
# Token counting
# ---------------------------------------------------------------------------

class TokenCounter:
    _SPECIAL_TOKEN_PATTERNS = [
        (re.compile(r'https?://\S+'), 5),
        (re.compile(r'[\w.+-]+@[\w-]+\.[\w.-]+'), 3),
        (re.compile(r'\b\d{1,3}(?:,\d{3})*(?:\.\d+)?\b'), 1),
        (re.compile(r'```[\s\S]*?```'), None),
    ]

    def __init__(self, method: TokenEstimationMethod = TokenEstimationMethod.HYBRID):
        self.method = method
        self._cache: Dict[int, int] = {}

    def count(self, text: str) -> int:
        text_hash = hash(text)
        if text_hash in self._cache:
            return self._cache[text_hash]
        if self.method == TokenEstimationMethod.WHITESPACE:
            result = self._whitespace_count(text)
        elif self.method == TokenEstimationMethod.CHARACTER:
            result = self._character_count(text)
        else:
            result = self._hybrid_count(text)
        self._cache[text_hash] = result
        return result

    def _whitespace_count(self, text: str) -> int:
        words = text.split()
        count = 0
        for word in words:
            if len(word) <= 3:
                count += 1
            elif len(word) <= 8:
                count += 1
            else:
                count += max(1, len(word) // 4)
        return max(1, count)

    def _character_count(self, text: str) -> int:
        return max(1, len(text) // 4)

    def _hybrid_count(self, text: str) -> int:
        ws = self._whitespace_count(text)
        ch = self._character_count(text)
        special_bonus = 0
        for pattern, weight in self._SPECIAL_TOKEN_PATTERNS:
            matches = pattern.findall(text)
            if weight is not None:
                special_bonus += len(matches) * weight
            else:
                for match in matches:
                    special_bonus += len(match) // 4
        base = int(ws * 0.6 + ch * 0.4)
        return max(1, base + special_bonus)


_default_counter = TokenCounter()


def count_tokens(text: str) -> int:
    return _default_counter.count(text)


def estimate_output_tokens(prompt_tokens: int, model: ModelConfig) -> int:
    if model.is_reasoning_model:
        return min(prompt_tokens * 3, model.context_limit - prompt_tokens)
    return min(prompt_tokens, model.context_limit - prompt_tokens)


# ---------------------------------------------------------------------------
# Context window validation
# ---------------------------------------------------------------------------

class ContextWindowValidator:
    def __init__(self, safety_margin: float = 0.05):
        self.safety_margin = safety_margin

    def validate(self, prompt_tokens: int, model: ModelConfig) -> bool:
        effective_limit = int(model.context_limit * (1.0 - self.safety_margin))
        return prompt_tokens <= effective_limit

    def available_output_tokens(self, prompt_tokens: int, model: ModelConfig) -> int:
        effective_limit = int(model.context_limit * (1.0 - self.safety_margin))
        return max(0, effective_limit - prompt_tokens)

    def utilization(self, prompt_tokens: int, model: ModelConfig) -> float:
        if model.context_limit == 0:
            return 1.0
        return prompt_tokens / model.context_limit

    def warn_if_near_limit(self, prompt_tokens: int, model: ModelConfig, threshold: float = 0.8):
        util = self.utilization(prompt_tokens, model)
        if util > threshold:
            logger.warning(
                "Context utilization at %.1f%% for model %s (%d / %d tokens)",
                util * 100,
                model.name,
                prompt_tokens,
                model.context_limit,
            )
            return True
        return False


def validate_context_window(prompt_tokens: int, model: ModelConfig) -> bool:
    validator = ContextWindowValidator()
    return validator.validate(prompt_tokens, model)


# ---------------------------------------------------------------------------
# Prompt formatting
# ---------------------------------------------------------------------------

class TemplateEngine:
    _VAR_PATTERN = re.compile(r'\{\{(\w+)(?:\|([^}]*))?\}\}')
    _COND_PATTERN = re.compile(r'\{%\s*if\s+(\w+)\s*%\}(.*?)\{%\s*endif\s*%\}', re.DOTALL)
    _LOOP_PATTERN = re.compile(
        r'\{%\s*for\s+(\w+)\s+in\s+(\w+)\s*%\}(.*?)\{%\s*endfor\s*%\}', re.DOTALL
    )

    def __init__(self):
        self._filter_funcs: Dict[str, Callable] = {
            "upper": str.upper,
            "lower": str.lower,
            "strip": str.strip,
            "title": str.title,
            "json": lambda x: json.dumps(x) if not isinstance(x, str) else x,
        }

    def render(self, template: str, variables: Dict[str, Any]) -> str:
        result = template
        result = self._process_loops(result, variables)
        result = self._process_conditionals(result, variables)
        result = self._process_variables(result, variables)
        return result

    def _process_variables(self, template: str, variables: Dict[str, Any]) -> str:
        def replacer(match):
            var_name = match.group(1)
            filter_name = match.group(2)
            value = variables.get(var_name, match.group(0))
            if filter_name and filter_name in self._filter_funcs:
                value = self._filter_funcs[filter_name](str(value))
            return str(value)
        return self._VAR_PATTERN.sub(replacer, template)

    def _process_conditionals(self, template: str, variables: Dict[str, Any]) -> str:
        def replacer(match):
            var_name = match.group(1)
            body = match.group(2)
            value = variables.get(var_name)
            if value:
                return self._process_variables(body, variables)
            return ""
        return self._COND_PATTERN.sub(replacer, template)

    def _process_loops(self, template: str, variables: Dict[str, Any]) -> str:
        def replacer(match):
            item_name = match.group(1)
            list_name = match.group(2)
            body = match.group(3)
            items = variables.get(list_name, [])
            if not isinstance(items, (list, tuple)):
                return ""
            parts = []
            for item in items:
                local_vars = dict(variables)
                local_vars[item_name] = item
                rendered = self._process_variables(body, local_vars)
                parts.append(rendered)
            return "".join(parts)
        return self._LOOP_PATTERN.sub(replacer, template)


def format_prompt(template: str, variables: Dict[str, Any]) -> str:
    engine = TemplateEngine()
    return engine.render(template, variables)


# ---------------------------------------------------------------------------
# JSON extraction and repair
# ---------------------------------------------------------------------------

class JSONExtractor:
    _FENCED_PATTERN = re.compile(r'```(?:json)?\s*\n?([\s\S]*?)\n?```')
    _OBJECT_PATTERN = re.compile(r'\{[\s\S]*\}')
    _ARRAY_PATTERN = re.compile(r'\[[\s\S]*\]')

    def extract(self, text: str) -> Optional[str]:
        fenced = self._FENCED_PATTERN.findall(text)
        if fenced:
            for block in fenced:
                block = block.strip()
                if block and (block.startswith('{') or block.startswith('[')):
                    return block
        obj_match = self._OBJECT_PATTERN.search(text)
        if obj_match:
            return obj_match.group(0)
        arr_match = self._ARRAY_PATTERN.search(text)
        if arr_match:
            return arr_match.group(0)
        return None

    def extract_all(self, text: str) -> List[str]:
        results = []
        fenced = self._FENCED_PATTERN.findall(text)
        for block in fenced:
            block = block.strip()
            if block:
                results.append(block)
        if not results:
            for pattern in [self._OBJECT_PATTERN, self._ARRAY_PATTERN]:
                for match in pattern.finditer(text):
                    results.append(match.group(0))
        return results


class JSONRepairer:
    def repair(self, text: str) -> str:
        text = text.strip()
        if not text:
            return text
        text = self._fix_trailing_commas(text)
        text = self._fix_single_quotes(text)
        text = self._fix_unquoted_keys(text)
        text = self._close_unclosed_strings(text)
        text = self._close_unclosed_brackets(text)
        return text

    def _fix_trailing_commas(self, text: str) -> str:
        result = re.sub(r',\s*([}\]])', r'\1', text)
        return result

    def _fix_single_quotes(self, text: str) -> str:
        in_double = False
        chars = list(text)
        i = 0
        while i < len(chars):
            if chars[i] == '\\' and i + 1 < len(chars):
                i += 2
                continue
            if chars[i] == '"':
                in_double = not in_double
            elif chars[i] == "'" and not in_double:
                chars[i] = '"'
            i += 1
        return ''.join(chars)

    def _fix_unquoted_keys(self, text: str) -> str:
        pattern = re.compile(r'(?<=[\{,])\s*([a-zA-Z_]\w*)\s*:')
        return pattern.sub(r' "\1":', text)

    def _close_unclosed_strings(self, text: str) -> str:
        in_string = False
        escaped = False
        for ch in text:
            if escaped:
                escaped = False
                continue
            if ch == '\\':
                escaped = True
                continue
            if ch == '"':
                in_string = not in_string
        if in_string:
            text += '"'
        return text

    def _close_unclosed_brackets(self, text: str) -> str:
        stack = []
        in_string = False
        escaped = False
        for ch in text:
            if escaped:
                escaped = False
                continue
            if ch == '\\':
                escaped = True
                continue
            if ch == '"':
                in_string = not in_string
                continue
            if in_string:
                continue
            if ch == '{':
                stack.append('}')
            elif ch == '[':
                stack.append(']')
            elif ch in ('}', ']'):
                if stack and stack[-1] == ch:
                    stack.pop()
        while stack:
            text += stack.pop()
        return text


def extract_json(text: str) -> Optional[str]:
    extractor = JSONExtractor()
    return extractor.extract(text)


def repair_json(text: str) -> str:
    repairer = JSONRepairer()
    return repairer.repair(text)


def parse_json_safe(text: str) -> Tuple[Optional[Any], Optional[str]]:
    try:
        return json.loads(text), None
    except json.JSONDecodeError:
        pass
    extracted = extract_json(text)
    if extracted:
        try:
            return json.loads(extracted), None
        except json.JSONDecodeError:
            pass
        repaired = repair_json(extracted)
        try:
            return json.loads(repaired), None
        except json.JSONDecodeError as e:
            return None, f"JSON parse error after repair: {e}"
    return None, "No JSON found in text"


# ---------------------------------------------------------------------------
# Schema validation
# ---------------------------------------------------------------------------

class SchemaValidator:
    def __init__(self, schema: Dict[str, Any]):
        self.schema = schema
        self._errors: List[str] = []

    def validate(self, data: Any) -> Tuple[bool, List[str]]:
        self._errors = []
        self._validate_node(data, self.schema, "$")
        return len(self._errors) == 0, list(self._errors)

    def _validate_node(self, data: Any, schema: Dict[str, Any], path: str):
        schema_type = schema.get("type")
        if schema_type:
            self._check_type(data, schema_type, path)
        if schema_type == "object":
            self._validate_object(data, schema, path)
        elif schema_type == "array":
            self._validate_array(data, schema, path)
        elif schema_type == "string":
            self._validate_string(data, schema, path)
        elif schema_type == "number" or schema_type == "integer":
            self._validate_number(data, schema, path)
        if "enum" in schema:
            if data not in schema["enum"]:
                self._errors.append(f"{path}: value {data!r} not in enum {schema['enum']}")
        if "const" in schema:
            if data != schema["const"]:
                self._errors.append(f"{path}: expected {schema['const']!r}, got {data!r}")

    def _check_type(self, data: Any, expected: str, path: str):
        type_map = {
            "string": str,
            "number": (int, float),
            "integer": int,
            "boolean": bool,
            "array": list,
            "object": dict,
            "null": type(None),
        }
        expected_type = type_map.get(expected)
        if expected_type is None:
            return
        if expected == "integer" and isinstance(data, bool):
            self._errors.append(f"{path}: expected integer, got boolean")
            return
        if expected == "number" and isinstance(data, bool):
            self._errors.append(f"{path}: expected number, got boolean")
            return
        if not isinstance(data, expected_type):
            self._errors.append(f"{path}: expected {expected}, got {type(data).__name__}")

    def _validate_object(self, data: Any, schema: Dict, path: str):
        if not isinstance(data, dict):
            return
        properties = schema.get("properties", {})
        required = set(schema.get("required", []))
        for req_key in required:
            if req_key not in data:
                self._errors.append(f"{path}.{req_key}: required property missing")
        additional = schema.get("additionalProperties", True)
        for key, value in data.items():
            if key in properties:
                self._validate_node(value, properties[key], f"{path}.{key}")
            elif additional is False:
                self._errors.append(f"{path}.{key}: additional property not allowed")
            elif isinstance(additional, dict):
                self._validate_node(value, additional, f"{path}.{key}")
        min_props = schema.get("minProperties")
        max_props = schema.get("maxProperties")
        if min_props is not None and len(data) < min_props:
            self._errors.append(f"{path}: expected at least {min_props} properties, got {len(data)}")
        if max_props is not None and len(data) > max_props:
            self._errors.append(f"{path}: expected at most {max_props} properties, got {len(data)}")

    def _validate_array(self, data: Any, schema: Dict, path: str):
        if not isinstance(data, list):
            return
        items_schema = schema.get("items")
        if items_schema:
            for i, item in enumerate(data):
                self._validate_node(item, items_schema, f"{path}[{i}]")
        min_items = schema.get("minItems")
        max_items = schema.get("maxItems")
        if min_items is not None and len(data) < min_items:
            self._errors.append(f"{path}: expected at least {min_items} items, got {len(data)}")
        if max_items is not None and len(data) > max_items:
            self._errors.append(f"{path}: expected at most {max_items} items, got {len(data)}")
        if schema.get("uniqueItems"):
            seen = []
            for i, item in enumerate(data):
                serialized = json.dumps(item, sort_keys=True)
                if serialized in seen:
                    self._errors.append(f"{path}[{i}]: duplicate item")
                seen.append(serialized)

    def _validate_string(self, data: Any, schema: Dict, path: str):
        if not isinstance(data, str):
            return
        min_len = schema.get("minLength")
        max_len = schema.get("maxLength")
        if min_len is not None and len(data) < min_len:
            self._errors.append(f"{path}: string length {len(data)} < minLength {min_len}")
        if max_len is not None and len(data) > max_len:
            self._errors.append(f"{path}: string length {len(data)} > maxLength {max_len}")
        pattern = schema.get("pattern")
        if pattern:
            if not re.search(pattern, data):
                self._errors.append(f"{path}: string does not match pattern {pattern!r}")

    def _validate_number(self, data: Any, schema: Dict, path: str):
        if not isinstance(data, (int, float)) or isinstance(data, bool):
            return
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")
        exclusive_min = schema.get("exclusiveMinimum")
        exclusive_max = schema.get("exclusiveMaximum")
        multiple_of = schema.get("multipleOf")
        if minimum is not None and data < minimum:
            self._errors.append(f"{path}: {data} < minimum {minimum}")
        if maximum is not None and data > maximum:
            self._errors.append(f"{path}: {data} > maximum {maximum}")
        if exclusive_min is not None and data <= exclusive_min:
            self._errors.append(f"{path}: {data} <= exclusiveMinimum {exclusive_min}")
        if exclusive_max is not None and data >= exclusive_max:
            self._errors.append(f"{path}: {data} >= exclusiveMaximum {exclusive_max}")
        if multiple_of is not None and data % multiple_of != 0:
            self._errors.append(f"{path}: {data} is not a multiple of {multiple_of}")


def validate_schema(data: Any, schema: Dict[str, Any]) -> Tuple[bool, List[str]]:
    validator = SchemaValidator(schema)
    return validator.validate(data)


def parse_structured_output(
    text: str,
    schema: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    parsed, error = parse_json_safe(text)
    if parsed is None:
        raise SchemaValidationError(f"Could not parse JSON: {error}")
    if not isinstance(parsed, dict):
        if isinstance(parsed, list):
            parsed = {"items": parsed}
        else:
            parsed = {"value": parsed}
    if schema is not None:
        valid, errors = validate_schema(parsed, schema)
        if not valid:
            raise SchemaValidationError(
                f"Schema validation failed: {'; '.join(errors)}",
                value=parsed,
            )
    return parsed


# ---------------------------------------------------------------------------
# Provider abstraction
# ---------------------------------------------------------------------------

class ProviderConfig:
    def __init__(self, provider: Provider):
        self.provider = provider

    def format_request(
        self,
        prompt: str,
        model: ModelConfig,
        temperature: float,
        max_tokens: Optional[int],
        output_schema: Optional[Dict] = None,
    ) -> Dict[str, Any]:
        raise NotImplementedError

    def parse_response(self, raw: Dict[str, Any]) -> Dict[str, Any]:
        raise NotImplementedError

    def get_headers(self, api_key: str) -> Dict[str, str]:
        raise NotImplementedError

    def simulate_response(
        self,
        prompt: str,
        model: ModelConfig,
        output_schema: Optional[Dict] = None,
        fail_mode: Optional[str] = None,
    ) -> Dict[str, Any]:
        raise NotImplementedError


class OpenAIProvider(ProviderConfig):
    def __init__(self):
        super().__init__(Provider.OPENAI)
        self._response_templates: Dict[str, str] = {
            "default": "This is a simulated OpenAI response.",
            "reasoning": "<thinking>Analyzing the problem step by step.</thinking>\nThe answer is 42.",
            "structured": '{"result": "simulated", "confidence": 0.95}',
        }

    def format_request(self, prompt, model, temperature, max_tokens, output_schema=None):
        request = {
            "model": model.name,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": temperature,
        }
        if max_tokens:
            request["max_tokens"] = max_tokens
        if output_schema and model.supports_structured_output:
            request["response_format"] = {
                "type": "json_schema",
                "json_schema": {"name": "output", "schema": output_schema},
            }
        return request

    def parse_response(self, raw):
        choices = raw.get("choices", [])
        if not choices:
            raise ServerError("No choices in response")
        choice = choices[0]
        message = choice.get("message", {})
        content = message.get("content", "")
        usage = raw.get("usage", {})
        return {
            "content": content,
            "input_tokens": usage.get("prompt_tokens", 0),
            "output_tokens": usage.get("completion_tokens", 0),
            "finish_reason": choice.get("finish_reason", "stop"),
            "thinking": None,
        }

    def get_headers(self, api_key):
        return {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        }

    def simulate_response(self, prompt, model, output_schema=None, fail_mode=None):
        if fail_mode == "rate_limit":
            raise RateLimitError("Rate limit exceeded", retry_after=1.0)
        if fail_mode == "timeout":
            raise TimeoutError("Request timed out")
        if fail_mode == "server_error":
            raise ServerError("Internal server error", status_code=500)
        if fail_mode == "overloaded":
            raise ModelOverloadedError()
        input_tokens = count_tokens(prompt)
        if output_schema:
            content = self._response_templates["structured"]
            if output_schema.get("properties"):
                content = self._generate_schema_response(output_schema)
        elif model.is_reasoning_model:
            content = self._response_templates["reasoning"]
        else:
            content = self._response_templates["default"]
        output_tokens = count_tokens(content)
        return {
            "choices": [{
                "message": {"content": content},
                "finish_reason": "stop",
            }],
            "usage": {
                "prompt_tokens": input_tokens,
                "completion_tokens": output_tokens,
            },
        }

    def _generate_schema_response(self, schema: Dict) -> str:
        obj = self._generate_from_schema(schema)
        return json.dumps(obj)

    def _generate_from_schema(self, schema: Dict) -> Any:
        schema_type = schema.get("type", "string")
        if schema_type == "object":
            result = {}
            for key, prop in schema.get("properties", {}).items():
                result[key] = self._generate_from_schema(prop)
            return result
        elif schema_type == "array":
            items = schema.get("items", {"type": "string"})
            return [self._generate_from_schema(items)]
        elif schema_type == "string":
            if "enum" in schema:
                return schema["enum"][0]
            return "simulated_value"
        elif schema_type == "number":
            return 0.5
        elif schema_type == "integer":
            return 1
        elif schema_type == "boolean":
            return True
        return None


class AnthropicProvider(ProviderConfig):
    def __init__(self):
        super().__init__(Provider.ANTHROPIC)
        self._response_templates = {
            "default": "This is a simulated Anthropic response.",
            "thinking": "Let me think about this carefully.",
            "structured": '{"result": "simulated", "confidence": 0.92}',
        }

    def format_request(self, prompt, model, temperature, max_tokens, output_schema=None):
        request = {
            "model": model.name,
            "messages": [{"role": "user", "content": prompt}],
            "max_tokens": max_tokens or 4096,
        }
        if model.reasoning_type != ReasoningType.EXTENDED_THINKING:
            request["temperature"] = temperature
        else:
            request["temperature"] = 1.0
            request["thinking"] = {"type": "enabled", "budget_tokens": 10000}
        if output_schema and model.supports_structured_output:
            request["tool_use"] = {
                "type": "auto",
                "tools": [{
                    "name": "structured_output",
                    "input_schema": output_schema,
                }],
            }
        return request

    def parse_response(self, raw):
        content_blocks = raw.get("content", [])
        text_parts = []
        thinking_parts = []
        for block in content_blocks:
            if block.get("type") == "text":
                text_parts.append(block.get("text", ""))
            elif block.get("type") == "thinking":
                thinking_parts.append(block.get("thinking", ""))
            elif block.get("type") == "tool_use":
                text_parts.append(json.dumps(block.get("input", {})))
        usage = raw.get("usage", {})
        return {
            "content": "\n".join(text_parts),
            "input_tokens": usage.get("input_tokens", 0),
            "output_tokens": usage.get("output_tokens", 0),
            "finish_reason": raw.get("stop_reason", "end_turn"),
            "thinking": "\n".join(thinking_parts) if thinking_parts else None,
        }

    def get_headers(self, api_key):
        return {
            "x-api-key": api_key,
            "Content-Type": "application/json",
            "anthropic-version": "2024-10-22",
        }

    def simulate_response(self, prompt, model, output_schema=None, fail_mode=None):
        if fail_mode == "rate_limit":
            raise RateLimitError("Rate limit exceeded", retry_after=2.0)
        if fail_mode == "timeout":
            raise TimeoutError("Request timed out")
        if fail_mode == "server_error":
            raise ServerError("Internal server error", status_code=529)
        if fail_mode == "overloaded":
            raise ModelOverloadedError()
        input_tokens = count_tokens(prompt)
        content_blocks = []
        if model.reasoning_type == ReasoningType.EXTENDED_THINKING:
            content_blocks.append({
                "type": "thinking",
                "thinking": self._response_templates["thinking"],
            })
        if output_schema and model.supports_structured_output:
            response_obj = self._generate_structured(output_schema)
            content_blocks.append({
                "type": "tool_use",
                "id": "tool_001",
                "name": "structured_output",
                "input": response_obj,
            })
            output_text = json.dumps(response_obj)
        else:
            output_text = self._response_templates["default"]
            content_blocks.append({"type": "text", "text": output_text})
        output_tokens = count_tokens(output_text)
        return {
            "content": content_blocks,
            "usage": {
                "input_tokens": input_tokens,
                "output_tokens": output_tokens,
            },
            "stop_reason": "end_turn",
        }

    def _generate_structured(self, schema: Dict) -> Dict:
        result = {}
        for key, prop in schema.get("properties", {}).items():
            ptype = prop.get("type", "string")
            if ptype == "string":
                result[key] = "simulated"
            elif ptype == "number":
                result[key] = 0.5
            elif ptype == "integer":
                result[key] = 1
            elif ptype == "boolean":
                result[key] = True
            elif ptype == "array":
                result[key] = []
            elif ptype == "object":
                result[key] = {}
        return result


class GoogleProvider(ProviderConfig):
    def __init__(self):
        super().__init__(Provider.GOOGLE)
        self._safety_ratings = [
            {"category": "HARM_CATEGORY_HARASSMENT", "probability": "NEGLIGIBLE"},
            {"category": "HARM_CATEGORY_HATE_SPEECH", "probability": "NEGLIGIBLE"},
        ]

    def format_request(self, prompt, model, temperature, max_tokens, output_schema=None):
        request = {
            "contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": {
                "temperature": temperature,
                "maxOutputTokens": max_tokens or 8192,
            },
        }
        if output_schema and model.supports_structured_output:
            request["generationConfig"]["response_mime_type"] = "application/json"
            request["generationConfig"]["response_schema"] = output_schema
        return request

    def parse_response(self, raw):
        candidates = raw.get("candidates", [])
        if not candidates:
            raise ServerError("No candidates in response")
        candidate = candidates[0]
        content = candidate.get("content", {})
        parts = content.get("parts", [])
        text_parts = []
        thinking_parts = []
        for part in parts:
            if "text" in part:
                text_parts.append(part["text"])
            if "thought" in part:
                thinking_parts.append(part["thought"])
        usage = raw.get("usageMetadata", {})
        return {
            "content": "\n".join(text_parts),
            "input_tokens": usage.get("promptTokenCount", 0),
            "output_tokens": usage.get("candidatesTokenCount", 0),
            "finish_reason": candidate.get("finishReason", "STOP"),
            "thinking": "\n".join(thinking_parts) if thinking_parts else None,
        }

    def get_headers(self, api_key):
        return {
            "x-goog-api-key": api_key,
            "Content-Type": "application/json",
        }

    def simulate_response(self, prompt, model, output_schema=None, fail_mode=None):
        if fail_mode == "rate_limit":
            raise RateLimitError("Resource exhausted", retry_after=5.0)
        if fail_mode == "timeout":
            raise TimeoutError("Deadline exceeded")
        if fail_mode == "server_error":
            raise ServerError("Internal error", status_code=500)
        if fail_mode == "overloaded":
            raise ModelOverloadedError("Model overloaded")
        input_tokens = count_tokens(prompt)
        parts = []
        if model.is_reasoning_model:
            parts.append({"thought": "Reasoning about the problem systematically."})
        if output_schema and model.supports_structured_output:
            response_obj = self._generate_structured(output_schema)
            output_text = json.dumps(response_obj)
        else:
            output_text = "This is a simulated Google response."
        parts.append({"text": output_text})
        output_tokens = count_tokens(output_text)
        return {
            "candidates": [{
                "content": {"parts": parts},
                "finishReason": "STOP",
                "safetyRatings": self._safety_ratings,
            }],
            "usageMetadata": {
                "promptTokenCount": input_tokens,
                "candidatesTokenCount": output_tokens,
            },
        }

    def _generate_structured(self, schema: Dict) -> Dict:
        result = {}
        for key, prop in schema.get("properties", {}).items():
            ptype = prop.get("type", "string")
            if ptype == "string":
                result[key] = "generated"
            elif ptype == "number":
                result[key] = 1.0
            elif ptype == "integer":
                result[key] = 42
            elif ptype == "boolean":
                result[key] = False
            elif ptype == "array":
                result[key] = ["item"]
            elif ptype == "object":
                result[key] = {"nested": "value"}
        return result


def get_provider(provider: Provider) -> ProviderConfig:
    providers = {
        Provider.OPENAI: OpenAIProvider,
        Provider.ANTHROPIC: AnthropicProvider,
        Provider.GOOGLE: GoogleProvider,
    }
    cls = providers.get(provider)
    if cls is None:
        raise InvalidRequestError(f"Unknown provider: {provider}")
    return cls()


# ---------------------------------------------------------------------------
# Response caching
# ---------------------------------------------------------------------------

class ResponseCache:
    def __init__(self, max_size: int = 128, strategy: CacheStrategy = CacheStrategy.LRU):
        self._max_size = max_size
        self._strategy = strategy
        self._cache: OrderedDict[str, Dict[str, Any]] = OrderedDict()
        self._hits = 0
        self._misses = 0
        self._lock = threading.Lock()

    @property
    def hit_rate(self) -> float:
        total = self._hits + self._misses
        if total == 0:
            return 0.0
        return self._hits / total

    @property
    def size(self) -> int:
        return len(self._cache)

    def compute_key(
        self,
        prompt: str,
        model_name: str,
        temperature: float,
        output_schema: Optional[Dict] = None,
    ) -> str:
        key_data = {
            "prompt": prompt,
            "model": model_name,
            "temperature": round(temperature, 4),
        }
        if output_schema:
            key_data["schema"] = json.dumps(output_schema, sort_keys=True)
        serialized = json.dumps(key_data, sort_keys=True)
        return hashlib.sha256(serialized.encode()).hexdigest()

    def get(self, key: str) -> Optional[Dict[str, Any]]:
        if self._strategy == CacheStrategy.NONE:
            self._misses += 1
            return None
        with self._lock:
            if key in self._cache:
                self._hits += 1
                self._cache.move_to_end(key)
                return copy.deepcopy(self._cache[key])
            self._misses += 1
            return None

    def put(self, key: str, value: Dict[str, Any]):
        if self._strategy == CacheStrategy.NONE:
            return
        with self._lock:
            if key in self._cache:
                self._cache.move_to_end(key)
                self._cache[key] = copy.deepcopy(value)
            else:
                if len(self._cache) >= self._max_size:
                    self._cache.popitem(last=False)
                self._cache[key] = copy.deepcopy(value)

    def invalidate(self, key: str):
        with self._lock:
            self._cache.pop(key, None)

    def clear(self):
        with self._lock:
            self._cache.clear()
            self._hits = 0
            self._misses = 0

    def stats(self) -> Dict[str, Any]:
        return {
            "size": self.size,
            "max_size": self._max_size,
            "hits": self._hits,
            "misses": self._misses,
            "hit_rate": self.hit_rate,
            "strategy": self._strategy.value,
        }


# ---------------------------------------------------------------------------
# Cost calculation
# ---------------------------------------------------------------------------

class CostCalculator:
    def __init__(self, models: Optional[List[ModelConfig]] = None):
        self._rate_lookup: Dict[str, ModelConfig] = {}
        if models:
            for m in models:
                self._rate_lookup[m.name] = m

    def calculate(self, input_tokens: int, output_tokens: int, model: ModelConfig) -> float:
        input_cost = (input_tokens / 1_000_000) * model.input_cost_per_million
        output_cost = (output_tokens / 1_000_000) * model.output_cost_per_million
        return input_cost + output_cost

    def calculate_by_name(self, input_tokens: int, output_tokens: int, model_name: str) -> float:
        model = self._rate_lookup.get(model_name)
        if model is None:
            logger.warning("No rate info for model %s, returning 0", model_name)
            return 0.0
        return self.calculate(input_tokens, output_tokens, model)

    def estimate_cost(
        self,
        prompt: str,
        model: ModelConfig,
        estimated_output_ratio: float = 1.0,
    ) -> float:
        input_tokens = count_tokens(prompt)
        output_tokens = int(input_tokens * estimated_output_ratio)
        return self.calculate(input_tokens, output_tokens, model)


def calculate_cost(input_tokens: int, output_tokens: int, model: ModelConfig) -> float:
    calc = CostCalculator()
    return calc.calculate(input_tokens, output_tokens, model)


# ---------------------------------------------------------------------------
# Retry configuration and logic
# ---------------------------------------------------------------------------

@dataclass
class RetryConfig:
    max_retries: int = 3
    base_delay: float = 1.0
    max_delay: float = 60.0
    jitter_factor: float = 0.1
    retry_on: Tuple[type, ...] = (TransientError,)

    def compute_delay(self, attempt: int) -> float:
        delay = self.base_delay * (2 ** attempt)
        delay = min(delay, self.max_delay)
        jitter = delay * self.jitter_factor * random.random()
        return delay + jitter

    def should_retry(self, error: Exception, attempt: int) -> bool:
        if attempt >= self.max_retries:
            return False
        return isinstance(error, self.retry_on)


class RetryState:
    def __init__(self, config: RetryConfig):
        self.config = config
        self.attempt = 0
        self.errors: List[Exception] = []
        self.delays: List[float] = []
        self.total_delay = 0.0

    def record_attempt(self, error: Exception):
        self.errors.append(error)
        self.attempt += 1

    def record_delay(self, delay: float):
        self.delays.append(delay)
        self.total_delay += delay

    @property
    def should_continue(self) -> bool:
        if not self.errors:
            return True
        return self.config.should_retry(self.errors[-1], self.attempt)

    @property
    def next_delay(self) -> float:
        return self.config.compute_delay(self.attempt)

    def summary(self) -> Dict[str, Any]:
        return {
            "attempts": self.attempt + 1,
            "retries": self.attempt,
            "errors": [str(e) for e in self.errors],
            "total_delay": self.total_delay,
            "delays": self.delays,
        }


# ---------------------------------------------------------------------------
# Invocation diagnostics and logging
# ---------------------------------------------------------------------------

@dataclass
class InvocationDiagnostics:
    model_selection_time_ms: float = 0.0
    context_validation_time_ms: float = 0.0
    cache_lookup_time_ms: float = 0.0
    request_format_time_ms: float = 0.0
    provider_call_time_ms: float = 0.0
    response_parse_time_ms: float = 0.0
    schema_validation_time_ms: float = 0.0
    total_time_ms: float = 0.0
    retry_count: int = 0
    cache_hit: bool = False
    warnings: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "model_selection_ms": round(self.model_selection_time_ms, 2),
            "context_validation_ms": round(self.context_validation_time_ms, 2),
            "cache_lookup_ms": round(self.cache_lookup_time_ms, 2),
            "request_format_ms": round(self.request_format_time_ms, 2),
            "provider_call_ms": round(self.provider_call_time_ms, 2),
            "response_parse_ms": round(self.response_parse_time_ms, 2),
            "schema_validation_ms": round(self.schema_validation_time_ms, 2),
            "total_ms": round(self.total_time_ms, 2),
            "retry_count": self.retry_count,
            "cache_hit": self.cache_hit,
            "warnings": self.warnings,
        }


class InvocationLogger:
    def __init__(self):
        self._log: List[Dict[str, Any]] = []
        self._lock = threading.Lock()

    def record(
        self,
        model_name: str,
        input_tokens: int,
        output_tokens: int,
        cost: float,
        diagnostics: InvocationDiagnostics,
    ):
        entry = {
            "timestamp": time.time(),
            "model": model_name,
            "input_tokens": input_tokens,
            "output_tokens": output_tokens,
            "cost": cost,
            "diagnostics": diagnostics.to_dict(),
        }
        with self._lock:
            self._log.append(entry)
        logger.info(
            "Invocation: model=%s tokens=%d/%d cost=%.6f retries=%d cache=%s",
            model_name,
            input_tokens,
            output_tokens,
            cost,
            diagnostics.retry_count,
            diagnostics.cache_hit,
        )

    def get_log(self) -> List[Dict[str, Any]]:
        with self._lock:
            return list(self._log)

    def total_cost(self) -> float:
        with self._lock:
            return sum(entry["cost"] for entry in self._log)

    def total_tokens(self) -> Tuple[int, int]:
        with self._lock:
            inp = sum(entry["input_tokens"] for entry in self._log)
            out = sum(entry["output_tokens"] for entry in self._log)
            return inp, out

    def average_cost(self) -> float:
        with self._lock:
            if not self._log:
                return 0.0
            return sum(entry["cost"] for entry in self._log) / len(self._log)

    def model_usage_breakdown(self) -> Dict[str, Dict[str, Any]]:
        with self._lock:
            breakdown: Dict[str, Dict[str, Any]] = {}
            for entry in self._log:
                model = entry["model"]
                if model not in breakdown:
                    breakdown[model] = {
                        "count": 0,
                        "total_cost": 0.0,
                        "total_input_tokens": 0,
                        "total_output_tokens": 0,
                    }
                breakdown[model]["count"] += 1
                breakdown[model]["total_cost"] += entry["cost"]
                breakdown[model]["total_input_tokens"] += entry["input_tokens"]
                breakdown[model]["total_output_tokens"] += entry["output_tokens"]
            return breakdown


# ---------------------------------------------------------------------------
# Usage tracker
# ---------------------------------------------------------------------------

class UsageTracker:
    def __init__(self):
        self._total_input = 0
        self._total_output = 0
        self._total_cost = 0.0
        self._invocation_count = 0
        self._per_model: Dict[str, Dict[str, Any]] = {}
        self._lock = threading.Lock()

    def record(self, model_name: str, input_tokens: int, output_tokens: int, cost: float):
        with self._lock:
            self._total_input += input_tokens
            self._total_output += output_tokens
            self._total_cost += cost
            self._invocation_count += 1
            if model_name not in self._per_model:
                self._per_model[model_name] = {
                    "count": 0, "input": 0, "output": 0, "cost": 0.0,
                }
            self._per_model[model_name]["count"] += 1
            self._per_model[model_name]["input"] += input_tokens
            self._per_model[model_name]["output"] += output_tokens
            self._per_model[model_name]["cost"] += cost

    def summary(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "total_input_tokens": self._total_input,
                "total_output_tokens": self._total_output,
                "total_cost": self._total_cost,
                "invocation_count": self._invocation_count,
                "per_model": dict(self._per_model),
            }

    def reset(self):
        with self._lock:
            self._total_input = 0
            self._total_output = 0
            self._total_cost = 0.0
            self._invocation_count = 0
            self._per_model.clear()


# ---------------------------------------------------------------------------
# Request builder and response parser pipeline
# ---------------------------------------------------------------------------

class RequestBuilder:
    def __init__(self, provider_config: ProviderConfig):
        self._provider = provider_config

    def build(
        self,
        prompt: str,
        model: ModelConfig,
        temperature: float,
        max_tokens: Optional[int],
        output_schema: Optional[Dict],
        system_prompt: Optional[str] = None,
        stop_sequences: Optional[List[str]] = None,
    ) -> Dict[str, Any]:
        request = self._provider.format_request(
            prompt, model, temperature, max_tokens, output_schema,
        )
        if system_prompt:
            request = self._inject_system_prompt(request, system_prompt, model)
        if stop_sequences:
            request = self._inject_stop_sequences(request, stop_sequences, model)
        return request

    def _inject_system_prompt(
        self, request: Dict, system_prompt: str, model: ModelConfig,
    ) -> Dict:
        if model.provider == Provider.OPENAI:
            messages = request.get("messages", [])
            messages.insert(0, {"role": "system", "content": system_prompt})
            request["messages"] = messages
        elif model.provider == Provider.ANTHROPIC:
            request["system"] = system_prompt
        elif model.provider == Provider.GOOGLE:
            contents = request.get("contents", [])
            if contents:
                first = contents[0]
                parts = first.get("parts", [])
                parts.insert(0, {"text": f"[System]: {system_prompt}\n\n"})
                first["parts"] = parts
        return request

    def _inject_stop_sequences(
        self, request: Dict, sequences: List[str], model: ModelConfig,
    ) -> Dict:
        if model.provider == Provider.OPENAI:
            request["stop"] = sequences
        elif model.provider == Provider.ANTHROPIC:
            request["stop_sequences"] = sequences
        elif model.provider == Provider.GOOGLE:
            gen_config = request.get("generationConfig", {})
            gen_config["stopSequences"] = sequences
            request["generationConfig"] = gen_config
        return request


class ResponseParser:
    def __init__(self, provider_config: ProviderConfig):
        self._provider = provider_config

    def parse(self, raw_response: Dict[str, Any]) -> Dict[str, Any]:
        parsed = self._provider.parse_response(raw_response)
        parsed["raw"] = raw_response
        return parsed


# ---------------------------------------------------------------------------
# Batch processing support
# ---------------------------------------------------------------------------

@dataclass
class BatchItem:
    prompt: str
    strength: float = 0.5
    temperature: float = 0.7
    output_schema: Optional[Dict] = None
    metadata: Optional[Dict] = None


@dataclass
class BatchResult:
    results: List[Any]
    total_cost: float
    total_input_tokens: int
    total_output_tokens: int
    error_count: int
    errors: List[Tuple[int, str]]

    def success_rate(self) -> float:
        if not self.results:
            return 0.0
        return 1.0 - (self.error_count / len(self.results))


# ---------------------------------------------------------------------------
# Prompt preprocessor
# ---------------------------------------------------------------------------

class PromptPreprocessor:
    def __init__(self):
        self._transformations: List[Callable[[str], str]] = []

    def add_transformation(self, fn: Callable[[str], str]):
        self._transformations.append(fn)

    def process(self, prompt: str) -> str:
        for fn in self._transformations:
            prompt = fn(prompt)
        return prompt

    @staticmethod
    def strip_excessive_whitespace(text: str) -> str:
        lines = text.split('\n')
        cleaned = []
        blank_count = 0
        for line in lines:
            stripped = line.rstrip()
            if not stripped:
                blank_count += 1
                if blank_count <= 2:
                    cleaned.append('')
            else:
                blank_count = 0
                cleaned.append(stripped)
        return '\n'.join(cleaned)

    @staticmethod
    def normalize_unicode(text: str) -> str:
        replacements = {
            '\u2018': "'", '\u2019': "'",
            '\u201c': '"', '\u201d': '"',
            '\u2013': '-', '\u2014': '--',
            '\u2026': '...',
            '\u00a0': ' ',
        }
        for old, new in replacements.items():
            text = text.replace(old, new)
        return text

    @staticmethod
    def truncate_to_token_limit(text: str, max_tokens: int) -> str:
        tokens = count_tokens(text)
        if tokens <= max_tokens:
            return text
        ratio = max_tokens / tokens
        target_chars = int(len(text) * ratio * 0.9)
        truncated = text[:target_chars]
        last_period = truncated.rfind('.')
        last_newline = truncated.rfind('\n')
        cut_point = max(last_period, last_newline)
        if cut_point > target_chars * 0.5:
            truncated = truncated[:cut_point + 1]
        return truncated + "\n[TRUNCATED]"


# ---------------------------------------------------------------------------
# Rate limiter (local, token-bucket)
# ---------------------------------------------------------------------------

class TokenBucketRateLimiter:
    def __init__(self, tokens_per_second: float, burst_size: int):
        self._rate = tokens_per_second
        self._burst = burst_size
        self._tokens = float(burst_size)
        self._last_refill = time.monotonic()
        self._lock = threading.Lock()

    def acquire(self, tokens: int = 1) -> float:
        with self._lock:
            now = time.monotonic()
            elapsed = now - self._last_refill
            self._tokens = min(self._burst, self._tokens + elapsed * self._rate)
            self._last_refill = now
            if self._tokens >= tokens:
                self._tokens -= tokens
                return 0.0
            deficit = tokens - self._tokens
            wait_time = deficit / self._rate
            self._tokens = 0
            return wait_time

    def try_acquire(self, tokens: int = 1) -> bool:
        with self._lock:
            now = time.monotonic()
            elapsed = now - self._last_refill
            self._tokens = min(self._burst, self._tokens + elapsed * self._rate)
            self._last_refill = now
            if self._tokens >= tokens:
                self._tokens -= tokens
                return True
            return False


# ---------------------------------------------------------------------------
# Conversation / message history
# ---------------------------------------------------------------------------

class MessageRole(Enum):
    SYSTEM = "system"
    USER = "user"
    ASSISTANT = "assistant"


@dataclass
class Message:
    role: MessageRole
    content: str
    name: Optional[str] = None
    metadata: Optional[Dict] = None

    def token_count(self) -> int:
        overhead = 4
        return count_tokens(self.content) + overhead

    def to_dict(self) -> Dict[str, Any]:
        d = {"role": self.role.value, "content": self.content}
        if self.name:
            d["name"] = self.name
        return d


class Conversation:
    def __init__(self, system_prompt: Optional[str] = None):
        self._messages: List[Message] = []
        if system_prompt:
            self._messages.append(Message(role=MessageRole.SYSTEM, content=system_prompt))

    def add_user_message(self, content: str, name: Optional[str] = None):
        self._messages.append(Message(role=MessageRole.USER, content=content, name=name))

    def add_assistant_message(self, content: str):
        self._messages.append(Message(role=MessageRole.ASSISTANT, content=content))

    def total_tokens(self) -> int:
        return sum(m.token_count() for m in self._messages)

    def to_prompt(self) -> str:
        parts = []
        for msg in self._messages:
            if msg.role == MessageRole.SYSTEM:
                parts.append(f"[System]\n{msg.content}")
            elif msg.role == MessageRole.USER:
                prefix = f"[{msg.name}]" if msg.name else "[User]"
                parts.append(f"{prefix}\n{msg.content}")
            else:
                parts.append(f"[Assistant]\n{msg.content}")
        return "\n\n".join(parts)

    def trim_to_fit(self, max_tokens: int) -> int:
        removed = 0
        while len(self._messages) > 1 and self.total_tokens() > max_tokens:
            if self._messages[0].role == MessageRole.SYSTEM:
                if len(self._messages) > 2:
                    self._messages.pop(1)
                    removed += 1
                else:
                    break
            else:
                self._messages.pop(0)
                removed += 1
        return removed

    @property
    def messages(self) -> List[Message]:
        return list(self._messages)

    def __len__(self) -> int:
        return len(self._messages)


# ---------------------------------------------------------------------------
# Model router (strength-based with overrides)
# ---------------------------------------------------------------------------

class ModelRouter:
    def __init__(self, models: List[ModelConfig]):
        self._models = models
        self._overrides: Dict[str, ModelConfig] = {}
        self._fallbacks: Dict[str, str] = {}

    def set_override(self, task_type: str, model: ModelConfig):
        self._overrides[task_type] = model

    def set_fallback(self, model_name: str, fallback_name: str):
        self._fallbacks[model_name] = fallback_name

    def route(
        self,
        strength: float,
        task_type: Optional[str] = None,
        require_structured: bool = False,
    ) -> ModelConfig:
        if task_type and task_type in self._overrides:
            return self._overrides[task_type]
        return select_model(
            self._models,
            strength,
            require_structured=require_structured,
        )

    def get_fallback(self, model: ModelConfig) -> Optional[ModelConfig]:
        fallback_name = self._fallbacks.get(model.name)
        if fallback_name:
            for m in self._models:
                if m.name == fallback_name:
                    return m
        cheaper = [m for m in self._models if m.effective_cost < model.effective_cost]
        if cheaper:
            cheaper.sort(key=lambda m: m.elo, reverse=True)
            return cheaper[0]
        return None


# ---------------------------------------------------------------------------
# Error classifier
# ---------------------------------------------------------------------------

class ErrorClassifier:
    _TRANSIENT_PATTERNS = [
        (re.compile(r'rate.?limit', re.IGNORECASE), ErrorCategory.RATE_LIMIT),
        (re.compile(r'timeout', re.IGNORECASE), ErrorCategory.TIMEOUT),
        (re.compile(r'server.?error', re.IGNORECASE), ErrorCategory.SERVER_ERROR),
        (re.compile(r'overloaded', re.IGNORECASE), ErrorCategory.MODEL_OVERLOADED),
        (re.compile(r'5\d{2}', re.IGNORECASE), ErrorCategory.SERVER_ERROR),
        (re.compile(r'too.?many.?requests', re.IGNORECASE), ErrorCategory.RATE_LIMIT),
        (re.compile(r'capacity', re.IGNORECASE), ErrorCategory.MODEL_OVERLOADED),
    ]

    @classmethod
    def classify(cls, error: Exception) -> ErrorCategory:
        if isinstance(error, RateLimitError):
            return ErrorCategory.RATE_LIMIT
        if isinstance(error, TimeoutError):
            return ErrorCategory.TIMEOUT
        if isinstance(error, ServerError):
            return ErrorCategory.SERVER_ERROR
        if isinstance(error, ModelOverloadedError):
            return ErrorCategory.MODEL_OVERLOADED
        if isinstance(error, TransientError):
            return error.category
        msg = str(error)
        for pattern, category in cls._TRANSIENT_PATTERNS:
            if pattern.search(msg):
                return category
        return ErrorCategory.INVALID_REQUEST

    @classmethod
    def is_transient(cls, error: Exception) -> bool:
        category = cls.classify(error)
        return category in (
            ErrorCategory.TRANSIENT,
            ErrorCategory.RATE_LIMIT,
            ErrorCategory.TIMEOUT,
            ErrorCategory.SERVER_ERROR,
            ErrorCategory.MODEL_OVERLOADED,
        )


# ---------------------------------------------------------------------------
# Configuration container
# ---------------------------------------------------------------------------

@dataclass
class ClientConfig:
    default_strength: float = 0.5
    default_temperature: float = 0.7
    default_max_tokens: Optional[int] = None
    retry_config: RetryConfig = field(default_factory=RetryConfig)
    cache_strategy: CacheStrategy = CacheStrategy.LRU
    cache_max_size: int = 128
    token_estimation_method: TokenEstimationMethod = TokenEstimationMethod.HYBRID
    context_safety_margin: float = 0.05
    enable_logging: bool = True
    api_keys: Dict[str, str] = field(default_factory=dict)
    rate_limit_tokens_per_second: float = 10.0
    rate_limit_burst: int = 20

    def get_api_key(self, provider: Provider) -> str:
        return self.api_keys.get(provider.value, "sim_key_not_needed")


# ---------------------------------------------------------------------------
# InvocationResult
# ---------------------------------------------------------------------------

@dataclass
class InvocationResult:
    result: str
    cost: float
    model_name: str
    thinking_output: Optional[str]
    input_tokens: int
    output_tokens: int
    diagnostics: Optional[InvocationDiagnostics] = None
    cached: bool = False
    retry_count: int = 0

    def to_dict(self) -> Dict[str, Any]:
        d = {
            "result": self.result,
            "cost": self.cost,
            "model_name": self.model_name,
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "cached": self.cached,
            "retry_count": self.retry_count,
        }
        if self.thinking_output:
            d["thinking_output"] = self.thinking_output
        if self.diagnostics:
            d["diagnostics"] = self.diagnostics.to_dict()
        return d


# ---------------------------------------------------------------------------
# State machine for invocation
# ---------------------------------------------------------------------------

class InvocationStateMachine:
    _TRANSITIONS = {
        InvocationState.PENDING: [InvocationState.SELECTING_MODEL],
        InvocationState.SELECTING_MODEL: [
            InvocationState.VALIDATING_CONTEXT,
            InvocationState.FAILED,
        ],
        InvocationState.VALIDATING_CONTEXT: [
            InvocationState.CHECKING_CACHE,
            InvocationState.FAILED,
        ],
        InvocationState.CHECKING_CACHE: [
            InvocationState.COMPLETE,
            InvocationState.FORMATTING_REQUEST,
        ],
        InvocationState.FORMATTING_REQUEST: [
            InvocationState.SENDING,
            InvocationState.FAILED,
        ],
        InvocationState.SENDING: [
            InvocationState.PARSING_RESPONSE,
            InvocationState.RETRYING,
            InvocationState.FAILED,
        ],
        InvocationState.RETRYING: [
            InvocationState.SENDING,
            InvocationState.FAILED,
        ],
        InvocationState.PARSING_RESPONSE: [
            InvocationState.VALIDATING_OUTPUT,
            InvocationState.COMPLETE,
            InvocationState.FAILED,
        ],
        InvocationState.VALIDATING_OUTPUT: [
            InvocationState.COMPLETE,
            InvocationState.FAILED,
        ],
        InvocationState.COMPLETE: [],
        InvocationState.FAILED: [],
    }

    def __init__(self):
        self._state = InvocationState.PENDING
        self._history: List[Tuple[InvocationState, float]] = [
            (InvocationState.PENDING, time.time()),
        ]

    @property
    def state(self) -> InvocationState:
        return self._state

    def transition(self, new_state: InvocationState):
        allowed = self._TRANSITIONS.get(self._state, [])
        if new_state not in allowed:
            raise InvalidRequestError(
                f"Invalid state transition: {self._state.name} -> {new_state.name}"
            )
        self._state = new_state
        self._history.append((new_state, time.time()))

    @property
    def history(self) -> List[Tuple[InvocationState, float]]:
        return list(self._history)

    @property
    def is_terminal(self) -> bool:
        return self._state in (InvocationState.COMPLETE, InvocationState.FAILED)


# ---------------------------------------------------------------------------
# Middleware / hooks
# ---------------------------------------------------------------------------

class InvocationMiddleware:
    def before_request(self, prompt: str, model: ModelConfig) -> str:
        return prompt

    def after_response(self, result: InvocationResult) -> InvocationResult:
        return result

    def on_error(self, error: Exception, attempt: int) -> Optional[Exception]:
        return error


class LoggingMiddleware(InvocationMiddleware):
    def before_request(self, prompt, model):
        logger.debug("Request to %s: %d chars", model.name, len(prompt))
        return prompt

    def after_response(self, result):
        logger.debug(
            "Response from %s: %d tokens, cost %.6f",
            result.model_name, result.output_tokens, result.cost,
        )
        return result


class CostLimitMiddleware(InvocationMiddleware):
    def __init__(self, max_cost: float):
        self._max_cost = max_cost
        self._accumulated = 0.0

    def after_response(self, result):
        self._accumulated += result.cost
        if self._accumulated > self._max_cost:
            logger.warning(
                "Cost limit exceeded: %.6f > %.6f",
                self._accumulated, self._max_cost,
            )
        return result

    @property
    def accumulated_cost(self) -> float:
        return self._accumulated


class ContentFilterMiddleware(InvocationMiddleware):
    _BLOCKED_PATTERNS = [
        re.compile(r'(?:password|secret|api.?key)\s*[:=]\s*\S+', re.IGNORECASE),
    ]

    def before_request(self, prompt, model):
        for pattern in self._BLOCKED_PATTERNS:
            if pattern.search(prompt):
                raise ContentFilterError("Prompt contains potentially sensitive content")
        return prompt


# ---------------------------------------------------------------------------
# The main invoke function and LLMClient class
# ---------------------------------------------------------------------------

class LLMClient:
    def __init__(
        self,
        config: Optional[ClientConfig] = None,
        models: Optional[List[ModelConfig]] = None,
    ):
        self._config = config or ClientConfig()
        self._models = models or load_models()
        self._cache = ResponseCache(
            max_size=self._config.cache_max_size,
            strategy=self._config.cache_strategy,
        )
        self._cost_calculator = CostCalculator(self._models)
        self._context_validator = ContextWindowValidator(
            safety_margin=self._config.context_safety_margin,
        )
        self._token_counter = TokenCounter(method=self._config.token_estimation_method)
        self._inv_logger = InvocationLogger()
        self._usage_tracker = UsageTracker()
        self._router = ModelRouter(self._models)
        self._preprocessor = PromptPreprocessor()
        self._preprocessor.add_transformation(PromptPreprocessor.strip_excessive_whitespace)
        self._preprocessor.add_transformation(PromptPreprocessor.normalize_unicode)
        self._middleware: List[InvocationMiddleware] = [LoggingMiddleware()]
        self._rate_limiter = TokenBucketRateLimiter(
            tokens_per_second=self._config.rate_limit_tokens_per_second,
            burst_size=self._config.rate_limit_burst,
        )

    def add_middleware(self, middleware: InvocationMiddleware):
        self._middleware.append(middleware)

    @property
    def cache(self) -> ResponseCache:
        return self._cache

    @property
    def usage(self) -> UsageTracker:
        return self._usage_tracker

    @property
    def invocation_log(self) -> InvocationLogger:
        return self._inv_logger

    @property
    def models(self) -> List[ModelConfig]:
        return list(self._models)

    def invoke(
        self,
        prompt: str,
        input_json: Optional[Dict[str, Any]] = None,
        strength: Optional[float] = None,
        temperature: Optional[float] = None,
        output_schema: Optional[Dict[str, Any]] = None,
        max_tokens: Optional[int] = None,
        system_prompt: Optional[str] = None,
        retry_config: Optional[RetryConfig] = None,
        bypass_cache: bool = False,
        task_type: Optional[str] = None,
        stop_sequences: Optional[List[str]] = None,
        fail_sequence: Optional[List[Optional[str]]] = None,
    ) -> InvocationResult:
        strength = strength if strength is not None else self._config.default_strength
        temperature = temperature if temperature is not None else self._config.default_temperature
        max_tokens = max_tokens or self._config.default_max_tokens
        retry_cfg = retry_config or self._config.retry_config
        if input_json:
            prompt = format_prompt(prompt, input_json)
        prompt = self._preprocessor.process(prompt)
        for mw in self._middleware:
            prompt = mw.before_request(
                prompt,
                self._models[0] if self._models else None,
            )
        state_machine = InvocationStateMachine()
        diagnostics = InvocationDiagnostics()
        t_start = time.monotonic()
        state_machine.transition(InvocationState.SELECTING_MODEL)
        t0 = time.monotonic()
        require_structured = output_schema is not None
        model = self._router.route(
            strength,
            task_type=task_type,
            require_structured=require_structured,
        )
        diagnostics.model_selection_time_ms = (time.monotonic() - t0) * 1000
        state_machine.transition(InvocationState.VALIDATING_CONTEXT)
        t0 = time.monotonic()
        prompt_tokens = self._token_counter.count(prompt)
        if not self._context_validator.validate(prompt_tokens, model):
            state_machine.transition(InvocationState.FAILED)
            raise ContextOverflowError(prompt_tokens, model.context_limit)
        self._context_validator.warn_if_near_limit(prompt_tokens, model)
        diagnostics.context_validation_time_ms = (time.monotonic() - t0) * 1000
        state_machine.transition(InvocationState.CHECKING_CACHE)
        t0 = time.monotonic()
        if not bypass_cache:
            cache_key = self._cache.compute_key(
                prompt, model.name, temperature, output_schema,
            )
            cached = self._cache.get(cache_key)
            if cached is not None:
                diagnostics.cache_hit = True
                diagnostics.cache_lookup_time_ms = (time.monotonic() - t0) * 1000
                diagnostics.total_time_ms = (time.monotonic() - t_start) * 1000
                state_machine.transition(InvocationState.COMPLETE)
                result = InvocationResult(
                    result=cached["content"],
                    cost=0.0,
                    model_name=model.name,
                    thinking_output=cached.get("thinking"),
                    input_tokens=cached.get("input_tokens", 0),
                    output_tokens=cached.get("output_tokens", 0),
                    diagnostics=diagnostics,
                    cached=True,
                )
                for mw in self._middleware:
                    result = mw.after_response(result)
                return result
        diagnostics.cache_lookup_time_ms = (time.monotonic() - t0) * 1000
        state_machine.transition(InvocationState.FORMATTING_REQUEST)
        t0 = time.monotonic()
        provider = get_provider(model.provider)
        builder = RequestBuilder(provider)
        request = builder.build(
            prompt, model, temperature, max_tokens, output_schema,
            system_prompt=system_prompt,
            stop_sequences=stop_sequences,
        )
        diagnostics.request_format_time_ms = (time.monotonic() - t0) * 1000
        retry_state = RetryState(retry_cfg)
        total_cost = 0.0
        last_error = None
        attempt_index = 0
        state_machine.transition(InvocationState.SENDING)
        while True:
            try:
                fail_mode = None
                if fail_sequence and attempt_index < len(fail_sequence):
                    fail_mode = fail_sequence[attempt_index]
                t0 = time.monotonic()
                wait_time = self._rate_limiter.acquire()
                if wait_time > 0:
                    pass
                raw_response = provider.simulate_response(
                    prompt, model, output_schema, fail_mode=fail_mode,
                )
                diagnostics.provider_call_time_ms += (time.monotonic() - t0) * 1000
                state_machine.transition(InvocationState.PARSING_RESPONSE)
                t0 = time.monotonic()
                parser = ResponseParser(provider)
                parsed = parser.parse(raw_response)
                diagnostics.response_parse_time_ms += (time.monotonic() - t0) * 1000
                response_input_tokens = parsed.get("input_tokens", prompt_tokens)
                response_output_tokens = parsed.get("output_tokens", 0)
                attempt_cost = self._cost_calculator.calculate(
                    response_input_tokens,
                    response_output_tokens,
                    model,
                )
                total_cost = attempt_cost
                content = parsed.get("content", "")
                thinking = parsed.get("thinking")
                if output_schema:
                    state_machine.transition(InvocationState.VALIDATING_OUTPUT)
                    t0 = time.monotonic()
                    parse_structured_output(content, output_schema)
                    diagnostics.schema_validation_time_ms = (time.monotonic() - t0) * 1000
                if not bypass_cache:
                    self._cache.put(cache_key, {
                        "content": content,
                        "thinking": thinking,
                        "input_tokens": response_input_tokens,
                        "output_tokens": response_output_tokens,
                    })
                diagnostics.retry_count = retry_state.attempt
                diagnostics.total_time_ms = (time.monotonic() - t_start) * 1000
                if not state_machine.is_terminal:
                    state_machine.transition(InvocationState.COMPLETE)
                self._inv_logger.record(
                    model.name,
                    response_input_tokens,
                    response_output_tokens,
                    total_cost,
                    diagnostics,
                )
                self._usage_tracker.record(
                    model.name,
                    response_input_tokens,
                    response_output_tokens,
                    total_cost,
                )
                result = InvocationResult(
                    result=content,
                    cost=total_cost,
                    model_name=model.name,
                    thinking_output=thinking,
                    input_tokens=response_input_tokens,
                    output_tokens=response_output_tokens,
                    diagnostics=diagnostics,
                    retry_count=retry_state.attempt,
                )
                for mw in self._middleware:
                    result = mw.after_response(result)
                return result

            except LLMClientError as e:
                last_error = e
                failed_attempt_cost = self._cost_calculator.calculate(
                    prompt_tokens, 0, model,
                )
                total_cost += failed_attempt_cost
                for mw in self._middleware:
                    transformed = mw.on_error(e, retry_state.attempt)
                    if transformed is not None:
                        e = transformed
                if not ErrorClassifier.is_transient(e):
                    state_machine.transition(InvocationState.FAILED)
                    raise
                retry_state.record_attempt(e)
                if not retry_state.should_continue:
                    state_machine.transition(InvocationState.FAILED)
                    raise
                delay = retry_state.next_delay
                retry_state.record_delay(delay)
                logger.info(
                    "Retry %d/%d after %.2fs for %s: %s",
                    retry_state.attempt,
                    retry_cfg.max_retries,
                    delay,
                    model.name,
                    e,
                )
                attempt_index += 1
                if state_machine.state != InvocationState.RETRYING:
                    state_machine.transition(InvocationState.RETRYING)
                state_machine.transition(InvocationState.SENDING)

    def invoke_batch(
        self,
        items: List[BatchItem],
        parallel: bool = False,
    ) -> BatchResult:
        results = []
        total_cost = 0.0
        total_input = 0
        total_output = 0
        error_count = 0
        errors = []
        for i, item in enumerate(items):
            try:
                result = self.invoke(
                    prompt=item.prompt,
                    strength=item.strength,
                    temperature=item.temperature,
                    output_schema=item.output_schema,
                )
                results.append(result)
                total_cost += result.cost
                total_input += result.input_tokens
                total_output += result.output_tokens
            except LLMClientError as e:
                results.append(None)
                error_count += 1
                errors.append((i, str(e)))
        return BatchResult(
            results=results,
            total_cost=total_cost,
            total_input_tokens=total_input,
            total_output_tokens=total_output,
            error_count=error_count,
            errors=errors,
        )

    def invoke_with_fallback(
        self,
        prompt: str,
        strength: float = 0.5,
        temperature: float = 0.7,
        output_schema: Optional[Dict] = None,
        max_retries_per_model: int = 2,
    ) -> InvocationResult:
        model = self._router.route(strength, require_structured=output_schema is not None)
        tried_models = set()
        current_model_override = None
        while True:
            try:
                if current_model_override:
                    self._router.set_override("_fallback_temp", current_model_override)
                result = self.invoke(
                    prompt=prompt,
                    strength=strength,
                    temperature=temperature,
                    output_schema=output_schema,
                    retry_config=RetryConfig(max_retries=max_retries_per_model),
                    task_type="_fallback_temp" if current_model_override else None,
                )
                if current_model_override:
                    del self._router._overrides["_fallback_temp"]
                return result
            except LLMClientError:
                tried_models.add(
                    current_model_override.name if current_model_override else model.name
                )
                fallback_model = self._router.get_fallback(
                    current_model_override or model,
                )
                if fallback_model and fallback_model.name not in tried_models:
                    logger.info("Falling back to %s", fallback_model.name)
                    current_model_override = fallback_model
                    continue
                if current_model_override:
                    try:
                        del self._router._overrides["_fallback_temp"]
                    except KeyError:
                        pass
                raise

    def get_stats(self) -> Dict[str, Any]:
        return {
            "cache": self._cache.stats(),
            "usage": self._usage_tracker.summary(),
            "models_available": len(self._models),
        }


# ---------------------------------------------------------------------------
# Module-level convenience function
# ---------------------------------------------------------------------------

_default_client: Optional[LLMClient] = None
_client_lock = threading.Lock()


def get_default_client() -> LLMClient:
    global _default_client
    with _client_lock:
        if _default_client is None:
            _default_client = LLMClient()
        return _default_client


def configure(config: ClientConfig):
    global _default_client
    with _client_lock:
        _default_client = LLMClient(config=config)


def invoke(
    prompt: str,
    input_json: Optional[Dict[str, Any]] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    output_schema: Optional[Dict[str, Any]] = None,
    max_tokens: Optional[int] = None,
    system_prompt: Optional[str] = None,
    retry_config: Optional[RetryConfig] = None,
    bypass_cache: bool = False,
    fail_sequence: Optional[List[Optional[str]]] = None,
) -> InvocationResult:
    client = get_default_client()
    return client.invoke(
        prompt=prompt,
        input_json=input_json,
        strength=strength,
        temperature=temperature,
        output_schema=output_schema,
        max_tokens=max_tokens,
        system_prompt=system_prompt,
        retry_config=retry_config,
        bypass_cache=bypass_cache,
        fail_sequence=fail_sequence,
    )


# ---------------------------------------------------------------------------
# Model comparison utilities
# ---------------------------------------------------------------------------

class ModelComparator:
    def __init__(self, models: List[ModelConfig]):
        self._models = models

    def compare_by_cost(self) -> List[Tuple[str, float]]:
        return sorted(
            [(m.name, m.effective_cost) for m in self._models],
            key=lambda x: x[1],
        )

    def compare_by_capability(self) -> List[Tuple[str, int]]:
        return sorted(
            [(m.name, m.elo) for m in self._models],
            key=lambda x: x[1],
            reverse=True,
        )

    def compare_by_efficiency(self) -> List[Tuple[str, float]]:
        return sorted(
            [(m.name, m.cost_efficiency) for m in self._models],
            key=lambda x: x[1],
            reverse=True,
        )

    def find_pareto_optimal(self) -> List[ModelConfig]:
        sorted_models = sorted(self._models, key=lambda m: m.effective_cost)
        pareto = []
        max_elo = -1
        for m in sorted_models:
            if m.elo > max_elo:
                pareto.append(m)
                max_elo = m.elo
        return pareto

    def recommend(
        self,
        budget: Optional[float] = None,
        min_elo: Optional[int] = None,
        provider: Optional[Provider] = None,
    ) -> List[ModelConfig]:
        candidates = list(self._models)
        if budget is not None:
            candidates = [m for m in candidates if m.effective_cost <= budget]
        if min_elo is not None:
            candidates = [m for m in candidates if m.elo >= min_elo]
        if provider is not None:
            candidates = [m for m in candidates if m.provider == provider]
        candidates.sort(key=lambda m: m.cost_efficiency, reverse=True)
        return candidates


# ---------------------------------------------------------------------------
# Prompt builder with structured sections
# ---------------------------------------------------------------------------

class PromptSection:
    def __init__(self, name: str, content: str, priority: int = 0):
        self.name = name
        self.content = content
        self.priority = priority

    def token_count(self) -> int:
        return count_tokens(self.content) + count_tokens(self.name) + 4


class PromptBuilder:
    def __init__(self):
        self._sections: List[PromptSection] = []
        self._variables: Dict[str, Any] = {}

    def add_section(self, name: str, content: str, priority: int = 0):
        self._sections.append(PromptSection(name, content, priority))
        return self

    def set_variable(self, key: str, value: Any):
        self._variables[key] = value
        return self

    def build(self, max_tokens: Optional[int] = None) -> str:
        sections = sorted(self._sections, key=lambda s: s.priority, reverse=True)
        if max_tokens is not None:
            included = []
            total = 0
            for section in sections:
                tc = section.token_count()
                if total + tc <= max_tokens:
                    included.append(section)
                    total += tc
            sections = included
        sections.sort(key=lambda s: self._sections.index(s))
        parts = []
        for section in sections:
            content = section.content
            if self._variables:
                content = format_prompt(content, self._variables)
            parts.append(f"## {section.name}\n{content}")
        return "\n\n".join(parts)

    def total_tokens(self) -> int:
        return sum(s.token_count() for s in self._sections)


# ---------------------------------------------------------------------------
# Response post-processors
# ---------------------------------------------------------------------------

class ResponsePostProcessor:
    def process(self, text: str) -> str:
        raise NotImplementedError


class StripMarkdownProcessor(ResponsePostProcessor):
    _CODE_BLOCK = re.compile(r'```\w*\n([\s\S]*?)\n```')
    _BOLD = re.compile(r'\*\*(.*?)\*\*')
    _ITALIC = re.compile(r'\*(.*?)\*')
    _HEADER = re.compile(r'^#+\s+', re.MULTILINE)
    _LINK = re.compile(r'\[([^\]]+)\]\([^)]+\)')

    def process(self, text: str) -> str:
        text = self._CODE_BLOCK.sub(r'\1', text)
        text = self._BOLD.sub(r'\1', text)
        text = self._ITALIC.sub(r'\1', text)
        text = self._HEADER.sub('', text)
        text = self._LINK.sub(r'\1', text)
        return text.strip()


class ExtractCodeProcessor(ResponsePostProcessor):
    _CODE_BLOCK = re.compile(r'```(\w*)\n([\s\S]*?)\n```')

    def __init__(self, language: Optional[str] = None):
        self._language = language

    def process(self, text: str) -> str:
        matches = self._CODE_BLOCK.findall(text)
        if not matches:
            return text
        if self._language:
            for lang, code in matches:
                if lang.lower() == self._language.lower():
                    return code.strip()
        return matches[0][1].strip()


class ChainProcessor(ResponsePostProcessor):
    def __init__(self, processors: List[ResponsePostProcessor]):
        self._processors = processors

    def process(self, text: str) -> str:
        for proc in self._processors:
            text = proc.process(text)
        return text


# ---------------------------------------------------------------------------
# Streaming simulation
# ---------------------------------------------------------------------------

class StreamChunk:
    def __init__(self, text: str, is_final: bool = False, metadata: Optional[Dict] = None):
        self.text = text
        self.is_final = is_final
        self.metadata = metadata or {}


class StreamSimulator:
    def __init__(self, full_text: str, chunk_size: int = 20):
        self._full_text = full_text
        self._chunk_size = chunk_size
        self._position = 0

    def __iter__(self):
        return self

    def __next__(self) -> StreamChunk:
        if self._position >= len(self._full_text):
            raise StopIteration
        end = min(self._position + self._chunk_size, len(self._full_text))
        text = self._full_text[self._position:end]
        self._position = end
        is_final = self._position >= len(self._full_text)
        return StreamChunk(text=text, is_final=is_final)

    def collect(self) -> str:
        parts = []
        for chunk in self:
            parts.append(chunk.text)
        return ''.join(parts)


# ---------------------------------------------------------------------------
# Embedding simulation
# ---------------------------------------------------------------------------

class EmbeddingResult:
    def __init__(self, vector: List[float], model: str, token_count: int):
        self.vector = vector
        self.model = model
        self.token_count = token_count
        self.dimension = len(vector)

    def similarity(self, other: 'EmbeddingResult') -> float:
        if self.dimension != other.dimension:
            raise ValueError("Dimension mismatch")
        dot = sum(a * b for a, b in zip(self.vector, other.vector))
        mag_a = math.sqrt(sum(a * a for a in self.vector))
        mag_b = math.sqrt(sum(b * b for b in other.vector))
        if mag_a == 0 or mag_b == 0:
            return 0.0
        return dot / (mag_a * mag_b)


class EmbeddingSimulator:
    def __init__(self, dimension: int = 256):
        self._dimension = dimension

    def embed(self, text: str, model: str = "text-embedding-3-small") -> EmbeddingResult:
        seed = hash(text) % (2**32)
        rng = random.Random(seed)
        raw = [rng.gauss(0, 1) for _ in range(self._dimension)]
        magnitude = math.sqrt(sum(x * x for x in raw))
        if magnitude > 0:
            raw = [x / magnitude for x in raw]
        return EmbeddingResult(
            vector=raw,
            model=model,
            token_count=count_tokens(text),
        )

    def embed_batch(self, texts: List[str], model: str = "text-embedding-3-small") -> List[EmbeddingResult]:
        return [self.embed(text, model) for text in texts]


# ---------------------------------------------------------------------------
# Token budget planner
# ---------------------------------------------------------------------------

class TokenBudgetPlanner:
    def __init__(self, model: ModelConfig):
        self._model = model
        self._reserved_output = 0
        self._reserved_system = 0

    def reserve_output(self, tokens: int):
        self._reserved_output = tokens

    def reserve_system(self, tokens: int):
        self._reserved_system = tokens

    def available_for_prompt(self) -> int:
        effective = int(self._model.context_limit * 0.95)
        return max(0, effective - self._reserved_output - self._reserved_system)

    def plan(self, prompt: str, system_prompt: Optional[str] = None) -> Dict[str, Any]:
        prompt_tokens = count_tokens(prompt)
        system_tokens = count_tokens(system_prompt) if system_prompt else 0
        total_input = prompt_tokens + system_tokens
        available_output = int(self._model.context_limit * 0.95) - total_input
        fits = total_input <= self.available_for_prompt() + self._reserved_system
        return {
            "model": self._model.name,
            "context_limit": self._model.context_limit,
            "prompt_tokens": prompt_tokens,
            "system_tokens": system_tokens,
            "total_input_tokens": total_input,
            "available_output_tokens": max(0, available_output),
            "utilization": total_input / self._model.context_limit,
            "fits": fits,
        }


# ---------------------------------------------------------------------------
# Conversation summarizer
# ---------------------------------------------------------------------------

class ConversationSummarizer:
    def __init__(self, client: Optional[LLMClient] = None):
        self._client = client

    def summarize_by_truncation(
        self,
        conversation: Conversation,
        max_tokens: int,
    ) -> Conversation:
        new_conv = Conversation()
        messages = conversation.messages
        system_msgs = [m for m in messages if m.role == MessageRole.SYSTEM]
        other_msgs = [m for m in messages if m.role != MessageRole.SYSTEM]
        for msg in system_msgs:
            new_conv._messages.append(msg)
        budget = max_tokens - sum(m.token_count() for m in system_msgs)
        included = []
        for msg in reversed(other_msgs):
            tc = msg.token_count()
            if budget >= tc:
                included.insert(0, msg)
                budget -= tc
            else:
                break
        new_conv._messages.extend(included)
        return new_conv

    def extract_key_points(self, conversation: Conversation) -> List[str]:
        points = []
        for msg in conversation.messages:
            if msg.role == MessageRole.ASSISTANT:
                sentences = re.split(r'[.!?]+', msg.content)
                for sent in sentences[:2]:
                    sent = sent.strip()
                    if len(sent) > 20:
                        points.append(sent)
        return points


# ---------------------------------------------------------------------------
# Request/response logging with rotation
# ---------------------------------------------------------------------------

class RotatingLog:
    def __init__(self, max_entries: int = 1000):
        self._entries: List[Dict[str, Any]] = []
        self._max = max_entries
        self._lock = threading.Lock()

    def append(self, entry: Dict[str, Any]):
        with self._lock:
            self._entries.append(entry)
            if len(self._entries) > self._max:
                self._entries = self._entries[-self._max:]

    def get_recent(self, n: int = 10) -> List[Dict[str, Any]]:
        with self._lock:
            return list(self._entries[-n:])

    def search(self, predicate: Callable[[Dict], bool]) -> List[Dict[str, Any]]:
        with self._lock:
            return [e for e in self._entries if predicate(e)]

    def clear(self):
        with self._lock:
            self._entries.clear()

    def __len__(self) -> int:
        return len(self._entries)


# ---------------------------------------------------------------------------
# Model performance tracker
# ---------------------------------------------------------------------------

class ModelPerformanceTracker:
    def __init__(self):
        self._records: Dict[str, List[Dict[str, Any]]] = {}
        self._lock = threading.Lock()

    def record(
        self,
        model_name: str,
        latency_ms: float,
        input_tokens: int,
        output_tokens: int,
        success: bool,
    ):
        with self._lock:
            if model_name not in self._records:
                self._records[model_name] = []
            self._records[model_name].append({
                "timestamp": time.time(),
                "latency_ms": latency_ms,
                "input_tokens": input_tokens,
                "output_tokens": output_tokens,
                "success": success,
            })

    def average_latency(self, model_name: str) -> float:
        with self._lock:
            records = self._records.get(model_name, [])
            if not records:
                return 0.0
            return sum(r["latency_ms"] for r in records) / len(records)

    def success_rate(self, model_name: str) -> float:
        with self._lock:
            records = self._records.get(model_name, [])
            if not records:
                return 1.0
            successes = sum(1 for r in records if r["success"])
            return successes / len(records)

    def throughput(self, model_name: str) -> float:
        with self._lock:
            records = self._records.get(model_name, [])
            if len(records) < 2:
                return 0.0
            total_tokens = sum(r["output_tokens"] for r in records)
            time_span = records[-1]["timestamp"] - records[0]["timestamp"]
            if time_span == 0:
                return 0.0
            return total_tokens / time_span

    def summary(self, model_name: str) -> Dict[str, Any]:
        return {
            "model": model_name,
            "average_latency_ms": self.average_latency(model_name),
            "success_rate": self.success_rate(model_name),
            "throughput_tokens_per_sec": self.throughput(model_name),
            "total_requests": len(self._records.get(model_name, [])),
        }


# ---------------------------------------------------------------------------
# Configuration serialization
# ---------------------------------------------------------------------------

class ConfigSerializer:
    @staticmethod
    def to_dict(config: ClientConfig) -> Dict[str, Any]:
        return {
            "default_strength": config.default_strength,
            "default_temperature": config.default_temperature,
            "default_max_tokens": config.default_max_tokens,
            "retry": {
                "max_retries": config.retry_config.max_retries,
                "base_delay": config.retry_config.base_delay,
                "max_delay": config.retry_config.max_delay,
                "jitter_factor": config.retry_config.jitter_factor,
            },
            "cache_strategy": config.cache_strategy.value,
            "cache_max_size": config.cache_max_size,
            "token_estimation_method": config.token_estimation_method.value,
            "context_safety_margin": config.context_safety_margin,
            "enable_logging": config.enable_logging,
            "rate_limit_tokens_per_second": config.rate_limit_tokens_per_second,
            "rate_limit_burst": config.rate_limit_burst,
        }

    @staticmethod
    def from_dict(data: Dict[str, Any]) -> ClientConfig:
        retry_data = data.get("retry", {})
        retry_config = RetryConfig(
            max_retries=retry_data.get("max_retries", 3),
            base_delay=retry_data.get("base_delay", 1.0),
            max_delay=retry_data.get("max_delay", 60.0),
            jitter_factor=retry_data.get("jitter_factor", 0.1),
        )
        cache_strategy_str = data.get("cache_strategy", "lru")
        cache_strategy = CacheStrategy(cache_strategy_str)
        token_method_str = data.get("token_estimation_method", "hybrid")
        token_method = TokenEstimationMethod(token_method_str)
        return ClientConfig(
            default_strength=data.get("default_strength", 0.5),
            default_temperature=data.get("default_temperature", 0.7),
            default_max_tokens=data.get("default_max_tokens"),
            retry_config=retry_config,
            cache_strategy=cache_strategy,
            cache_max_size=data.get("cache_max_size", 128),
            token_estimation_method=token_method,
            context_safety_margin=data.get("context_safety_margin", 0.05),
            enable_logging=data.get("enable_logging", True),
            rate_limit_tokens_per_second=data.get("rate_limit_tokens_per_second", 10.0),
            rate_limit_burst=data.get("rate_limit_burst", 20),
        )

    @staticmethod
    def to_json(config: ClientConfig) -> str:
        return json.dumps(ConfigSerializer.to_dict(config), indent=2)

    @staticmethod
    def from_json(json_str: str) -> ClientConfig:
        return ConfigSerializer.from_dict(json.loads(json_str))


# ---------------------------------------------------------------------------
# Prompt template library
# ---------------------------------------------------------------------------

class PromptTemplateLibrary:
    def __init__(self):
        self._templates: Dict[str, str] = {}
        self._metadata: Dict[str, Dict[str, Any]] = {}

    def register(self, name: str, template: str, metadata: Optional[Dict] = None):
        self._templates[name] = template
        if metadata:
            self._metadata[name] = metadata

    def get(self, name: str) -> Optional[str]:
        return self._templates.get(name)

    def render(self, name: str, variables: Dict[str, Any]) -> str:
        template = self._templates.get(name)
        if template is None:
            raise InvalidRequestError(f"Template not found: {name}")
        return format_prompt(template, variables)

    def list_templates(self) -> List[str]:
        return list(self._templates.keys())

    def get_metadata(self, name: str) -> Optional[Dict[str, Any]]:
        return self._metadata.get(name)


# ---------------------------------------------------------------------------
# Safety and content filtering
# ---------------------------------------------------------------------------

class SafetyChecker:
    _PII_PATTERNS = [
        (re.compile(r'\b\d{3}-\d{2}-\d{4}\b'), "SSN"),
        (re.compile(r'\b\d{16}\b'), "credit_card"),
        (re.compile(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b'), "email"),
        (re.compile(r'\b\d{3}[-.]?\d{3}[-.]?\d{4}\b'), "phone"),
    ]

    def check_pii(self, text: str) -> List[Dict[str, Any]]:
        findings = []
        for pattern, pii_type in self._PII_PATTERNS:
            matches = pattern.findall(text)
            for match in matches:
                findings.append({
                    "type": pii_type,
                    "value": match[:4] + "****",
                    "count": 1,
                })
        return findings

    def redact_pii(self, text: str) -> str:
        result = text
        for pattern, pii_type in self._PII_PATTERNS:
            result = pattern.sub(f"[REDACTED_{pii_type.upper()}]", result)
        return result

    def estimate_toxicity(self, text: str) -> float:
        toxic_words = {
            "hate", "kill", "attack", "destroy", "stupid",
            "idiot", "terrible", "awful", "disgusting",
        }
        words = set(text.lower().split())
        overlap = words & toxic_words
        if not words:
            return 0.0
        return min(1.0, len(overlap) / 5.0)


# ---------------------------------------------------------------------------
# Multi-turn conversation manager
# ---------------------------------------------------------------------------

class ConversationManager:
    def __init__(self, client: LLMClient, system_prompt: Optional[str] = None):
        self._client = client
        self._conversation = Conversation(system_prompt)
        self._max_history_tokens = 100000

    def send(
        self,
        message: str,
        strength: float = 0.5,
        temperature: float = 0.7,
        output_schema: Optional[Dict] = None,
    ) -> InvocationResult:
        self._conversation.add_user_message(message)
        prompt = self._conversation.to_prompt()
        result = self._client.invoke(
            prompt=prompt,
            strength=strength,
            temperature=temperature,
            output_schema=output_schema,
            bypass_cache=True,
        )
        self._conversation.add_assistant_message(result.result)
        removed = self._conversation.trim_to_fit(self._max_history_tokens)
        if removed > 0:
            logger.info("Trimmed %d messages to fit context", removed)
        return result

    @property
    def conversation(self) -> Conversation:
        return self._conversation

    def reset(self):
        system = None
        for msg in self._conversation.messages:
            if msg.role == MessageRole.SYSTEM:
                system = msg.content
                break
        self._conversation = Conversation(system)


# ---------------------------------------------------------------------------
# Evaluation / scoring helpers
# ---------------------------------------------------------------------------

class ResponseEvaluator:
    def evaluate_completeness(self, response: str, expected_fields: List[str]) -> float:
        response_lower = response.lower()
        found = sum(1 for field in expected_fields if field.lower() in response_lower)
        if not expected_fields:
            return 1.0
        return found / len(expected_fields)

    def evaluate_json_validity(self, response: str) -> float:
        extracted = extract_json(response)
        if extracted is None:
            return 0.0
        try:
            json.loads(extracted)
            return 1.0
        except json.JSONDecodeError:
            repaired = repair_json(extracted)
            try:
                json.loads(repaired)
                return 0.5
            except json.JSONDecodeError:
                return 0.0

    def evaluate_length(self, response: str, min_tokens: int, max_tokens: int) -> float:
        tokens = count_tokens(response)
        if tokens < min_tokens:
            return tokens / min_tokens
        if tokens > max_tokens:
            return max(0, 1.0 - (tokens - max_tokens) / max_tokens)
        return 1.0

    def composite_score(
        self,
        response: str,
        expected_fields: Optional[List[str]] = None,
        min_tokens: int = 10,
        max_tokens: int = 1000,
        weights: Optional[Dict[str, float]] = None,
    ) -> float:
        if weights is None:
            weights = {"completeness": 0.4, "json_validity": 0.3, "length": 0.3}
        scores = {}
        if expected_fields:
            scores["completeness"] = self.evaluate_completeness(response, expected_fields)
        else:
            scores["completeness"] = 1.0
        scores["json_validity"] = self.evaluate_json_validity(response)
        scores["length"] = self.evaluate_length(response, min_tokens, max_tokens)
        total = 0.0
        weight_sum = 0.0
        for key, weight in weights.items():
            if key in scores:
                total += scores[key] * weight
                weight_sum += weight
        if weight_sum == 0:
            return 0.0
        return total / weight_sum


# ---------------------------------------------------------------------------
# Adaptive strength selector
# ---------------------------------------------------------------------------

class AdaptiveStrengthSelector:
    def __init__(self, initial_strength: float = 0.5):
        self._strength = initial_strength
        self._history: List[Tuple[float, bool]] = []
        self._learning_rate = 0.1

    def current_strength(self) -> float:
        return self._strength

    def record_outcome(self, strength: float, success: bool, quality: float = 1.0):
        self._history.append((strength, success))
        if success and quality >= 0.8:
            self._strength = max(0.0, self._strength - self._learning_rate * 0.5)
        elif not success:
            self._strength = min(1.0, self._strength + self._learning_rate)
        self._learning_rate *= 0.99

    def suggest_strength(self, task_difficulty: float = 0.5) -> float:
        base = self._strength
        adjusted = base * 0.6 + task_difficulty * 0.4
        return max(0.0, min(1.0, adjusted))


# ---------------------------------------------------------------------------
# Checksumming and integrity
# ---------------------------------------------------------------------------

class ResponseIntegrity:
    @staticmethod
    def compute_checksum(content: str) -> str:
        return hashlib.sha256(content.encode()).hexdigest()[:16]

    @staticmethod
    def verify_checksum(content: str, expected: str) -> bool:
        return ResponseIntegrity.compute_checksum(content) == expected

    @staticmethod
    def compute_fingerprint(result: InvocationResult) -> str:
        data = f"{result.model_name}:{result.input_tokens}:{result.output_tokens}:{result.result[:100]}"
        return hashlib.md5(data.encode()).hexdigest()


# ---------------------------------------------------------------------------
# Retry strategy variants
# ---------------------------------------------------------------------------

class FixedDelayRetryConfig(RetryConfig):
    def __init__(self, delay: float = 1.0, max_retries: int = 3):
        super().__init__(
            max_retries=max_retries,
            base_delay=delay,
            max_delay=delay,
            jitter_factor=0.0,
        )

    def compute_delay(self, attempt: int) -> float:
        return self.base_delay


class LinearBackoffRetryConfig(RetryConfig):
    def __init__(self, base_delay: float = 1.0, increment: float = 1.0, max_retries: int = 3):
        super().__init__(
            max_retries=max_retries,
            base_delay=base_delay,
            max_delay=base_delay + increment * max_retries,
        )
        self._increment = increment

    def compute_delay(self, attempt: int) -> float:
        return self.base_delay + self._increment * attempt


class DecorrelatedJitterRetryConfig(RetryConfig):
    def __init__(self, base_delay: float = 1.0, max_delay: float = 60.0, max_retries: int = 3):
        super().__init__(
            max_retries=max_retries,
            base_delay=base_delay,
            max_delay=max_delay,
        )
        self._last_delay = base_delay

    def compute_delay(self, attempt: int) -> float:
        self._last_delay = min(
            self.max_delay,
            random.uniform(self.base_delay, self._last_delay * 3),
        )
        return self._last_delay


# ---------------------------------------------------------------------------
# Prompt chain / pipeline
# ---------------------------------------------------------------------------

@dataclass
class ChainStep:
    name: str
    prompt_template: str
    strength: float = 0.5
    temperature: float = 0.7
    output_schema: Optional[Dict] = None
    post_processor: Optional[ResponsePostProcessor] = None
    transform_output: Optional[Callable[[str], Dict[str, Any]]] = None


class PromptChain:
    def __init__(self, client: LLMClient):
        self._client = client
        self._steps: List[ChainStep] = []

    def add_step(self, step: ChainStep):
        self._steps.append(step)
        return self

    def execute(self, initial_variables: Dict[str, Any]) -> List[InvocationResult]:
        results = []
        variables = dict(initial_variables)
        for step in self._steps:
            prompt = format_prompt(step.prompt_template, variables)
            result = self._client.invoke(
                prompt=prompt,
                strength=step.strength,
                temperature=step.temperature,
                output_schema=step.output_schema,
            )
            output = result.result
            if step.post_processor:
                output = step.post_processor.process(output)
            if step.transform_output:
                new_vars = step.transform_output(output)
                variables.update(new_vars)
            else:
                variables[step.name + "_output"] = output
            results.append(result)
        return results

    def estimate_total_cost(self, initial_variables: Dict[str, Any]) -> float:
        cost_calc = CostCalculator(self._client.models)
        total = 0.0
        variables = dict(initial_variables)
        for step in self._steps:
            prompt = format_prompt(step.prompt_template, variables)
            model = select_model(self._client.models, step.strength)
            total += cost_calc.estimate_cost(prompt, model)
            variables[step.name + "_output"] = "[estimated]"
        return total


# ---------------------------------------------------------------------------
# Helpers: text utilities used throughout
# ---------------------------------------------------------------------------

def truncate_text(text: str, max_length: int, suffix: str = "...") -> str:
    if len(text) <= max_length:
        return text
    return text[:max_length - len(suffix)] + suffix


def sanitize_for_json(text: str) -> str:
    text = text.replace('\\', '\\\\')
    text = text.replace('"', '\\"')
    text = text.replace('\n', '\\n')
    text = text.replace('\r', '\\r')
    text = text.replace('\t', '\\t')
    return text


def merge_dicts_deep(base: Dict, override: Dict) -> Dict:
    result = dict(base)
    for key, value in override.items():
        if key in result and isinstance(result[key], dict) and isinstance(value, dict):
            result[key] = merge_dicts_deep(result[key], value)
        else:
            result[key] = value
    return result


def stable_hash(data: Any) -> str:
    serialized = json.dumps(data, sort_keys=True, default=str)
    return hashlib.sha256(serialized.encode()).hexdigest()


def chunk_text(text: str, max_tokens: int) -> List[str]:
    words = text.split()
    chunks = []
    current_chunk: List[str] = []
    current_count = 0
    for word in words:
        word_tokens = max(1, len(word) // 4)
        if current_count + word_tokens > max_tokens and current_chunk:
            chunks.append(' '.join(current_chunk))
            current_chunk = []
            current_count = 0
        current_chunk.append(word)
        current_count += word_tokens
    if current_chunk:
        chunks.append(' '.join(current_chunk))
    return chunks


def estimate_cost_for_text(text: str, model: ModelConfig, output_ratio: float = 1.0) -> float:
    input_tokens = count_tokens(text)
    output_tokens = int(input_tokens * output_ratio)
    return calculate_cost(input_tokens, output_tokens, model)


# ---------------------------------------------------------------------------
# Structured output builder
# ---------------------------------------------------------------------------

class SchemaBuilder:
    def __init__(self):
        self._schema: Dict[str, Any] = {"type": "object", "properties": {}, "required": []}

    def add_string(self, name: str, required: bool = True, description: str = "", enum: Optional[List[str]] = None):
        prop: Dict[str, Any] = {"type": "string"}
        if description:
            prop["description"] = description
        if enum:
            prop["enum"] = enum
        self._schema["properties"][name] = prop
        if required:
            self._schema["required"].append(name)
        return self

    def add_number(self, name: str, required: bool = True, minimum: Optional[float] = None, maximum: Optional[float] = None):
        prop: Dict[str, Any] = {"type": "number"}
        if minimum is not None:
            prop["minimum"] = minimum
        if maximum is not None:
            prop["maximum"] = maximum
        self._schema["properties"][name] = prop
        if required:
            self._schema["required"].append(name)
        return self

    def add_integer(self, name: str, required: bool = True, minimum: Optional[int] = None, maximum: Optional[int] = None):
        prop: Dict[str, Any] = {"type": "integer"}
        if minimum is not None:
            prop["minimum"] = minimum
        if maximum is not None:
            prop["maximum"] = maximum
        self._schema["properties"][name] = prop
        if required:
            self._schema["required"].append(name)
        return self

    def add_boolean(self, name: str, required: bool = True):
        self._schema["properties"][name] = {"type": "boolean"}
        if required:
            self._schema["required"].append(name)
        return self

    def add_array(self, name: str, items_schema: Dict[str, Any], required: bool = True):
        self._schema["properties"][name] = {"type": "array", "items": items_schema}
        if required:
            self._schema["required"].append(name)
        return self

    def add_object(self, name: str, properties: Dict[str, Dict], required: bool = True):
        self._schema["properties"][name] = {"type": "object", "properties": properties}
        if required:
            self._schema["required"].append(name)
        return self

    def build(self) -> Dict[str, Any]:
        return copy.deepcopy(self._schema)


# ---------------------------------------------------------------------------
# Model capability matrix
# ---------------------------------------------------------------------------

class CapabilityMatrix:
    def __init__(self, models: List[ModelConfig]):
        self._models = models

    def supports_feature(self, model_name: str, feature: str) -> bool:
        model = self._find_model(model_name)
        if model is None:
            return False
        feature_map = {
            "structured_output": model.supports_structured_output,
            "reasoning": model.is_reasoning_model,
            "large_context": model.context_limit >= 200000,
            "extended_thinking": model.reasoning_type == ReasoningType.EXTENDED_THINKING,
            "chain_of_thought": model.reasoning_type == ReasoningType.CHAIN_OF_THOUGHT,
            "million_context": model.context_limit >= 1000000,
        }
        return feature_map.get(feature, False)

    def models_with_feature(self, feature: str) -> List[ModelConfig]:
        return [m for m in self._models if self.supports_feature(m.name, feature)]

    def feature_matrix(self) -> Dict[str, Dict[str, bool]]:
        features = [
            "structured_output", "reasoning", "large_context",
            "extended_thinking", "chain_of_thought", "million_context",
        ]
        matrix = {}
        for model in self._models:
            matrix[model.name] = {
                f: self.supports_feature(model.name, f) for f in features
            }
        return matrix

    def _find_model(self, name: str) -> Optional[ModelConfig]:
        for m in self._models:
            if m.name == name:
                return m
        return None


# ---------------------------------------------------------------------------
# Provider health tracker
# ---------------------------------------------------------------------------

class ProviderHealthTracker:
    def __init__(self):
        self._health: Dict[str, List[bool]] = {}
        self._window_size = 100
        self._lock = threading.Lock()

    def record(self, provider: Provider, success: bool):
        with self._lock:
            key = provider.value
            if key not in self._health:
                self._health[key] = []
            self._health[key].append(success)
            if len(self._health[key]) > self._window_size:
                self._health[key] = self._health[key][-self._window_size:]

    def health_score(self, provider: Provider) -> float:
        with self._lock:
            key = provider.value
            records = self._health.get(key, [])
            if not records:
                return 1.0
            return sum(1 for r in records if r) / len(records)

    def is_healthy(self, provider: Provider, threshold: float = 0.5) -> bool:
        return self.health_score(provider) >= threshold

    def all_health(self) -> Dict[str, float]:
        return {p.value: self.health_score(p) for p in Provider}


# ---------------------------------------------------------------------------
# Utilities for working with model configs
# ---------------------------------------------------------------------------

def filter_models(
    models: List[ModelConfig],
    provider: Optional[Provider] = None,
    min_elo: Optional[int] = None,
    max_cost: Optional[float] = None,
    supports_structured: Optional[bool] = None,
    reasoning_only: bool = False,
    min_context: Optional[int] = None,
) -> List[ModelConfig]:
    result = list(models)
    if provider is not None:
        result = [m for m in result if m.provider == provider]
    if min_elo is not None:
        result = [m for m in result if m.elo >= min_elo]
    if max_cost is not None:
        result = [m for m in result if m.effective_cost <= max_cost]
    if supports_structured is not None:
        result = [m for m in result if m.supports_structured_output == supports_structured]
    if reasoning_only:
        result = [m for m in result if m.is_reasoning_model]
    if min_context is not None:
        result = [m for m in result if m.context_limit >= min_context]
    return result


def cheapest_model(models: List[ModelConfig]) -> Optional[ModelConfig]:
    if not models:
        return None
    return min(models, key=lambda m: m.effective_cost)


def best_model(models: List[ModelConfig]) -> Optional[ModelConfig]:
    if not models:
        return None
    return max(models, key=lambda m: m.elo)


def model_by_name(models: List[ModelConfig], name: str) -> Optional[ModelConfig]:
    for m in models:
        if m.name == name:
            return m
    return None


# ---------------------------------------------------------------------------
# Cost reporting
# ---------------------------------------------------------------------------

class CostReport:
    def __init__(self, usage_tracker: UsageTracker):
        self._tracker = usage_tracker

    def generate(self) -> Dict[str, Any]:
        summary = self._tracker.summary()
        per_model = summary.get("per_model", {})
        sorted_by_cost = sorted(
            per_model.items(),
            key=lambda x: x[1]["cost"],
            reverse=True,
        )
        return {
            "total_cost": summary["total_cost"],
            "total_input_tokens": summary["total_input_tokens"],
            "total_output_tokens": summary["total_output_tokens"],
            "invocation_count": summary["invocation_count"],
            "average_cost_per_invocation": (
                summary["total_cost"] / summary["invocation_count"]
                if summary["invocation_count"] > 0 else 0.0
            ),
            "by_model": [
                {
                    "model": name,
                    "cost": data["cost"],
                    "count": data["count"],
                    "input_tokens": data["input"],
                    "output_tokens": data["output"],
                }
                for name, data in sorted_by_cost
            ],
        }

    def format_text(self) -> str:
        report = self.generate()
        lines = [
            "Cost Report",
            "=" * 40,
            f"Total Cost: ${report['total_cost']:.6f}",
            f"Invocations: {report['invocation_count']}",
            f"Avg Cost/Invocation: ${report['average_cost_per_invocation']:.6f}",
            f"Total Tokens: {report['total_input_tokens']} in / {report['total_output_tokens']} out",
            "",
            "By Model:",
            "-" * 40,
        ]
        for entry in report["by_model"]:
            lines.append(
                f"  {entry['model']}: ${entry['cost']:.6f} ({entry['count']} calls)"
            )
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Multi-provider failover client
# ---------------------------------------------------------------------------

class FailoverClient:
    def __init__(
        self,
        client: LLMClient,
        provider_priority: Optional[List[Provider]] = None,
    ):
        self._client = client
        self._priority = provider_priority or [Provider.ANTHROPIC, Provider.OPENAI, Provider.GOOGLE]
        self._health = ProviderHealthTracker()

    def invoke(
        self,
        prompt: str,
        strength: float = 0.5,
        temperature: float = 0.7,
        output_schema: Optional[Dict] = None,
    ) -> InvocationResult:
        errors = []
        for provider in self._priority:
            if not self._health.is_healthy(provider, threshold=0.3):
                continue
            try:
                result = self._client.invoke(
                    prompt=prompt,
                    strength=strength,
                    temperature=temperature,
                    output_schema=output_schema,
                )
                self._health.record(provider, True)
                return result
            except LLMClientError as e:
                self._health.record(provider, False)
                errors.append((provider.value, str(e)))
        raise LLMClientError(
            f"All providers failed: {'; '.join(f'{p}: {e}' for p, e in errors)}"
        )
