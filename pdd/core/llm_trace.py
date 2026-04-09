from __future__ import annotations

import json
import re
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, asdict
from typing import Any, Dict, Iterator, Optional


@dataclass
class LLMTracePair:
    prompt: str
    response: str
    model: str = "unknown"


_current_operation: ContextVar[Optional[str]] = ContextVar("pdd_current_operation", default=None)
_last_pair_by_operation: ContextVar[Dict[str, LLMTracePair]] = ContextVar(
    "pdd_llm_last_pair_by_operation", default={}
)


_SENSITIVE_PATTERNS = [
    # Common bearer tokens / API keys
    re.compile(r"(?i)\b(bearer)\s+[a-z0-9\-_\.=:+/]{10,}"),
    re.compile(r"(?i)\b(api[_-]?key|token|secret|password)\b\s*[:=]\s*[^\s\"']{6,}"),
]


def set_current_operation(operation: Optional[str]) -> None:
    _current_operation.set(operation)


@contextmanager
def operation_scope(operation: str) -> Iterator[None]:
    token = _current_operation.set(operation)
    try:
        yield
    finally:
        _current_operation.reset(token)


def _truncate(text: str, limit_chars: int) -> str:
    if text is None:
        return ""
    if len(text) <= limit_chars:
        return text
    return text[:limit_chars] + f"\n... (truncated, {len(text)} total chars)"


def _redact(text: str) -> str:
    if not text:
        return text
    redacted = text
    for pat in _SENSITIVE_PATTERNS:
        redacted = pat.sub("<redacted>", redacted)
    return redacted


def record_llm_pair(
    *,
    prompt: Any,
    response: Any,
    model: str = "unknown",
    prompt_limit_chars: int = 20_000,
    response_limit_chars: int = 20_000,
) -> None:
    """
    Record the most recent (prompt, raw_response) pair for the current operation.
    Intended to be called by llm_invoke.
    """
    op = _current_operation.get()
    if not op:
        return

    try:
        prompt_text = prompt if isinstance(prompt, str) else json.dumps(prompt, ensure_ascii=False, default=str)
    except Exception:
        prompt_text = str(prompt)

    try:
        response_text = response if isinstance(response, str) else json.dumps(response, ensure_ascii=False, default=str)
    except Exception:
        response_text = str(response)

    pair = LLMTracePair(
        prompt=_truncate(_redact(prompt_text), prompt_limit_chars),
        response=_truncate(_redact(response_text), response_limit_chars),
        model=str(model or "unknown"),
    )

    current = dict(_last_pair_by_operation.get() or {})
    current[op] = pair
    _last_pair_by_operation.set(current)


def pop_last_pair(operation: str) -> Optional[Dict[str, Any]]:
    """Pop and return the last recorded pair for an operation (as a dict)."""
    current = dict(_last_pair_by_operation.get() or {})
    pair = current.pop(operation, None)
    _last_pair_by_operation.set(current)
    return asdict(pair) if pair else None

