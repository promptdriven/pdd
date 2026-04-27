from __future__ import annotations

import json
import re
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, asdict
from typing import Any, Dict, Iterator, List, Optional


@dataclass
class LLMTracePair:
    prompt: str
    response: str
    model: str = "unknown"
    thinking: Optional[str] = None


_current_operation: ContextVar[Optional[str]] = ContextVar("pdd_current_operation", default=None)
_pairs_by_operation: ContextVar[Dict[str, List[LLMTracePair]]] = ContextVar(
    "pdd_llm_pairs_by_operation", default={}
)


_SENSITIVE_PATTERNS = [
    # Common bearer tokens / API keys
    re.compile(r"(?i)\b(bearer)\s+[a-z0-9\-_\.=:+/]{10,}"),
    re.compile(r"(?i)\b(api[_-]?key|token|secret|password)\b\s*[:=]\s*[^\s\"']{6,}"),
    # JSON-style quoted values: "api_key": "sk-..." or "token": "eyJ..."
    re.compile(r'(?i)"(api[_-]?key|token|secret|password)"\s*:\s*"([^"]{6,})"'),
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


def _normalize_thinking(thinking: Any) -> Optional[str]:
    """Normalize thinking to a string or None.

    Some providers return thinking as a string. Others return it as a list
    of objects (e.g., [{"type": "thinking", "thinking": "..."}]). Normalize
    to a single string before storing.
    """
    if thinking is None:
        return None
    if isinstance(thinking, str):
        return thinking
    if isinstance(thinking, list):
        parts = []
        for item in thinking:
            if isinstance(item, dict):
                # Extract text content from dict items
                text = item.get("thinking") or item.get("text") or item.get("content") or ""
                if text:
                    parts.append(str(text))
            else:
                parts.append(str(item))
        return "\n".join(parts)
    return str(thinking)


def record_llm_pair(
    *,
    prompt: Any,
    response: Any,
    model: str = "unknown",
    thinking: Any = None,
    prompt_limit_chars: int = 20_000,
    response_limit_chars: int = 20_000,
    thinking_limit_chars: int = 20_000,
) -> None:
    """
    Record a (prompt, raw_response) pair for the current operation.
    Intended to be called by llm_invoke. All pairs are accumulated in a list.
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

    thinking_text = _normalize_thinking(thinking)

    pair = LLMTracePair(
        prompt=_truncate(_redact(prompt_text), prompt_limit_chars),
        response=_truncate(_redact(response_text), response_limit_chars),
        model=str(model or "unknown"),
        thinking=_truncate(_redact(thinking_text), thinking_limit_chars) if thinking_text is not None else None,
    )

    current = dict(_pairs_by_operation.get() or {})
    pairs_list = list(current.get(op, []))
    pairs_list.append(pair)
    current[op] = pairs_list
    _pairs_by_operation.set(current)


def pop_all_pairs(operation: str) -> List[Dict[str, Any]]:
    """Pop and return all recorded pairs for an operation (as a list of dicts)."""
    current = dict(_pairs_by_operation.get() or {})
    pairs = current.pop(operation, [])
    _pairs_by_operation.set(current)
    return [asdict(p) for p in pairs]


# Backwards compatibility alias
def pop_last_pair(operation: str) -> Optional[Dict[str, Any]]:
    """Pop and return the last recorded pair for an operation (as a dict).

    Deprecated: use pop_all_pairs() instead. Kept for callers that only
    need the most recent pair.
    """
    all_pairs = pop_all_pairs(operation)
    return all_pairs[-1] if all_pairs else None
