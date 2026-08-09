"""Tolerant parser for agent-CLI session/rollout logs (design.md §6.2 tap 1).

The recording proxy is the primary source; the CLI's own session log (for
Codex, JSONL rollout files under ``CODEX_HOME/sessions``) is a redundant
cross-check. The parser is deliberately schema-tolerant: it extracts what it
recognizes (token usage, tool calls, request-ish events) and records what it
does not, so schema drift in a pinned CLI version surfaces as data instead of
a crash.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable


@dataclass
class SessionSummary:
    path: str
    line_count: int = 0
    parsed_lines: int = 0
    malformed_lines: int = 0
    tool_call_names: list[str] = field(default_factory=list)
    token_events: list[dict[str, int | None]] = field(default_factory=list)
    event_types: dict[str, int] = field(default_factory=dict)
    unknown_event_types: list[str] = field(default_factory=list)

    @property
    def cumulative_input_tokens(self) -> int | None:
        values = [e["input_tokens"] for e in self.token_events if e["input_tokens"]]
        return sum(values) if values else None

    @property
    def request_count_estimate(self) -> int:
        return len(self.token_events)


_USAGE_KEYS = ("usage", "token_usage", "total_token_usage", "last_token_usage")
_INPUT_KEYS = ("input_tokens", "prompt_tokens", "input", "cached_input_tokens")
_OUTPUT_KEYS = ("output_tokens", "completion_tokens", "output")


def _find_usage(obj: Any, depth: int = 0) -> dict[str, int | None] | None:
    """Recursively locate a usage-like dict and normalize it."""
    if depth > 6 or not isinstance(obj, dict):
        return None
    for key in _USAGE_KEYS:
        candidate = obj.get(key)
        if isinstance(candidate, dict):
            input_tokens = next(
                (candidate[k] for k in _INPUT_KEYS if isinstance(candidate.get(k), int)),
                None,
            )
            output_tokens = next(
                (candidate[k] for k in _OUTPUT_KEYS if isinstance(candidate.get(k), int)),
                None,
            )
            if input_tokens is not None or output_tokens is not None:
                return {"input_tokens": input_tokens, "output_tokens": output_tokens}
    for value in obj.values():
        found = _find_usage(value, depth + 1)
        if found is not None:
            return found
    return None


def _find_tool_calls(obj: Any, depth: int = 0) -> Iterable[str]:
    """Recursively collect tool/function-call names."""
    if depth > 6:
        return
    if isinstance(obj, dict):
        obj_type = str(obj.get("type", ""))
        if obj_type.endswith("_call") or obj_type in ("tool_call", "function_call"):
            name = obj.get("name") or (obj.get("function") or {}).get("name")
            yield str(name) if name else obj_type
        for value in obj.values():
            yield from _find_tool_calls(value, depth + 1)
    elif isinstance(obj, list):
        for item in obj:
            yield from _find_tool_calls(item, depth + 1)


_KNOWN_TYPE_HINTS = (
    "message",
    "response",
    "request",
    "tool",
    "function",
    "token",
    "usage",
    "turn",
    "session",
    "event",
    "shell",
    "patch",
    "reasoning",
)


def parse_session_log(path: str | Path) -> SessionSummary:
    """Parse one JSONL session/rollout file into a summary."""
    path = Path(path)
    summary = SessionSummary(path=str(path))
    with path.open("r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            summary.line_count += 1
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                summary.malformed_lines += 1
                continue
            summary.parsed_lines += 1
            if not isinstance(event, dict):
                continue
            event_type = str(
                event.get("type") or (event.get("payload") or {}).get("type") or "untyped"
            )
            summary.event_types[event_type] = summary.event_types.get(event_type, 0) + 1
            if not any(hint in event_type.lower() for hint in _KNOWN_TYPE_HINTS):
                if event_type not in summary.unknown_event_types:
                    summary.unknown_event_types.append(event_type)
            usage = _find_usage(event)
            if usage is not None:
                summary.token_events.append(usage)
            for name in _find_tool_calls(event):
                summary.tool_call_names.append(name)
    return summary


def reconcile(
    proxy_input_tokens_total: int | None,
    proxy_request_count: int,
    session: SessionSummary,
    token_tolerance: float = 0.05,
) -> list[str]:
    """Compare proxy record against the CLI's own session log.

    Returns a list of human-readable discrepancies (empty = consistent).
    Disagreement flags the run per design §6.2 — it does not auto-void it.
    """
    problems: list[str] = []
    if session.malformed_lines:
        problems.append(
            f"session log has {session.malformed_lines} malformed lines"
        )
    session_tokens = session.cumulative_input_tokens
    if proxy_input_tokens_total is not None and session_tokens is not None:
        if proxy_input_tokens_total > 0:
            drift = abs(session_tokens - proxy_input_tokens_total) / proxy_input_tokens_total
            if drift > token_tolerance:
                problems.append(
                    "input-token mismatch: proxy="
                    f"{proxy_input_tokens_total} session={session_tokens} "
                    f"(drift {drift:.1%} > {token_tolerance:.0%})"
                )
    if session.request_count_estimate and proxy_request_count:
        if session.request_count_estimate > proxy_request_count:
            problems.append(
                "session log reports more usage events "
                f"({session.request_count_estimate}) than proxied requests "
                f"({proxy_request_count}) — traffic may have bypassed the proxy"
            )
    return problems
