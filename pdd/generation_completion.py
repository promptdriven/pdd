"""Deterministic completion checks for provider-finished generations."""

import ast
import json
import re
import textwrap
import warnings
from typing import Any, Tuple


COMPLETED_FINISH_REASONS = {
    "stop",
    "end_turn",
    "complete",
    "completed",
    "finished",
}

_FENCED_CODE_BLOCK_RE = re.compile(
    r"^\s*```[^\n`]*\n(?P<body>.*?)(?:\n)?```\s*$",
    re.DOTALL,
)


def completion_check_tail(text: str, max_chars: int = 600) -> str:
    """Return a tail slice that starts on a line boundary when possible."""
    if len(text) <= max_chars:
        return text

    start = len(text) - max_chars
    newline_index = text.find("\n", start)
    if newline_index != -1 and newline_index + 1 < len(text):
        return text[newline_index + 1:]
    return text[start:]


def provider_reports_completion(finish_reason: Any) -> bool:
    """Return True when provider metadata says generation ended normally."""
    if isinstance(finish_reason, (list, tuple)):
        return bool(finish_reason) and all(
            provider_reports_completion(item) for item in finish_reason
        )
    if finish_reason is None:
        return False

    normalized = str(finish_reason).strip().lower().replace("-", "_").replace(" ", "_")
    return normalized in COMPLETED_FINISH_REASONS


def provider_finished_structurally(
    output: Any,
    finish_reason: Any,
    language: str,
) -> bool:
    """Return True when provider and local structural signals both indicate completion."""
    if not provider_reports_completion(finish_reason):
        return False
    if not isinstance(output, str):
        return True

    return output_is_structurally_complete(output, language)


def output_is_structurally_complete(output: str, language: str) -> bool:
    """Return True when output has a complete structure for the target language."""
    body, has_closed_fence = strip_outer_code_fence(output)
    normalized_language = (language or "").strip().lower()

    if normalized_language == "python":
        return python_code_parses(body)
    if normalized_language == "json":
        return json_parses(body)
    return has_closed_fence


def strip_outer_code_fence(output: str) -> Tuple[str, bool]:
    """Strip a single outer Markdown code fence and report whether it was closed."""
    match = _FENCED_CODE_BLOCK_RE.match(output)
    if not match:
        return output, False
    return match.group("body"), True


def python_code_parses(code: str) -> bool:
    """Return True when Python code parses at module scope."""
    if not code.strip():
        return False

    dedented = textwrap.dedent(code)
    candidates = [code, dedented]
    for candidate in candidates:
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", SyntaxWarning)
                ast.parse(candidate)
            return True
        except SyntaxError:
            continue
    return False


def json_parses(text: str) -> bool:
    """Return True when text is valid JSON."""
    try:
        json.loads(text)
        return True
    except (TypeError, ValueError):
        return False
