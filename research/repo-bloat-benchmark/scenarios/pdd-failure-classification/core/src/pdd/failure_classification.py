"""Classify pytest/verification output for failure-aware retry strategies.

Dependency-sliced from ``pdd/failure_classification.py`` (upstream pinned
commit in ``scenario.json``); identifiers and comments were normalized during
slicing — see ``seed.patch`` for the recorded transform.
"""

from __future__ import annotations

import re
from enum import Enum


class FailureKind(str, Enum):
    SYNTAX_IMPORT = "syntax_import"
    ASSERTION_LOGIC = "assertion_logic"
    TIMEOUT_FLAKY = "timeout_flaky"
    BUDGET_TRUNCATED = "budget_truncated"
    INFRASTRUCTURE_ERROR = "infrastructure_error"


_TIMEOUT_PATTERN = re.compile(
    r"(timed out after|pytest-timeout|\+\+\+ timeout \+\+\+|timeout \(>|"
    r"deadline exceeded|test.*timed out|failed: timeout)",
    re.IGNORECASE,
)

_SYNTAX_IMPORT_PATTERN = re.compile(
    r"(SyntaxError|IndentationError|TabError|ImportError|ModuleNotFoundError|"
    r"ImportError while loading|ERROR collecting|No module named)",
    re.MULTILINE,
)


def classify_failure(text: str) -> FailureKind:
    """Heuristic classification of combined pytest/verification stderr+stdout."""
    if not text or not text.strip():
        return FailureKind.ASSERTION_LOGIC
    lowered = text.lower()
    if _SYNTAX_IMPORT_PATTERN.search(text):
        return FailureKind.SYNTAX_IMPORT
    if _TIMEOUT_PATTERN.search(lowered):
        return FailureKind.TIMEOUT_FLAKY
    return FailureKind.ASSERTION_LOGIC


_FILE_LINE_PATTERN = re.compile(r'File "([^"]+)", line (\d+)', re.MULTILINE)
_EXCEPTION_PATTERN = re.compile(
    r"^[\s]*(?:E\s+)?([\w]+(?:Error|Exception)):\s*",
    re.MULTILINE,
)


def extract_failure_signature(text: str) -> str:
    """Coarse signature for 'same failure' detection: exception + first file:line.

    Empty string if nothing usable is found.
    """
    if not text:
        return ""
    file_match = _FILE_LINE_PATTERN.search(text)
    exception_match = _EXCEPTION_PATTERN.search(text)
    exception = exception_match.group(1) if exception_match else ""
    if file_match:
        path, line = file_match.group(1), file_match.group(2)
        if exception:
            return f"{exception}:{path}:{line}"
        return f"{path}:{line}"
    if exception:
        return exception
    # Fallback: normalized head (avoid unbounded growth)
    return re.sub(r"\s+", " ", text[:240]).strip()


def failure_classification_hint(kind: FailureKind) -> str:
    """Short guidance for the fix LLM and logs."""
    if kind == FailureKind.SYNTAX_IMPORT:
        return (
            "Failure kind: syntax/import. Prioritize fixing syntax, imports, and "
            "module paths before changing test assertions or business logic."
        )
    if kind == FailureKind.TIMEOUT_FLAKY:
        return (
            "Failure kind: timeout/flaky. Prefer stabilizing the test (timeouts, "
            "isolation, I/O) over large logic rewrites; avoid weakening assertions "
            "unless the prompt clearly allows it."
        )
    if kind == FailureKind.BUDGET_TRUNCATED:
        return "shot stopped — per-shot or total budget exhausted; increase budget limits or reduce per-shot work scope"
    if kind == FailureKind.INFRASTRUCTURE_ERROR:
        return "shot stopped by infrastructure failure (crash, timeout, OOM); check infrastructure health and retry"
    return (
        "Failure kind: assertion/logic. Use the prompt as spec; align code and tests "
        "with expected behavior."
    )


def format_signature_hint(sig: str) -> str:
    """Human-readable location fragment for console messages."""
    if not sig:
        return "(could not locate a stable error position)"
    if len(sig) > 120:
        return sig[:117] + "..."
    return sig
