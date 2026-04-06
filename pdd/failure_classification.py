"""
Classify pytest/verification output for failure-aware retry strategies in pdd fix.

Used by fix_error_loop to avoid burning LLM budget on repeated fixes that are
unlikely to help (unchanged syntax/import errors, timeout/flaky patterns).
"""

from __future__ import annotations

import re
from enum import Enum


class FailureKind(str, Enum):
    SYNTAX_IMPORT = "syntax_import"
    ASSERTION_LOGIC = "assertion_logic"
    TIMEOUT_FLAKY = "timeout_flaky"


# Match before generic errors so timeouts are not misclassified.
_RE_TIMEOUT = re.compile(
    r"(timed out after|pytest-timeout|\+\+\+ timeout \+\+\+|timeout \(>|"
    r"deadline exceeded|test.*timed out|failed: timeout)",
    re.IGNORECASE,
)

_RE_SYNTAX_IMPORT = re.compile(
    r"(SyntaxError|IndentationError|TabError|ImportError|ModuleNotFoundError|"
    r"ImportError while loading|ERROR collecting|No module named)",
    re.MULTILINE,
)


def classify_failure(text: str) -> FailureKind:
    """
    Heuristic classification of combined pytest/verification stderr+stdout.

    Order: timeout/flaky → syntax/import → default assertion/logic.
    """
    if not text or not text.strip():
        return FailureKind.ASSERTION_LOGIC
    lower = text.lower()
    if _RE_TIMEOUT.search(lower):
        return FailureKind.TIMEOUT_FLAKY
    if _RE_SYNTAX_IMPORT.search(text):
        return FailureKind.SYNTAX_IMPORT
    return FailureKind.ASSERTION_LOGIC


_FILE_LINE = re.compile(r'File "([^"]+)", line (\d+)', re.MULTILINE)
_EXC_LINE = re.compile(
    r"^[\s]*(?:E\s+)?([\w]+(?:Error|Exception)):\s*",
    re.MULTILINE,
)


def extract_failure_signature(text: str) -> str:
    """
    Coarse signature for 'same failure' detection: exception + first file:line.

    Empty string if nothing usable is found.
    """
    if not text:
        return ""
    fm = _FILE_LINE.search(text)
    em = _EXC_LINE.search(text)
    exc = em.group(1) if em else ""
    if fm:
        path, line = fm.group(1), fm.group(2)
        if exc:
            return f"{exc}:{path}:{line}"
        return f"{path}:{line}"
    if exc:
        return exc
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
