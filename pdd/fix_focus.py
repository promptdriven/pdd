"""
Focused repair for large dev units in pdd fix.

When the code file exceeds LARGE_CODE_THRESHOLD lines OR the test file exceeds
LARGE_TEST_THRESHOLD lines, this module activates two-phase focused repair:

  Fast-path  : traceback names 1–3 functions → slice only those functions.
  Phase 1    : build a code skeleton (signatures only) + send with error log
               to a lightweight LLM call → DiagnosisResult (broken function names).
  Phase 2    : extract matching function slices, pass to fix_errors_from_unit_tests,
               then reconstruct the full file by splicing bodies back at their
               original line offsets.
  Fallback   : any exception → caller should use full-file path instead.

Public exports:
  DiagnosisResult     – Pydantic model with list of broken function names
  FocusedInputs       – dataclass returned by prepare_focused_inputs()
  is_large()          – True when focused repair threshold is exceeded
  prepare_focused_inputs() – main entry; returns FocusedInputs or None
  reconstruct_code()  – splice fixed slices back into the original file
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Optional

from pydantic import BaseModel, Field

LARGE_CODE_THRESHOLD = 500    # lines in code file
LARGE_TEST_THRESHOLD = 1000   # lines in test file


# ---------------------------------------------------------------------------
# Public data types
# ---------------------------------------------------------------------------

class DiagnosisResult(BaseModel):
    """Structured output from the Phase-1 diagnosis LLM call."""
    function_names: list[str] = Field(
        description=(
            "Names of functions most likely responsible for the test failures, "
            "as they appear in the code skeleton."
        )
    )


@dataclass
class FunctionSlice:
    """One function/method extracted from the source file."""
    name: str
    start_line: int   # 1-indexed, inclusive (first decorator or 'def' line)
    end_line: int     # 1-indexed, inclusive (last line of the function body)
    source: str       # raw source lines for this function (including leading whitespace)


@dataclass
class FocusedInputs:
    """Inputs produced by prepare_focused_inputs() for a focused LLM fix call."""
    focused_code: str           # concatenated source of the matched function slices
    focused_tests: str          # unit-test content (full, for now)
    slices: list[FunctionSlice] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Threshold check
# ---------------------------------------------------------------------------

def _count_lines(text: str) -> int:
    """Return the number of lines in *text*."""
    if not text:
        return 0
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def is_large(code: str, unit_test: str) -> bool:
    """Return True when focused repair should be considered."""
    return (
        _count_lines(code) > LARGE_CODE_THRESHOLD
        or _count_lines(unit_test) > LARGE_TEST_THRESHOLD
    )


# ---------------------------------------------------------------------------
# Skeleton builder  (Phase 1 helper)
# ---------------------------------------------------------------------------

def build_skeleton(code: str) -> str:
    """
    Return *code* with all function / method bodies replaced by ``...``,
    retaining only signatures and top-level docstrings.

    Falls back to returning *code* unchanged if it cannot be parsed.
    """
    try:
        tree = ast.parse(code)
    except SyntaxError:
        return code

    lines = code.splitlines(keepends=True)
    result = list(lines)

    # Collect all function defs; process in reverse line order so replacements
    # do not shift the line numbers of earlier functions.
    func_defs: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_defs.append(node)

    func_defs.sort(key=lambda n: n.lineno, reverse=True)

    for func in func_defs:
        if not func.body:
            continue

        first_stmt = func.body[0]
        # Skip pure-docstring bodies (nothing to replace).
        if (
            isinstance(first_stmt, ast.Expr)
            and isinstance(first_stmt.value, ast.Constant)
            and isinstance(first_stmt.value.value, str)
        ):
            if len(func.body) == 1:
                continue
            replace_from = func.body[1].lineno
        else:
            replace_from = first_stmt.lineno

        end_line = func.end_lineno  # type: ignore[attr-defined]

        # Determine indentation from the first replaced line.
        target_line = lines[replace_from - 1]
        indent = len(target_line) - len(target_line.lstrip())
        placeholder = " " * indent + "...\n"

        # Replace lines [replace_from, end_line] (1-indexed) with a single '...'
        result[replace_from - 1 : end_line] = [placeholder]

    return "".join(result)


# ---------------------------------------------------------------------------
# Function slice extractor
# ---------------------------------------------------------------------------

def _get_all_functions(code: str) -> list[FunctionSlice]:
    """
    Parse *code* and return a FunctionSlice for every function/method,
    including decorators in the slice boundaries.
    """
    try:
        tree = ast.parse(code)
    except SyntaxError:
        return []

    lines = code.splitlines(keepends=True)
    slices: list[FunctionSlice] = []

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Include decorators: the first decorator's line, if any.
            if node.decorator_list:
                start = node.decorator_list[0].lineno  # 1-indexed
            else:
                start = node.lineno  # 1-indexed

            end = node.end_lineno  # type: ignore[attr-defined]  # 1-indexed inclusive
            source = "".join(lines[start - 1 : end])
            slices.append(
                FunctionSlice(
                    name=node.name,
                    start_line=start,
                    end_line=end,
                    source=source,
                )
            )

    return slices


# ---------------------------------------------------------------------------
# Fast-path: traceback-based function name extraction
# ---------------------------------------------------------------------------

_TRACEBACK_FRAME = re.compile(
    r'^\s+File "[^"]+", line \d+, in (\w+)\s*$',
    re.MULTILINE,
)
_NON_FUNC_NAMES = frozenset(
    {"<module>", "<listcomp>", "<dictcomp>", "<setcomp>", "<genexpr>", "<lambda>"}
)


def extract_function_names_from_traceback(error: str) -> list[str]:
    """
    Return a deduplicated list of function names mentioned in a Python traceback.

    Returns an empty list if fewer than 1 or more than 3 distinct names are
    found (0 = no traceback / no specific target; >3 = too ambiguous for
    fast-path).
    """
    names: list[str] = []
    for m in _TRACEBACK_FRAME.finditer(error):
        name = m.group(1)
        if name not in _NON_FUNC_NAMES and name not in names:
            names.append(name)
    if 1 <= len(names) <= 3:
        return names
    return []


# ---------------------------------------------------------------------------
# Phase 1: diagnosis via lightweight LLM call
# ---------------------------------------------------------------------------

def _diagnose_broken_functions(
    code: str,
    error: str,
    strength: float,
    temperature: float,
    time: float,
    verbose: bool = False,
    language: Optional[str] = None,
) -> list[str]:
    """
    Ask a lightweight LLM to identify broken functions from the code skeleton
    and the error log.  Returns a list of function names (may be empty).

    Any exception is swallowed so callers can fall back silently.
    """
    try:
        from .llm_invoke import llm_invoke  # local import to avoid circular deps

        skeleton = build_skeleton(code)
        # Trim very long error logs to keep the diagnosis call cheap.
        trimmed_error = error[:4000] if len(error) > 4000 else error

        diag_prompt = (
            "You are a code repair assistant. Given a Python code skeleton (function "
            "signatures only, bodies replaced with '...') and a test-failure error log, "
            "identify which functions are most likely causing the failures.\n\n"
            "Code skeleton:\n```python\n{skeleton}\n```\n\n"
            "Error log:\n```\n{error}\n```\n\n"
            "Return ONLY a JSON object with a 'function_names' field: a list of 1–5 "
            "function names that appear in the skeleton above and are most likely broken."
        )

        response = llm_invoke(
            prompt=diag_prompt,
            input_json={"skeleton": skeleton, "error": trimmed_error},
            strength=min(strength, 0.4),  # lightweight call
            temperature=temperature,
            output_pydantic=DiagnosisResult,
            verbose=verbose,
            time=min(time, 0.2) if time is not None else 0.1,
            language=language,
        )

        result = response.get("result")
        if isinstance(result, DiagnosisResult) and result.function_names:
            return result.function_names[:5]
    except Exception:
        pass  # silent fallback

    return []


# ---------------------------------------------------------------------------
# Public API: prepare_focused_inputs
# ---------------------------------------------------------------------------

def prepare_focused_inputs(
    code: str,
    unit_test: str,
    error: str,
    strength: float,
    temperature: float,
    time: float,
    verbose: bool = False,
    language: Optional[str] = None,
) -> Optional[FocusedInputs]:
    """
    Build focused LLM inputs for large dev units.

    Returns a FocusedInputs with the relevant function slices, or None when:
      - the files are not large (caller should use full-file path), or
      - no target functions could be identified, or
      - any error occurred (silent fallback to full-file path).
    """
    try:
        if not is_large(code, unit_test):
            return None

        # Fast-path: try to identify targets from the traceback directly.
        target_names = extract_function_names_from_traceback(error)

        if not target_names:
            # Phase 1: diagnose via skeleton + lightweight LLM.
            target_names = _diagnose_broken_functions(
                code=code,
                error=error,
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                language=language,
            )

        if not target_names:
            return None

        # Phase 2: extract the matching function slices from the code.
        all_slices = _get_all_functions(code)
        if not all_slices:
            return None

        matched = [s for s in all_slices if s.name in target_names]
        if not matched:
            return None

        focused_code = "\n\n".join(s.source for s in matched)
        return FocusedInputs(
            focused_code=focused_code,
            focused_tests=unit_test,
            slices=matched,
        )

    except Exception:
        return None  # silent fallback


# ---------------------------------------------------------------------------
# Public API: reconstruct_code
# ---------------------------------------------------------------------------

def reconstruct_code(
    original_code: str,
    fixed_focused_code: str,
    slices: list[FunctionSlice],
) -> str:
    """
    Splice updated function bodies from *fixed_focused_code* back into
    *original_code* at the line offsets recorded in *slices*.

    Only the named functions that appear in *slices* are replaced; all other
    content in *original_code* is preserved unchanged.

    Returns *original_code* unchanged if splicing fails for any reason.
    """
    try:
        target_names = {s.name for s in slices}

        # Extract the fixed versions of only the targeted functions.
        all_fixed = _get_all_functions(fixed_focused_code)
        fixed_by_name: dict[str, str] = {
            f.name: f.source for f in all_fixed if f.name in target_names
        }

        if not fixed_by_name:
            return original_code

        lines = original_code.splitlines(keepends=True)

        # Process in reverse line order to prevent offset drift when line counts differ.
        for slc in sorted(slices, key=lambda s: s.start_line, reverse=True):
            if slc.name not in fixed_by_name:
                continue
            fixed_source = fixed_by_name[slc.name]
            fixed_lines = fixed_source.splitlines(keepends=True)
            lines[slc.start_line - 1 : slc.end_line] = fixed_lines

        return "".join(lines)

    except Exception:
        return original_code  # silent fallback
