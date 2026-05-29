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
import textwrap
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
    source: str       # dedented source of this function (ready for top-level use)
    qualname: str = ""  # qualified name, e.g. "ClassName.method" or "function"
    indent: int = 0     # original indentation in the source file (number of spaces)


@dataclass
class FocusedInputs:
    """Inputs produced by prepare_focused_inputs() for a focused LLM fix call."""
    focused_code: str           # concatenated source of the matched function slices
    focused_tests: str          # relevant subset of test file (full file as fallback)
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
    Parse *code* and return a FunctionSlice for every top-level function and
    every method of a top-level class.

    Each slice is dedented so it is valid as a standalone top-level definition.
    The original indentation is stored in ``FunctionSlice.indent`` and the
    qualified name (e.g. ``ClassName.method``) is stored in
    ``FunctionSlice.qualname``.
    """
    try:
        tree = ast.parse(code)
    except SyntaxError:
        return []

    lines = code.splitlines(keepends=True)
    slices: list[FunctionSlice] = []

    def _extract(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        class_name: str | None,
    ) -> None:
        start = node.decorator_list[0].lineno if node.decorator_list else node.lineno
        end = node.end_lineno  # type: ignore[attr-defined]
        raw_source = "".join(lines[start - 1 : end])
        first_line = lines[start - 1]
        original_indent = len(first_line) - len(first_line.lstrip())
        dedented = textwrap.dedent(raw_source)
        qualname = f"{class_name}.{node.name}" if class_name else node.name
        slices.append(
            FunctionSlice(
                name=node.name,
                qualname=qualname,
                start_line=start,
                end_line=end,
                source=dedented,
                indent=original_indent,
            )
        )

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _extract(node, None)
        elif isinstance(node, ast.ClassDef):
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    _extract(child, node.name)

    return slices


# ---------------------------------------------------------------------------
# Format slices for the LLM
# ---------------------------------------------------------------------------

def _format_slice_for_llm(slc: FunctionSlice) -> str:
    """
    Return the slice source formatted for inclusion in the focused-repair prompt.

    Top-level functions are returned as-is (already dedented).
    Class methods are wrapped in a minimal class stub so the LLM sees them as
    valid Python and can round-trip them back with their class context intact.
    """
    if slc.qualname == slc.name:
        # Top-level function: dedented source is already valid Python.
        return slc.source
    # Class method: wrap in a minimal class stub.
    class_name = slc.qualname.split(".")[0]
    indented_method = textwrap.indent(slc.source, "    ")
    return f"class {class_name}:\n{indented_method}"


# ---------------------------------------------------------------------------
# Fast-path: traceback-based function name extraction
# ---------------------------------------------------------------------------

_TRACEBACK_FRAME = re.compile(
    r'^\s+File "[^"]+", line \d+, in (\w+)\s*$',
    re.MULTILINE,
)
# Variant that also captures the line number for line-based disambiguation.
_TRACEBACK_FRAME_WITH_LINE = re.compile(
    r'^\s+File "[^"]+", line (\d+), in (\w+)\s*$',
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


def _match_slices_to_traceback(
    all_slices: list[FunctionSlice],
    error: str,
    target_names: list[str],
) -> list[FunctionSlice]:
    """
    Select slices matching *target_names*, using traceback line numbers to
    disambiguate when multiple slices share the same simple name (e.g. two
    classes both have a ``run`` method).

    For each target name with multiple candidates, only slices whose
    ``start_line..end_line`` range contains a traceback line number are
    selected.  If no line number resolves the ambiguity, all candidates are
    included so the caller falls back gracefully.
    """
    # Build name -> [lineno, ...] from traceback frames.
    name_to_linenos: dict[str, list[int]] = {}
    for m in _TRACEBACK_FRAME_WITH_LINE.finditer(error):
        name = m.group(2)
        if name in target_names and name not in _NON_FUNC_NAMES:
            name_to_linenos.setdefault(name, []).append(int(m.group(1)))

    matched: list[FunctionSlice] = []
    seen: set[str] = set()

    for name in target_names:
        # Match by simple name OR by qualname (e.g. "MyClass.run" from LLM output).
        candidates = [s for s in all_slices if s.name == name or s.qualname == name]
        if not candidates:
            continue
        if len(candidates) == 1:
            slc = candidates[0]
            if slc.qualname not in seen:
                matched.append(slc)
                seen.add(slc.qualname)
            continue
        # Multiple candidates share the same simple name (class methods).
        # Try line-based disambiguation.
        linenos = name_to_linenos.get(name, [])
        line_matched = [
            c for c in candidates
            if any(c.start_line <= ln <= c.end_line for ln in linenos)
            and c.qualname not in seen
        ]
        if line_matched:
            for slc in line_matched:
                matched.append(slc)
                seen.add(slc.qualname)
        else:
            # No useful line info: include all candidates (reconstruct_code
            # will handle them correctly via qualname matching).
            for c in candidates:
                if c.qualname not in seen:
                    matched.append(c)
                    seen.add(c.qualname)

    return matched


# ---------------------------------------------------------------------------
# Test slice extractor  (narrows the test file to only the failing tests)
# ---------------------------------------------------------------------------

_PYTEST_FAILED = re.compile(
    r'^(?:FAILED|ERROR)\s+[^\s:]+::([A-Za-z_][A-Za-z0-9_]*)(?:::([A-Za-z_][A-Za-z0-9_]*))?',
    re.MULTILINE,
)

# Standard unittest/pytest setup and teardown method names always included when
# a class is partially extracted so the extracted class remains self-contained.
_SETUP_NAMES: frozenset[str] = frozenset({
    "setUp", "tearDown", "setUpClass", "tearDownClass",
    "setup_method", "teardown_method", "setup_class", "teardown_class",
    "setup", "teardown",
})


def _has_fixture_decorator(decorators: list[ast.expr]) -> bool:
    """Return True if any decorator is pytest.fixture or fixture."""
    for d in decorators:
        if isinstance(d, ast.Attribute) and d.attr == "fixture":
            return True
        if isinstance(d, ast.Name) and d.id == "fixture":
            return True
        if isinstance(d, ast.Call):
            func = d.func
            if (isinstance(func, ast.Attribute) and func.attr == "fixture") or (
                isinstance(func, ast.Name) and func.id == "fixture"
            ):
                return True
    return False


def _is_noncollecting_test_class(node: ast.ClassDef) -> bool:
    """Return True when a Test* class is likely support context, not tests."""
    has_test_method = any(
        isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
        and child.name.startswith("test_")
        for child in node.body
    )
    if not has_test_method:
        return True
    for child in node.body:
        if not isinstance(child, ast.Assign):
            continue
        if not any(isinstance(t, ast.Name) and t.id == "__test__" for t in child.targets):
            continue
        if isinstance(child.value, ast.Constant) and child.value.value is False:
            return True
    return False


def _defined_names(source: str) -> set[str]:
    """Return top-level names defined by imports, assignments, defs, and classes."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return set()

    names: set[str] = set()
    for node in tree.body:
        if isinstance(node, ast.Import):
            for alias in node.names:
                names.add(alias.asname or alias.name.split(".", 1)[0])
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name != "*":
                    names.add(alias.asname or alias.name)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            targets = []
            if isinstance(node, ast.Assign):
                targets = list(node.targets)
            else:
                targets = [node.target]
            for target in targets:
                for child in ast.walk(target):
                    if isinstance(child, ast.Name):
                        names.add(child.id)
    return names


def _loaded_names(source: str) -> set[str]:
    """Return names loaded by *source*."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return set()
    return {
        node.id
        for node in ast.walk(tree)
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
    }


def _extract_test_slices(error: str, unit_test: str) -> str:
    """
    Extract only the failing test functions/classes from *unit_test*.

    Parses pytest FAILED/ERROR lines to identify target names, then uses AST
    to extract those top-level functions/classes plus module-level imports and
    fixture definitions.  Returns *unit_test* unchanged when extraction fails,
    produces no targets, or the result is not meaningfully smaller.

    For ``Class::method`` node IDs, only the failing method (plus setup/teardown
    and fixture methods) is extracted from the class, rather than the whole
    class.  Falls back to the full class when precise extraction fails.
    """
    try:
        # Parse failing targets.
        # func_targets: top-level function names (or class names without a
        #   specific method, e.g. a class-level ERROR).
        # class_targets: class_name -> set of specific failing method names.
        func_targets: set[str] = set()
        class_targets: dict[str, set[str]] = {}

        for m in _PYTEST_FAILED.finditer(error):
            first, second = m.group(1), m.group(2)
            if second:
                # Class::method format — record the specific method.
                if first not in class_targets:
                    class_targets[first] = set()
                class_targets[first].add(second)
            else:
                # Top-level function or class-only reference (e.g. collection error).
                func_targets.add(first)

        if not func_targets and not class_targets:
            return unit_test

        try:
            tree = ast.parse(unit_test)
        except SyntaxError:
            return unit_test

        lines = unit_test.splitlines(keepends=True)
        preamble_parts: list[str] = []
        test_parts: list[str] = []
        support_defs: dict[str, str] = {}

        def remember_support(name: str, chunk: str) -> None:
            if name not in support_defs:
                support_defs[name] = chunk

        for node in tree.body:
            node_end = getattr(node, "end_lineno", node.lineno)

            if isinstance(node, (ast.Import, ast.ImportFrom)):
                chunk = "".join(lines[node.lineno - 1 : node_end])
                preamble_parts.append(chunk)

            elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                # Module-level constants and assignments (e.g. CASES, TEST_DATA)
                # used as shared test data; include so selected tests can reference them.
                chunk = "".join(lines[node.lineno - 1 : node_end])
                preamble_parts.append(chunk)

            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                deco_start = (
                    node.decorator_list[0].lineno if node.decorator_list else node.lineno
                )
                chunk = "".join(lines[deco_start - 1 : node_end])
                is_fixture = _has_fixture_decorator(node.decorator_list)
                if node.name in func_targets:
                    test_parts.append(chunk)
                elif is_fixture or not node.name.startswith("test_"):
                    # Include fixtures and module-level helper functions so that
                    # selected tests can call them without NameError.
                    preamble_parts.append(chunk)
                else:
                    remember_support(node.name, chunk)

            elif isinstance(node, ast.ClassDef):
                deco_start = (
                    node.decorator_list[0].lineno if node.decorator_list else node.lineno
                )
                if node.name in func_targets:
                    # Class-level failure (no specific method) — include whole class.
                    chunk = "".join(lines[deco_start - 1 : node_end])
                    test_parts.append(chunk)
                elif node.name in class_targets:
                    method_targets = class_targets[node.name]
                    # Try to extract only the targeted methods plus setup/teardown/fixtures.
                    first_body_start = node.body[0].lineno if node.body else node_end + 1
                    if node.body and getattr(node.body[0], "decorator_list", None):
                        first_body_start = node.body[0].decorator_list[0].lineno
                    class_header = "".join(lines[deco_start - 1 : first_body_start - 1])
                    selected_methods: list[str] = []
                    for child in node.body:
                        child_end = getattr(child, "end_lineno", child.lineno)
                        if isinstance(child, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                            # Class-level attributes/constants (e.g. CASES = [...])
                            # needed by targeted methods via self.CASES.
                            selected_methods.append(
                                "".join(lines[child.lineno - 1 : child_end])
                            )
                        elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            child_deco = (
                                child.decorator_list[0].lineno
                                if child.decorator_list
                                else child.lineno
                            )
                            if (
                                child.name in method_targets
                                or child.name in _SETUP_NAMES
                                or _has_fixture_decorator(child.decorator_list)
                                or not child.name.startswith("test_")
                            ):
                                # Include: targeted methods, setup/teardown/fixtures, and
                                # non-test helper methods (e.g. self.helper()) so that
                                # targeted tests have all referenced context.
                                selected_methods.append(
                                    "".join(lines[child_deco - 1 : child_end])
                                )
                    if selected_methods:
                        class_text = class_header + "\n".join(selected_methods) + "\n"
                        test_parts.append(class_text)
                    else:
                        # Fallback: include whole class.
                        chunk = "".join(lines[deco_start - 1 : node_end])
                        test_parts.append(chunk)
                else:
                    # Non-target class: include as preamble if it looks like a helper/data
                    # class (name does not start with "Test") so that failing tests can
                    # reference it without NameError (e.g. `class Case`, `class Params`).
                    chunk = "".join(lines[deco_start - 1 : node_end])
                    if not node.name.startswith("Test"):
                        preamble_parts.append(chunk)
                    elif _is_noncollecting_test_class(node):
                        remember_support(node.name, chunk)

        if not test_parts:
            return unit_test

        preamble = "".join(preamble_parts).rstrip("\n")
        body = "\n\n".join(t.rstrip("\n") for t in test_parts)
        result = f"{preamble}\n\n{body}\n" if preamble else f"{body}\n"

        # If the minimized slice still references top-level helpers from the
        # original test module, add only those support definitions. This prevents
        # focused prompts like `class TestFeature(TestBase): ...` from omitting
        # `TestBase`, while avoiding unrelated collected test classes.
        added_support: set[str] = set()
        while True:
            missing = [
                name for name in sorted(_loaded_names(result) - _defined_names(result))
                if name in support_defs and name not in added_support
            ]
            if not missing:
                break
            additions = []
            for name in missing:
                additions.append(support_defs[name].rstrip("\n"))
                added_support.add(name)
            if preamble:
                preamble = preamble + "\n\n" + "\n\n".join(additions)
            else:
                preamble = "\n\n".join(additions)
            result = f"{preamble}\n\n{body}\n"

        # Only use the extracted version if it is meaningfully smaller.
        if len(result) >= 0.9 * len(unit_test):
            return unit_test

        return result

    except Exception:
        return unit_test


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

        try:
            ast.parse(code)
        except SyntaxError:
            return []

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
        phase1_ran = False

        if not target_names:
            phase1_ran = True
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

        # Use traceback line numbers to disambiguate same-named methods across
        # different classes before falling back to simple name matching.
        matched = _match_slices_to_traceback(all_slices, error, target_names)
        if not matched and not phase1_ran:
            # Fast-path names (e.g. test_* functions only) matched nothing in
            # product code.  Run Phase 1 diagnosis before giving up.
            target_names = _diagnose_broken_functions(
                code=code,
                error=error,
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                language=language,
            )
            if target_names:
                matched = _match_slices_to_traceback(all_slices, error, target_names)

        if not matched:
            return None

        # Build focused code using class stubs for methods so the LLM receives
        # valid Python and can return it with class context preserved.
        focused_code = "\n\n".join(_format_slice_for_llm(s) for s in matched)

        # Extract only the failing test functions/classes to reduce the test payload.
        focused_tests = _extract_test_slices(error, unit_test)

        return FocusedInputs(
            focused_code=focused_code,
            focused_tests=focused_tests,
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

    Matches fixed functions by qualified name (e.g. ``ClassName.method``) when
    the LLM preserved the class stub wrapper, falling back to simple name
    matching otherwise.  Each fixed slice is reindented from its dedented form
    to the original indentation level before splicing.

    Returns *original_code* unchanged if splicing fails for any reason.
    """
    try:
        all_fixed = _get_all_functions(fixed_focused_code)
        if not all_fixed:
            return original_code

        # Build lookup tables: qualified name → dedented fixed source,
        # and simple name → dedented fixed source (fallback).
        fixed_by_qualname: dict[str, str] = {f.qualname: f.source for f in all_fixed}
        fixed_by_name: dict[str, str] = {f.name: f.source for f in all_fixed}

        lines = original_code.splitlines(keepends=True)

        # Process in reverse line order to prevent offset drift.
        for slc in sorted(slices, key=lambda s: s.start_line, reverse=True):
            # Prefer qualname match (handles class stubs and avoids collisions).
            # Only fall back to simple name for top-level functions (where
            # qualname == name): never for class methods, because two classes
            # can share the same method name and the wrong fix would be spliced
            # into the non-targeted class.
            fixed_dedented = fixed_by_qualname.get(slc.qualname)
            if fixed_dedented is None and slc.qualname == slc.name:
                fixed_dedented = fixed_by_name.get(slc.name)
            if fixed_dedented is None:
                continue

            # Reindent the fixed (dedented) source to the original indent level.
            if slc.indent > 0:
                fixed_indented = textwrap.indent(fixed_dedented, " " * slc.indent)
            else:
                fixed_indented = fixed_dedented

            fixed_lines = fixed_indented.splitlines(keepends=True)
            lines[slc.start_line - 1 : slc.end_line] = fixed_lines

        return "".join(lines)

    except Exception:
        return original_code  # silent fallback
