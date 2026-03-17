#!/usr/bin/env python3
"""Validate that a generated test file is behavioral, not structural.

Two-layer detection:
1. AST analysis (Python): checks that tests actually CALL the function under test
   and don't import introspection modules. This is a POSITIVE check — "does the test
   do the right thing?" — not a blocklist of bad patterns.
2. Import/reflection module detection (all languages): flags imports of reflection
   modules at the module level. Catches the entire module, not individual functions,
   so novel introspection patterns within a flagged module are still caught.

Usage:
    python validate_behavioral_test.py <test_file> <language> <buggy_source_file>

Exit codes:
    0 = behavioral test (good)
    1 = structural test detected (bad)
    2 = usage error
"""

import ast
import re
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Python AST analysis
# ---------------------------------------------------------------------------

# Entire modules that have no business being imported in a behavioral test.
# This is NOT a function-level blocklist — importing the module at all is the signal.
INTROSPECTION_MODULES = frozenset({
    "inspect",       # signature, getsource, getfullargspec, getmembers, ...
    "dis",           # bytecode disassembly
    "ctypes",        # C-level struct introspection
})

# Builtins that, when used inside an assert, indicate structural testing.
# We only flag these when they appear as the TOP-LEVEL call in an assertion,
# not when they're used as normal control flow.
STRUCTURAL_ASSERT_BUILTINS = frozenset({
    "hasattr",
    "getattr",
    "callable",
    "dir",
    "vars",
})


def _extract_function_names_from_source(source_path: str) -> set[str]:
    """Extract top-level and class-method function names from the buggy source."""
    try:
        tree = ast.parse(Path(source_path).read_text())
    except (SyntaxError, FileNotFoundError):
        return set()

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            names.add(node.name)
    return names


def _get_call_names(node: ast.AST) -> set[str]:
    """Recursively collect all function/method names called within an AST subtree."""
    names: set[str] = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Call):
            if isinstance(child.func, ast.Name):
                names.add(child.func.id)
            elif isinstance(child.func, ast.Attribute):
                names.add(child.func.attr)
    return names


def check_python_ast(test_path: str, source_path: str) -> list[str]:
    """AST-level analysis of a Python test file.

    Returns a list of issues found. Empty list = test is behavioral.
    """
    test_source = Path(test_path).read_text()
    try:
        tree = ast.parse(test_source)
    except SyntaxError as exc:
        return [f"SyntaxError in generated test: {exc}"]

    issues: list[str] = []

    # --- Layer 1: introspection module imports ---
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                root_module = alias.name.split(".")[0]
                if root_module in INTROSPECTION_MODULES:
                    issues.append(
                        f"Imports introspection module '{alias.name}' — "
                        f"behavioral tests should not need {root_module}"
                    )
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                root_module = node.module.split(".")[0]
                if root_module in INTROSPECTION_MODULES:
                    imported = ", ".join(a.name for a in node.names)
                    issues.append(
                        f"Imports from introspection module '{node.module}' "
                        f"({imported}) — this indicates structural testing"
                    )

    # --- Layer 2: structural builtins inside assertions ---
    for node in ast.walk(tree):
        if isinstance(node, ast.Assert):
            # Walk the assertion expression looking for structural calls
            for child in ast.walk(node.test):
                if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
                    if child.func.id in STRUCTURAL_ASSERT_BUILTINS:
                        issues.append(
                            f"Assertion uses structural builtin '{child.func.id}()' — "
                            f"tests should assert on behavior (return values, side effects), "
                            f"not code shape"
                        )
        # Also catch pytest-style: assert hasattr(...) or just hasattr as expression
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            func = node.value.func
            if isinstance(func, ast.Attribute):
                # e.g., self.assertTrue(hasattr(...))
                for arg in ast.walk(node.value):
                    if isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name):
                        if arg.func.id in STRUCTURAL_ASSERT_BUILTINS:
                            issues.append(
                                f"Test assertion wraps structural builtin "
                                f"'{arg.func.id}()'"
                            )

    # --- Layer 3: POSITIVE check — does the test call the function under test? ---
    source_funcs = _extract_function_names_from_source(source_path)
    if source_funcs:
        # Exclude dunder methods and private helpers — focus on public API
        public_funcs = {f for f in source_funcs if not f.startswith("_")}
        if public_funcs:
            # Collect all function calls made inside test functions
            test_calls: set[str] = set()
            for node in ast.walk(tree):
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if node.name.startswith("test_") or node.name.startswith("test"):
                        test_calls.update(_get_call_names(node))

            # Check if ANY public function from the buggy source is called
            called_source_funcs = public_funcs & test_calls
            if not called_source_funcs:
                issues.append(
                    f"No test function calls any public function from the source "
                    f"({', '.join(sorted(public_funcs))}). Behavioral tests must "
                    f"actually invoke the code under test."
                )

    return issues


# ---------------------------------------------------------------------------
# Language-agnostic reflection module detection
# ---------------------------------------------------------------------------

# Map of language -> list of (pattern, description).
# These detect IMPORTS of reflection modules, not individual function calls.
# Catching the import means ANY usage of that module is flagged, even novel patterns.
REFLECTION_IMPORT_PATTERNS: dict[str, list[tuple[str, str]]] = {
    "Python": [
        (r"^\s*(import\s+inspect|from\s+inspect\s+import)", "inspect module"),
        (r"^\s*(import\s+dis|from\s+dis\s+import)", "dis module"),
        (r"^\s*from\s+typing\s+import\s+.*get_type_hints", "typing.get_type_hints"),
    ],
    "Go": [
        (r'^\s*"reflect"', "reflect package"),
        (r'^\s*"runtime"', "runtime package (introspection)"),
        (r'^\s*"go/ast"', "go/ast package"),
    ],
    "Java": [
        (r"^\s*import\s+java\.lang\.reflect\b", "java.lang.reflect"),
        (r"^\s*import\s+java\.lang\.invoke\b", "java.lang.invoke (MethodHandle introspection)"),
    ],
    "JavaScript": [
        (r"\bReflect\.(get|has|ownKeys|apply|construct|defineProperty|getOwnPropertyDescriptor)\b",
         "Reflect API"),
        (r"\bFunction\.prototype\.toString\b", "Function.prototype.toString"),
        (r"\bObject\.getOwnPropertyDescriptor\b", "Object.getOwnPropertyDescriptor"),
    ],
    "Ruby": [
        (r"\b(respond_to\?|method_defined\?|instance_method|\.methods\b)", "Ruby introspection"),
    ],
}

# Assertion patterns — POSITIVE check that the file contains real assertions.
ASSERTION_PATTERNS: dict[str, list[str]] = {
    "Python": [r"\bassert\s", r"assertEqual", r"assertTrue", r"assertRaises", r"pytest\.raises", r"\.assert_called", r"\.assert_not_called", r"\.assert_has_calls"],
    "Go": [r"\bt\.(Error|Fatal|Run|Helper)\b", r"\bassert\.", r"\brequire\."],
    "Java": [r"\bassert(Equals|True|False|Throws|NotNull|That)\b", r"@Test"],
    "JavaScript": [r"\bexpect\s*\(", r"\bassert\s*[\.(]", r"\bit\s*\(", r"\btest\s*\("],
    "Ruby": [r"\bassert", r"\bexpect\s*[\({]", r"\bit\s+['\"]", r"\bdescribe\s+['\"]"],
}


def check_language_agnostic(test_path: str, language: str) -> list[str]:
    """Content-level checks for any language."""
    content = Path(test_path).read_text()
    issues: list[str] = []

    # Check for reflection module imports
    patterns = REFLECTION_IMPORT_PATTERNS.get(language, [])
    for pattern, desc in patterns:
        if re.search(pattern, content, re.MULTILINE):
            issues.append(f"Imports reflection/introspection ({desc}) — structural signal")

    # Positive check: file must contain assertions
    assertion_pats = ASSERTION_PATTERNS.get(language, [])
    if assertion_pats and not any(re.search(p, content) for p in assertion_pats):
        issues.append(f"No assertion patterns found for {language} — not a real test")

    return issues


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <test_file> <language> [buggy_source_file]", file=sys.stderr)
        return 2

    test_file = sys.argv[1]
    language = sys.argv[2]
    source_file = sys.argv[3] if len(sys.argv) > 3 else ""

    if not Path(test_file).exists():
        print(f"ERROR: test file not found: {test_file}", file=sys.stderr)
        return 2

    all_issues: list[str] = []

    # Language-agnostic checks (all languages)
    all_issues.extend(check_language_agnostic(test_file, language))

    # Python-specific AST analysis
    if language == "Python":
        all_issues.extend(check_python_ast(test_file, source_file))

    if all_issues:
        print(f"STRUCTURAL TEST DETECTED in {test_file}:")
        for issue in all_issues:
            print(f"  - {issue}")
        return 1
    else:
        print(f"PASS: {test_file} appears to be a behavioral test")
        return 0


if __name__ == "__main__":
    sys.exit(main())
