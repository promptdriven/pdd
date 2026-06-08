"""Generated test quality gate: detects brittle selectors and private assertions (issue #1466).

Analyzes test source files using the stdlib ast module and regex to detect:
- Brittle CSS utility selectors (e.g., .btn-primary-abc1234)
- Exact dynamic text in assertions (ISO timestamps, UUIDs)
- Private attribute/implementation-detail assertions (obj._internal)
- Happy-path-only test suites (no error cases)

All processing is deterministic — no LLM calls.
"""
from __future__ import annotations

import ast
import logging
import re
from pathlib import Path

from pdd.generation_source_contract import (
    TestFindingKind,
    TestQualityFinding,
)

logger = logging.getLogger(__name__)

# CSS utility class pattern: random-looking suffix with 4+ alphanumeric chars
_BRITTLE_CSS_PATTERN = re.compile(
    r'\.(?:[a-zA-Z0-9_-]+-)?(?:[a-f0-9]{4,}|[a-zA-Z]{3,}\d{3,})',
)

# Exact ISO timestamp / UUID in assertion
_DYNAMIC_TEXT_PATTERN = re.compile(
    r'(?:\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}|'
    r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})',
)


def _find_brittle_selectors(
    source: str, source_file: Path
) -> list[TestQualityFinding]:
    """Find brittle CSS selector patterns in test source."""
    findings: list[TestQualityFinding] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if _BRITTLE_CSS_PATTERN.search(line):
            findings.append(
                TestQualityFinding(
                    test_file=str(source_file),
                    line=lineno,
                    finding_kind=TestFindingKind.brittle_selector,
                    detail=f"Brittle CSS utility selector detected: {line.strip()!r}",
                    suggestion=(
                        "Use semantic selectors instead: By.ARIA_LABEL, By.ROLE, "
                        "getByRole(), or data-testid attributes."
                    ),
                )
            )
    return findings


def _find_exact_dynamic_text(
    source: str, source_file: Path
) -> list[TestQualityFinding]:
    """Find exact ISO timestamps and UUIDs hardcoded in assertions."""
    findings: list[TestQualityFinding] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if _DYNAMIC_TEXT_PATTERN.search(line) and "assert" in line.lower():
            findings.append(
                TestQualityFinding(
                    test_file=str(source_file),
                    line=lineno,
                    finding_kind=TestFindingKind.exact_dynamic_text,
                    detail=f"Exact dynamic text in assertion: {line.strip()!r}",
                    suggestion=(
                        "Use pattern matching (re.match) or partial string checks "
                        "instead of exact timestamp/UUID comparisons."
                    ),
                )
            )
    return findings


def _find_private_impl_assertions(
    tree: ast.AST, source_file: Path
) -> list[TestQualityFinding]:
    """Find assertions on private attributes (_name or __name) via AST walk."""
    findings: list[TestQualityFinding] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and node.attr.startswith("_"):
            lineno = getattr(node, "lineno", 0)
            findings.append(
                TestQualityFinding(
                    test_file=str(source_file),
                    line=lineno,
                    finding_kind=TestFindingKind.private_impl_assertion,
                    detail=f"Assertion on private attribute: .{node.attr}",
                    suggestion=(
                        f"Assert on public interface, not private attribute '.{node.attr}'. "
                        "Test observable behavior via public API instead."
                    ),
                )
            )
    return findings


def _find_happy_path_only(
    tree: ast.AST, source_file: Path
) -> list[TestQualityFinding]:
    """Find test classes/files that have no error cases (happy-path only)."""
    findings: list[TestQualityFinding] = []

    # Gather all test functions
    test_funcs = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")
    ]

    if not test_funcs:
        return []

    # Check if any test function contains pytest.raises or error-related assertions
    has_error_case = False
    for func in test_funcs:
        for node in ast.walk(func):
            if isinstance(node, ast.Call):
                func_attr = getattr(node.func, "attr", "")
                func_id = getattr(node.func, "id", "")
                if "raises" in (func_attr or func_id):
                    has_error_case = True
                    break
            # Also check for "error", "exception", "fail" in test names
        if has_error_case:
            break

    # Also check test function names for error/exception/invalid patterns
    if not has_error_case:
        error_keywords = ("error", "exception", "invalid", "fail", "raise", "decline")
        has_error_case = any(
            any(kw in func.name.lower() for kw in error_keywords)
            for func in test_funcs
        )

    if not has_error_case and len(test_funcs) >= 1:
        lineno = getattr(test_funcs[0], "lineno", 1)
        findings.append(
            TestQualityFinding(
                test_file=str(source_file),
                line=lineno,
                finding_kind=TestFindingKind.happy_path_only,
                detail=(
                    f"Test file has {len(test_funcs)} test(s) but no error/edge cases detected."
                ),
                suggestion=(
                    "Add tests for error conditions: invalid inputs, boundary values, "
                    "and exception paths (use pytest.raises for expected exceptions)."
                ),
            )
        )

    return findings


def audit_test_quality(test_files: list[Path]) -> list[TestQualityFinding]:
    """Audit a list of test files for quality issues.

    Returns an empty list for an empty input. No LLM calls — pure AST/regex analysis.

    Detects:
    - brittle_selector: CSS utility class selectors
    - exact_dynamic_text: hardcoded timestamps/UUIDs in assertions
    - private_impl_assertion: assertions on _private attributes
    - happy_path_only: no error or edge-case tests present
    """
    if not test_files:
        return []

    all_findings: list[TestQualityFinding] = []

    for test_file in test_files:
        if not test_file.exists():
            logger.warning("audit_test_quality: file not found: %s", test_file)
            continue

        try:
            source = test_file.read_text(encoding="utf-8")
        except OSError as exc:
            logger.warning("audit_test_quality: cannot read %s: %s", test_file, exc)
            continue

        # Brittle CSS selectors (regex on source text)
        all_findings.extend(_find_brittle_selectors(source, test_file))

        # Exact dynamic text in assertions (regex on source text)
        all_findings.extend(_find_exact_dynamic_text(source, test_file))

        # AST-based checks
        try:
            tree = ast.parse(source, filename=str(test_file))
        except SyntaxError as exc:
            logger.warning("audit_test_quality: syntax error in %s: %s", test_file, exc)
            continue

        all_findings.extend(_find_private_impl_assertions(tree, test_file))
        all_findings.extend(_find_happy_path_only(tree, test_file))

    logger.debug(
        "audit_test_quality: %d files, %d findings", len(test_files), len(all_findings)
    )
    return all_findings
