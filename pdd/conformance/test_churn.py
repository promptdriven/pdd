"""The test-churn gate: refuses high-churn rewrites of existing test files.

Also owns the test-path taxonomy (``_is_test_output_path``,
``_is_python_generation``), which the public-surface gate reuses to exempt test
files from surface checks.
"""

import difflib
import glob
import logging
import os
import pathlib
import re
from typing import List, Optional

from .directives import _env_flag_enabled, _iter_breaking_change_directives
from .gate_errors import TestChurnError, _LANGUAGE_TEST_FILE_EXTS

logger = logging.getLogger(__name__)


# Test-churn opt-out verbs. The marker doc and prompt body advertise both
# imperative ("rewrite tests") and gerund ("rewriting tests") wording, so the
# parser must accept both — anything documented in the directive emitted by
# `TestChurnError.repair_directive` must opt out the gate when echoed back.
_TEST_CHURN_OPT_OUT_RE = re.compile(
    r"\b("
    r"rewrit(?:e|es|ed|ing)|"
    r"replac(?:e|es|ed|ing)|"
    r"regenerat(?:e|es|ed|ing)|"
    r"overwrit(?:e|es|ing|ten)|"
    r"churn|"
    r"remov(?:e|es|ed|ing)|"
    r"drop(?:s|ped|ping)?"
    r")\b",
    re.IGNORECASE,
)

_TEST_CHURN_TARGET_RE = re.compile(r"\btests?\b", re.IGNORECASE)

# Separators that break the verb-object phrase. If any of these appears
# between the opt-out verb and `tests?`, the verb's nearest object is
# something OTHER than tests, so the directive must NOT opt out the gate.
# Examples: `rewrite docs and update tests` (the verb's object is "docs",
# not "tests"); `rewrite calculator, update tests` (comma breaks the phrase).
_TEST_CHURN_BRIDGE_BREAK_RE = re.compile(
    r"[,;]|\b(?:and|but|then|or|plus|also)\b",
    re.IGNORECASE,
)

def _prompt_allows_test_churn(prompt_content: Optional[str]) -> bool:
    """Return True only for explicit test rewrite/churn breaking-change directives.

    Only anchored ``BREAKING-CHANGE:`` directive lines count: prose that
    mentions the marker mid-line (e.g. instructional text referring to it)
    must NOT silently disable the test-churn gate. The directive must also
    pair an opt-out verb (imperative or gerund — ``rewrite``/``rewriting``/
    ``replace``/``replacing`` etc.) with the ``test``/``tests`` object: the
    parser scans every opt-out verb match, and requires that ``tests?``
    appear in the SAME verb-object phrase (no comma, semicolon, or
    conjunction like ``and``/``but``/``then``/``or`` between the verb
    and ``tests?``). That way:

    - ``BREAKING-CHANGE: rewriting the failing tests`` opts out (verb's
      object IS tests).
    - ``BREAKING-CHANGE: rewrite the test suite for new helper`` opts out
      (verb's object IS tests; trailing prose after a noun phrase is fine).
    - ``BREAKING-CHANGE: rewrite docs and update tests`` does NOT opt out
      (``rewrite``'s object is ``docs``; ``and`` breaks the phrase before
      ``tests``, and ``update`` is not in the opt-out verb list).
    - ``BREAKING-CHANGE: drop foo and rewrite tests`` DOES opt out (the
      second verb ``rewrite`` directly governs ``tests``).
    """
    for directive in _iter_breaking_change_directives(prompt_content):
        for verb_match in _TEST_CHURN_OPT_OUT_RE.finditer(directive):
            tail = directive[verb_match.end():]
            target_match = _TEST_CHURN_TARGET_RE.search(tail)
            if not target_match:
                continue
            bridge = tail[: target_match.start()]
            if _TEST_CHURN_BRIDGE_BREAK_RE.search(bridge):
                # A separator/conjunction breaks the verb-object phrase, so
                # `tests?` belongs to a DIFFERENT verb than the opt-out one.
                continue
            return True
    return False

def _is_python_generation(language: Optional[str], output_path: Optional[str]) -> bool:
    detected = (language or "").lower()
    return detected in {"python", "py"} or bool(
        output_path and str(output_path).lower().endswith(".py")
    )

def _is_test_output_path(output_path: Optional[str]) -> bool:
    if not output_path:
        return False
    path = pathlib.Path(str(output_path))
    name = path.name
    lower_name = name.lower()
    js_like_test_suffixes = (
        ".test.ts",
        ".test.tsx",
        ".test.js",
        ".test.jsx",
        ".test.mjs",
        ".test.cjs",
        ".spec.ts",
        ".spec.tsx",
        ".spec.js",
        ".spec.jsx",
        ".spec.mjs",
        ".spec.cjs",
    )
    # `<name>_test.<ext>` / `<name>_spec.<ext>` patterns for files that
    # live next to production code rather than under `tests/`. Go's
    # `handler_test.go` is the canonical example; Ruby (`widget_spec.rb`),
    # Rust (`widget_test.rs`), Elixir (`widget_test.exs`), Dart
    # (`widget_test.dart`), Clojure, and Lua all follow analogous
    # shapes. Driven by `_LANGUAGE_TEST_FILE_EXTS` so adding a new
    # language to `language_format.csv` automatically covers its
    # `_test.<ext>` / `_spec.<ext>` naming without another fix round.
    if any(
        lower_name.endswith(f"_test{ext}") or lower_name.endswith(f"_spec{ext}")
        for ext in _LANGUAGE_TEST_FILE_EXTS
    ):
        return True
    # PascalCase JVM/.NET/Swift test suffixes: `FooTest.java`,
    # `FooIT.java` (Maven failsafe integration test), `FooTestCase.java`
    # (older JUnit/TestNG), `BarTests.kt`, `WidgetSpec.kt`, ScalaTest's
    # `FooSpec.scala`, ScalaCheck / Spock `FooSpec.groovy`, Swift
    # `FooTests.swift`, xUnit/NUnit `FooTests.cs`. The agentic test
    # prompt names `Test.java` as a recognised convention; the rest
    # follow the same camel-case convention. Case-sensitive —
    # lowercasing would false-positive on `latest.kt`, `manifest.java`,
    # `request.scala`, `latest.groovy` etc. Languages whose test
    # filenames are lowercase (Python/Go/Ruby/Rust/Elixir/Dart/...) are
    # already handled by the `_test.<ext>` / `_spec.<ext>` branch above.
    pascal_test_suffixes = (
        "Test.java",
        "Tests.java",
        "TestCase.java",
        "IT.java",
        "Test.kt",
        "Tests.kt",
        "Spec.kt",
        "Test.scala",
        "Tests.scala",
        "Spec.scala",
        "Test.groovy",
        "Tests.groovy",
        "Spec.groovy",
        "Tests.swift",
        "Test.cs",
        "Tests.cs",
    )
    return (
        name.startswith("test_")
        or lower_name.endswith(js_like_test_suffixes)
        or name.endswith(pascal_test_suffixes)
        or any(part in {"tests", "__tests__", "__test__"} for part in path.parts)
    )

def _get_test_churn_threshold() -> float:
    """Return the PDD_TEST_CHURN_THRESHOLD as a clamped 0..1 ratio.

    Accepts either a decimal ratio (``"0.40"``) or a percent string
    (``"40%"`` / ``"100%"``). The percent suffix is stripped and the value
    is divided by 100 before clamping. Unparseable values (``"invalid"``)
    log a warning and fall back to the documented default of ``0.40`` so
    a typo doesn't silently disable the gate.
    """
    raw = os.environ.get("PDD_TEST_CHURN_THRESHOLD", "0.40")
    text = (raw or "").strip()
    if not text:
        return 0.40
    is_percent = text.endswith("%")
    if is_percent:
        text = text[:-1].rstrip()
    try:
        value = float(text)
    except (TypeError, ValueError):
        logger.warning(
            "PDD_TEST_CHURN_THRESHOLD=%r is not a number; "
            "falling back to default 0.40.",
            raw,
        )
        return 0.40
    if is_percent:
        value /= 100.0
    if value < 0:
        return 0.0
    if value > 1:
        return 1.0
    return value

def _compute_test_churn_ratio(pre_text: str, post_text: str) -> float:
    before_lines = (pre_text or "").splitlines()
    after_lines = (post_text or "").splitlines()
    diff = difflib.unified_diff(before_lines, after_lines, lineterm="")
    added = 0
    removed = 0
    for line in diff:
        if line.startswith(("+++", "---", "@@")):
            continue
        if line.startswith("+"):
            added += 1
        elif line.startswith("-"):
            removed += 1
    if removed == 0:
        return 0.0
    return min(max(added, removed) / max(len(before_lines), 1), 1.0)

def _calculate_test_churn_ratio(before: str, after: str) -> float:
    """Backward-compatible wrapper for the prompt-named churn helper."""
    return _compute_test_churn_ratio(before, after)

def _verify_test_churn(
    existing_code: Optional[str],
    generated_code: str,
    prompt_name: str,
    output_path: Optional[str],
    prompt_content: Optional[str],
    adopted_human: bool = False,
) -> None:
    """Fail when rewriting an existing test file exceeds the churn threshold.

    *adopted_human* records whether this test was adopted from an existing HUMAN
    co-located test (unpinned) — provenance the issue #1903 §B.4 never-block
    requires, computed by the caller at path-resolution time. It only annotates
    the raised error; the gate decision here is unchanged.
    """
    if (
        not existing_code
        or not existing_code.strip()
        or _env_flag_enabled("PDD_SKIP_TEST_CHURN_GATE")
        or _env_flag_enabled("PDD_SKIP_CONFORMANCE")
        or not _is_test_output_path(output_path)
        or _prompt_allows_test_churn(prompt_content)
    ):
        return

    threshold = _get_test_churn_threshold()
    ratio = _compute_test_churn_ratio(existing_code, generated_code)
    if ratio > threshold:
        raise TestChurnError(
            prompt_name=prompt_name,
            output_path=output_path or "",
            churn_ratio=ratio,
            threshold=threshold,
            pre_line_count=len(existing_code.splitlines()),
            post_line_count=len(generated_code.splitlines()),
            adopted_human=adopted_human,
        )

def _find_default_test_files(tests_dir: Optional[str], code_file_path: Optional[str]) -> List[str]:
    """Find default test files for a given code file in the tests directory."""
    if not tests_dir or not code_file_path:
        return []

    tests_path = pathlib.Path(tests_dir)
    code_path = pathlib.Path(code_file_path)

    if not tests_path.exists() or not tests_path.is_dir():
        return []

    code_stem = code_path.stem
    code_suffix = code_path.suffix

    # Look for files starting with test_{code_stem}
    # We look for test_{code_stem}*.{code_suffix}
    # e.g., hello.py -> test_hello.py, test_hello_1.py
    pattern = f"test_{glob.escape(code_stem)}*{glob.escape(code_suffix)}"
    found_files = list(tests_path.glob(pattern))

    return [str(p) for p in sorted(found_files)]
