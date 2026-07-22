"""
Real-LLM regression tests for issue #939: call-site enumeration and retry safety.

Two tests, each making one change() call + deterministic output checks:
1. Call-site enumeration — verifies the LLM lists all 4 call sites by name
2. Retry safety — verifies the LLM specifies a max retry count AND fallback

Requires: PDD_RUN_REAL_LLM_TESTS=1 or --run-all
"""

import os
import re
from dataclasses import dataclass
from pathlib import Path

import pytest

from pdd.change import change

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


def _skip_unless_real() -> None:
    """Skip unless real LLM tests are enabled."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM tests require API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all."
        )


@dataclass(frozen=True)
class JudgmentResult:
    """Structured result for deterministic release-gate evaluation."""

    passed: bool
    reasoning: str


CALL_SITE_NAMES = ("ingest", "transform", "export_csv", "audit_log")

_CALL_SITE_TUPLE_HANDLING_PATTERN = re.compile(
    r"\b(?:unpack(?:s|ed|ing)?|destructur\w*|capture|assign|use|check|inspect|handle|"
    r"update|adapt|adjust|modify)\b.{0,120}\b(?:is_valid|reason)\b|"
    r"\b(?:is_valid|reason)\b.{0,120}\b(?:unpack(?:s|ed|ing)?|destructur\w*|capture|"
    r"assign|use|check|inspect|handle|update|adapt|adjust|modify)\b",
    re.IGNORECASE | re.DOTALL,
)

_RETRY_BOUND_PATTERNS = [
    re.compile(
        r"\b(?:retry|retries|attempt|attempts)\s+"
        r"(?:up\s+to\s+|at\s+most\s+|no\s+more\s+than\s+)?\d+\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:up\s+to|at\s+most|no\s+more\s+than|max(?:imum)?(?:\s+of)?)\s+"
        r"\d+\s+(?:retry|retries|attempt|attempts|time|times)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b\d+\s+(?:retry|retries|attempt|attempts|tries|time|times)\b",
        re.IGNORECASE,
    ),
]

_RETRY_EXHAUSTION_PATTERN = re.compile(
    r"\b(?:"
    r"(?:all\s+)?(?:retries|(?:retry\s+)?attempts?)\s+"
    r"(?:(?:is|are|were|have\s+been|has\s+been)\s+)?exhausted|"
    r"(?:retry|retries|attempts?)\s+exhaustion|"
    r"after\s+all\s+(?:retry\s+)?attempts?"
    r"(?:\s+(?:(?:have|has|are|were)\s+)?"
    r"(?:fail(?:s|ed)?|exhausted))?|"
    r"after\s+all\s+retries"
    r"(?:\s+(?:(?:have|has|are|were)\s+)?"
    r"(?:fail(?:s|ed)?|exhausted))?|"
    r"after\s+\d+\s+(?:failed\s+)?(?:retry\s+)?attempts?|"
    r"all\s+(?:retry\s+)?attempts?\s+"
    r"(?:(?:have|has|are|were)\s+)?fail(?:s|ed)?|"
    r"all\s+\d+\s+(?:retry\s+)?attempts?\s+"
    r"(?:(?:have|has|are|were)\s+)?fail(?:s|ed)?"
    r"(?:\s+due\s+to\s+(?:(?:an?|the)\s+)?"
    r"(?:[\w-]+\s+){0,4}?(?:errors?|exceptions?|failures?))?|"
    r"(?:if|when)\s+[\w\s]+fail(?:s|ed)?\s+on\s+(?:the\s+)?"
    r"\d+(?:st|nd|rd|th)\s+attempt|"
    r"(?:if|when)\s+(?:the\s+)?\d+(?:st|nd|rd|th)\s+attempt\s+"
    r"(?:(?:also|still)\s+)?fail(?:s|ed)?"
    r"(?:\s+with\s+(?:(?:a|an|the)\s+)?(?:connection\s+)?"
    r"(?:error|exception|failure))?|"
    r"(?:if|when)\s+(?:the\s+)?(?:connection\s+)?"
    r"(?:error|exception|failure)\s+(?:still\s+)?"
    r"(?:persist(?:s|ed)?|remain(?:s|ed)?)\s+after\s+(?:the\s+)?"
    r"\d+(?:st|nd|rd|th)\s+(?:retry\s+)?attempt|"
    r"once\s+(?:the\s+)?(?:max(?:imum)?\s+)?(?:retry\s+)?attempts?\s+"
    r"(?:is\s+|are\s+)?(?:reached|exhausted)|"
    r"(?:once|when|if)\s+(?:the\s+)?max(?:imum)?\s+number\s+of\s+attempts?\s+"
    r"(?:is\s+|are\s+|has\s+been\s+)?(?:reached|exceeded|exhausted)|"
    r"(?:retry\s+)?limit\s+(?:is\s+|has\s+been\s+)?(?:reached|exceeded)|"
    r"(?:final|last)\s+(?:retry\s+)?attempt"
    r"(?:\s+(?:(?:also|still)\s+)?(?:"
    r"fail(?:s|ed)?(?:\s+with\s+(?:(?:a|an|the)\s+)?"
    r"(?:connection\s+)?(?:error|exception|failure))?|"
    r"(?:encounters?|raises?|has)\s+(?:(?:a|an|the)\s+)?"
    r"(?:connection\s+)?(?:error|exception|failure)))?|"
    r"if\s+(?:it\s+)?still\s+fail(?:s|ed)?|"
    r"when\s+(?:all\s+)?(?:retry\s+)?attempts?\s+fail|"
    r"stop\s+retrying|"
    r"(?:do\s+not|don['’]t|must\s+not|mustn['’]t)\s+"
    r"(?:retry(?:\s+again)?|continue\s+retrying)"
    r")\b",
    re.IGNORECASE,
)

_NON_EXHAUSTION_PREFIX_PATTERN = re.compile(
    r"(?:\bbefore|\bunless|\bprior\s+to|\bnot|\bexcept(?:\s+when)?|"
    r"\b(?:fewer|less)\s+than)\s*$",
    re.IGNORECASE,
)

_UNTIL_EXHAUSTION_PREFIX_PATTERN = re.compile(r"\buntil\s*$", re.IGNORECASE)

_RETRY_UNTIL_PREFIX_PATTERN = re.compile(
    r"\bretry(?:ing)?\s+until\s*$",
    re.IGNORECASE,
)

_STOP_RETRYING_EXHAUSTION_PATTERN = re.compile(
    r"(?:do\s+not|don['’]t|must\s+not|mustn['’]t)\s+"
    r"(?:retry(?:\s+again)?|continue\s+retrying)",
    re.IGNORECASE,
)

_CONDITIONAL_UNIT_PATTERN = re.compile(
    r"^\s*(?:if|when|unless|before|until|on|upon|in\s+case|provided\s+that|"
    r"for\s+(?:(?:an?\s+)?(?:invalid|malformed|bad|unsupported|non[- ]?retryable)\b|"
    r"(?:auth(?:entication|orization)?|validation)\s+(?:failure|error)\b))",
    re.IGNORECASE,
)

_RETRY_UNIT_PATTERN = re.compile(r"[^,;.!?]+(?:[,;.!?]+|$)", re.DOTALL)

_RETRY_CONTINUATION_PATTERN = re.compile(
    r"\b(?:keep(?:s|ing)?|continu(?:e|es|ed|ing)|resum(?:e|es|ed|ing))\s+"
    r"(?:(?:to|with)\s+)?(?:retry(?:ing)?|retries)\b|"
    r"\btry\s+again\b|"
    r"\banother\s+(?:retry\s+)?attempt\b|"
    r"\b(?:continu(?:e|es|ed|ing)|resum(?:e|es|ed|ing)|proceed(?:s|ed|ing)?)\s+"
    r"(?:processing\s+)?normally\b",
    re.IGNORECASE,
)

_REJECTED_ACTION_PATTERN = re.compile(
    r"(?:"
    r"\bunder\s+no\s+circumstances\b|"
    r"\b(?:do|does|did|must|should|shall|will|would|can|could|may|might)\s+"
    r"not\b|"
    r"\b(?:mustn|shouldn|shan|won|wouldn|can|couldn|mayn|mightn)['’]t\b|"
    r"\bcannot\b|"
    r"\bnever\b|"
    r"\bavoid(?:s|ed|ing)?\b|"
    r"\bwithout\b|"
    r"\brefrain(?:s|ed|ing)?\s+from\b|"
    r"\bno\s+(?:error|exception|failure)\b|"
    r"\b(?:forbidden|prohibited|disallowed|not\s+allowed|not\s+permitted)\b"
    r")",
    re.IGNORECASE | re.DOTALL,
)

_SUCCESS_RETURN_PATTERN = re.compile(
    r"\breturn(?:s|ed|ing)?\s+(?:(?:a|an|the)\s+)?"
    r"(?:success(?:ful(?:ly)?)?|ok(?:ay)?|true|normally)\b",
    re.IGNORECASE,
)

_CONNECTIVE_ONLY_PATTERN = re.compile(
    r"^\s*(?:then|(?:and|but)\s+then|otherwise|however|but|nevertheless|"
    r"as\s+(?:a|the)\s+fallback)?\s*$",
    re.IGNORECASE,
)

_ACTION_ADVERBS = (
    r"(?:(?:immediately|gracefully|clearly|explicitly|directly|finally)\s+)*"
)
_ACTION_INTRO = (
    r"(?:(?:then|otherwise|as\s+(?:a|the)\s+fallback|stop\s+retrying\s+and)\s+)?"
)
_DIRECT_ACTION_PATTERNS = tuple(
    re.compile(rf"^\s*{_ACTION_INTRO}{_ACTION_ADVERBS}{body}\s*$", re.IGNORECASE)
    for body in (
        r"(?:re[- ]?)?rais(?:e|ed)\b.{0,96}",
        r"(?:surface|propagate|abort|skip)\b.{0,96}",
        r"return\b.{0,64}\b(?:error|exception|failure)\b.{0,32}",
        r"log\b.{0,64}\b(?:error|exception|failure)\b.{0,32}",
        r"fail\s+with\b.{0,64}\b(?:error|exception|failure)\b.{0,32}",
        r"use\b.{1,80}\bas\s+(?:the\s+)?fallback\b.{0,32}",
        r"(?:fallback|fall\s+back)\s+to\b.{1,80}",
        r"fail\s+closed\b.{0,64}",
        r"allow\b.{1,64}\bto\s+(?:surface|propagate|abort|skip)\b.{0,64}",
    )
)
_MODAL_PREFIX_PATTERN = re.compile(
    rf"^\s*{_ACTION_INTRO}(?:(?:the|a|an|this|that)\s+)?"
    rf"(?:[\w`.-]+\s+){{1,8}}"
    rf"(?:(?:is|are)\s+required\s+to\s+{_ACTION_ADVERBS}|"
    rf"(?:needs?|ought)\s+to\s+{_ACTION_ADVERBS}|"
    rf"(?:must|should|shall|will|would|can|could|may|might)\s+"
    rf"{_ACTION_ADVERBS}(?:be\s+{_ACTION_ADVERBS})?|"
    rf"(?:has|have)\s+to\s+{_ACTION_ADVERBS}|(?:is|are)\s+{_ACTION_ADVERBS})"
    r"(?P<action>.+?)\s*$",
    re.IGNORECASE | re.DOTALL,
)

_INVERSE_EXHAUSTION_PATTERN = re.compile(
    r"^\s*(?:when|once|after)\s+(?:"
    r"(?:the\s+)?(?:max(?:imum)?\s+)?(?:retry\s+)?(?:attempts?|retries)\s+"
    r"(?:(?:is|are|have\s+been|has\s+been)\s+)?(?:exhausted|fail(?:s|ed)?)|"
    r"all\s+(?:retry\s+)?(?:attempts?|retries)\s+"
    r"(?:(?:are|have\s+been)\s+)?(?:exhausted|fail(?:s|ed)?)|"
    r"all\s+\d+\s+(?:retry\s+)?(?:attempts?|retries)\s+"
    r"(?:(?:(?:are|have\s+been)\s+)?exhausted|"
    r"(?:(?:are|have\s+been)\s+)?fail(?:s|ed)?"
    r"(?:\s+due\s+to\s+(?:(?:an?|the)\s+)?"
    r"(?:[\w-]+\s+){0,4}?(?:errors?|exceptions?|failures?))?)|"
    r"(?:the\s+)?(?:retry\s+)?limit\s+"
    r"(?:(?:is|has\s+been)\s+)?(?:reached|exceeded|exhausted)|"
    r"(?:the\s+)?max(?:imum)?\s+number\s+of\s+attempts?\s+"
    r"(?:(?:is|has\s+been)\s+)?(?:reached|exceeded|exhausted)|"
    r"(?:the\s+)?(?:connection\s+)?(?:error|exception|failure)\s+"
    r"(?:still\s+)?(?:persists?|remains?)\s+after\s+(?:the\s+)?"
    r"\d+(?:st|nd|rd|th)\s+(?:retry\s+)?attempt|"
    r"(?:the\s+)?\d+(?:st|nd|rd|th)\s+(?:retry\s+)?attempt\s+"
    r"(?:(?:also|still)\s+)?fails?"
    r")\s*$",
    re.IGNORECASE,
)


def _judge_call_site_names(prompt_output: str) -> JudgmentResult:
    """Check that every named call site is told to handle the new tuple."""
    missing = [
        name
        for name in CALL_SITE_NAMES
        if not re.search(rf"\b{re.escape(name)}\b", prompt_output)
    ]
    if missing:
        return JudgmentResult(
            passed=False,
            reasoning="Missing required call-site name(s): " + ", ".join(missing),
        )
    if not _CALL_SITE_TUPLE_HANDLING_PATTERN.search(prompt_output):
        return JudgmentResult(
            passed=False,
            reasoning=(
                "Missing instructions for callers to handle the new "
                "(is_valid, reason) tuple."
            ),
        )
    return JudgmentResult(
        passed=True,
        reasoning="All required call-site names and tuple-handling instructions are present.",
    )


def _judge_retry_bound(prompt_output: str) -> JudgmentResult:
    """Check that retry guidance has an explicit numeric limit."""
    if any(pattern.search(prompt_output) for pattern in _RETRY_BOUND_PATTERNS):
        return JudgmentResult(
            passed=True,
            reasoning="A numeric retry limit is present.",
        )
    return JudgmentResult(
        passed=False,
        reasoning="No explicit numeric retry limit found.",
    )


def _retry_units(prompt_output: str) -> tuple[str, ...]:
    """Split prose into ordered comma, semicolon, and sentence units."""
    return tuple(
        match.group(0).rstrip(" ,;.!?\t\r\n").strip()
        for match in _RETRY_UNIT_PATTERN.finditer(prompt_output)
        if match.group(0).rstrip(" ,;.!?\t\r\n").strip()
    )


def _fallback_action_state(text: str) -> tuple[bool, bool]:
    """Classify one self-contained action unit as affirmative or rejected."""
    text = text.strip(" ,;:.!?\t\r\n")
    if _RETRY_CONTINUATION_PATTERN.search(text):
        return False, True
    if _SUCCESS_RETURN_PATTERN.search(text):
        return False, True
    if _REJECTED_ACTION_PATTERN.search(text):
        return False, True

    candidates = [text]
    coordinated = re.split(r"\band\b", text, flags=re.IGNORECASE)[-1].strip()
    if coordinated != text:
        candidates.append(coordinated)
    for candidate in tuple(candidates):
        modal = _MODAL_PREFIX_PATTERN.fullmatch(candidate)
        if modal:
            candidates.append(modal.group("action"))
    affirmative = any(
        pattern.fullmatch(candidate)
        for candidate in candidates
        for pattern in _DIRECT_ACTION_PATTERNS
    )
    return affirmative, False


def _inverse_action_state(unit: str) -> tuple[bool, bool]:
    """Classify only a self-contained ``ACTION when EXHAUSTED`` unit."""
    connectors = tuple(re.finditer(r"\b(?:when|once|after)\b", unit, re.IGNORECASE))
    for connector in reversed(connectors):
        condition = unit[connector.start() :].strip()
        if not _INVERSE_EXHAUSTION_PATTERN.fullmatch(condition):
            continue
        action_text = unit[: connector.start()].strip()
        action, rejected = _fallback_action_state(action_text)
        return action, rejected
    return False, False


def _is_immediate_contradiction(units: tuple[str, ...], index: int) -> bool:
    """Return whether the unit immediately after an action contradicts it."""
    next_index = index + 1
    while next_index < len(units) and _CONNECTIVE_ONLY_PATTERN.fullmatch(
        units[next_index]
    ):
        next_index += 1
    if next_index >= len(units):
        return False
    _, rejected = _fallback_action_state(units[next_index])
    return rejected


def _has_affirmative_exhaustion(text: str) -> bool:
    """Return whether *text* names exhaustion without negating or preposing it."""
    return any(
        _is_affirmative_exhaustion_match(text, match)
        and not _STOP_RETRYING_EXHAUSTION_PATTERN.fullmatch(match.group())
        for match in _RETRY_EXHAUSTION_PATTERN.finditer(text)
    )


def _is_affirmative_exhaustion_match(text: str, match: re.Match[str]) -> bool:
    """Bind one exhaustion phrase to affirmative local temporal context."""
    prefix = text[: match.start()]
    if _NON_EXHAUSTION_PREFIX_PATTERN.search(prefix):
        return False
    if _UNTIL_EXHAUSTION_PREFIX_PATTERN.search(prefix):
        return bool(
            _RETRY_CONTINUATION_PATTERN.search(prefix)
            or _RETRY_UNTIL_PREFIX_PATTERN.search(prefix)
        )
    return True


def _previous_meaningful_unit(units: tuple[str, ...], index: int) -> str | None:
    """Return the prior non-connective unit, if one exists."""
    previous = index - 1
    while previous >= 0 and _CONNECTIVE_ONLY_PATTERN.fullmatch(units[previous]):
        previous -= 1
    return units[previous] if previous >= 0 else None


def _stop_exhaustion_has_retry_context(
    units: tuple[str, ...], index: int, unit_prefix: str
) -> bool:
    """Reject stop-only guidance inherited from an unrelated conditional branch."""
    if unit_prefix.strip() and not _has_affirmative_exhaustion(unit_prefix):
        return False
    previous = _previous_meaningful_unit(units, index)
    if previous is None or not _CONDITIONAL_UNIT_PATTERN.match(previous):
        return True
    return _has_affirmative_exhaustion(previous)


def _judge_retry_fallback(prompt_output: str) -> JudgmentResult:
    """Check that retry exhaustion has explicit fallback behavior."""
    units = _retry_units(prompt_output)
    has_exhaustion = False
    has_action = False
    for index, unit in enumerate(units):
        for exhaustion in _RETRY_EXHAUSTION_PATTERN.finditer(unit):
            prefix = unit[: exhaustion.start()]
            if not _is_affirmative_exhaustion_match(unit, exhaustion):
                continue
            if _STOP_RETRYING_EXHAUSTION_PATTERN.fullmatch(exhaustion.group()) and not (
                _stop_exhaustion_has_retry_context(units, index, prefix)
            ):
                continue
            has_exhaustion = True
            suffix = unit[exhaustion.end() :]
            action, rejected = _fallback_action_state(suffix)
            if (
                action
                and not rejected
                and not _is_immediate_contradiction(units, index)
            ):
                has_action = True
                break
            action, rejected = _inverse_action_state(unit)
            if (
                action
                and not rejected
                and not _is_immediate_contradiction(units, index)
            ):
                has_action = True
                break
            if rejected or suffix.strip():
                continue
            action_index = index + 1
            while action_index < len(units) and _CONNECTIVE_ONLY_PATTERN.fullmatch(
                units[action_index]
            ):
                action_index += 1
            if action_index >= len(units):
                continue
            action, rejected = _fallback_action_state(units[action_index])
            if (
                action
                and not rejected
                and not _is_immediate_contradiction(units, action_index)
            ):
                has_action = True
                break
        if has_action:
            break

    if has_exhaustion and has_action:
        return JudgmentResult(
            passed=True,
            reasoning="Retry exhaustion and fallback behavior are both present.",
        )
    missing = []
    if not has_exhaustion:
        missing.append("retry exhaustion condition")
    if not has_action:
        missing.append("fallback action")
    return JudgmentResult(
        passed=False,
        reasoning="Missing " + " and ".join(missing) + ".",
    )


# ---------------------------------------------------------------------------
# Test inputs
# ---------------------------------------------------------------------------

CALL_SITE_INPUT_PROMPT = """\
Build a Python module that processes data records.

The module must contain:
- A helper function `validate_record(record)` that returns True if the record
  is valid, False otherwise.
- Four pipeline functions that each call `validate_record`:
  1. `ingest(records)` — filters out invalid records before ingestion.
  2. `transform(records)` — skips invalid records during transformation.
  3. `export_csv(records)` — warns on invalid records while exporting.
  4. `audit_log(records)` — logs invalid records for compliance review.
"""

CALL_SITE_INPUT_CODE = """\
def validate_record(record):
    return bool(record.get("id") and record.get("name"))

def ingest(records):
    return [r for r in records if validate_record(r)]

def transform(records):
    out = []
    for r in records:
        if not validate_record(r):
            continue
        out.append({**r, "name": r["name"].upper()})
    return out

def export_csv(records):
    import csv, io
    buf = io.StringIO()
    w = csv.DictWriter(buf, fieldnames=["id", "name"])
    w.writeheader()
    for r in records:
        if not validate_record(r):
            print(f"WARN: skipping invalid record {r}")
            continue
        w.writerow(r)
    return buf.getvalue()

def audit_log(records):
    for r in records:
        if not validate_record(r):
            print(f"AUDIT: invalid record detected: {r}")
"""

CALL_SITE_CHANGE_PROMPT = """\
Change `validate_record` to return a tuple `(is_valid, reason)` instead of a
plain bool. `reason` should be a string explaining why validation failed
(empty string when valid).
"""

RETRY_INPUT_PROMPT = """\
Build a Python data-import pipeline with three steps:
1. `fetch_data(url)` — downloads JSON from a URL.
2. `parse_data(raw)` — parses the JSON into records.
3. `load_data(records, db)` — inserts records into a database.

The pipeline runner `run_pipeline(url, db)` calls these in sequence.
"""

RETRY_INPUT_CODE = """\
import json, urllib.request

def fetch_data(url):
    with urllib.request.urlopen(url) as resp:
        return resp.read().decode()

def parse_data(raw):
    return json.loads(raw)

def load_data(records, db):
    for r in records:
        db.insert(r)

def run_pipeline(url, db):
    raw = fetch_data(url)
    records = parse_data(raw)
    load_data(records, db)
"""

RETRY_CHANGE_PROMPT = """\
When `fetch_data` raises a connection error, retry from the beginning of the
pipeline.
"""


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class TestDeterministicChangeJudges:
    """Unit coverage for release-gate judges used by the real LLM tests."""

    def test_change_prompt_requires_call_site_safety_in_final_prompt(self) -> None:
        """The final prompt contract must carry call-site adaptations forward."""
        template = Path("pdd/prompts/change_LLM.prompt").read_text(encoding="utf-8")

        assert "final modified_prompt itself" in template
        assert "name every affected call site" in template
        assert "how each caller must adapt" in template

    def test_change_prompt_requires_retry_safety_in_final_prompt(self) -> None:
        template = Path("pdd/prompts/change_LLM.prompt").read_text(encoding="utf-8")

        assert "final modified_prompt itself" in template
        assert "concrete numeric retry limit" in template
        assert "maximum of 3 attempts" in template
        assert "after all attempts fail" in template

    def test_call_site_judge_requires_all_names(self) -> None:
        judgment = _judge_call_site_names(
            "Update ingest, transform, export_csv, and audit_log so each "
            "caller unpacks (is_valid, reason) and checks is_valid."
        )
        assert judgment.passed

        missing = _judge_call_site_names(
            "Update ingest, transform, and export_csv so each caller "
            "unpacks (is_valid, reason)."
        )
        assert not missing.passed
        assert "audit_log" in missing.reasoning

    def test_call_site_judge_rejects_name_only_output(self) -> None:
        unchanged = _judge_call_site_names(CALL_SITE_INPUT_PROMPT)
        assert not unchanged.passed
        assert "tuple" in unchanged.reasoning

        copied_inputs = _judge_call_site_names(
            CALL_SITE_INPUT_PROMPT + "\n" + CALL_SITE_CHANGE_PROMPT
        )
        assert not copied_inputs.passed
        assert "tuple" in copied_inputs.reasoning

    def test_call_site_judge_accepts_inflected_unpack_before_tuple_name(self) -> None:
        judgment = _judge_call_site_names(
            "ingest, transform, export_csv, and audit_log each call validate_record. "
            "Each caller unpacks the result and branches on is_valid."
        )

        assert judgment.passed

        unpacked = _judge_call_site_names(
            "ingest, transform, export_csv, and audit_log each call validate_record. "
            "Each caller unpacked the result and checked is_valid."
        )
        assert unpacked.passed

        unpackable = _judge_call_site_names(
            "ingest, transform, export_csv, and audit_log see an unpackable result. "
            "Callers remain unchanged around is_valid."
        )
        assert not unpackable.passed

        unpackaged = _judge_call_site_names(
            "ingest, transform, export_csv, and audit_log receive unpackaged "
            "is_valid metadata, with no caller changes."
        )
        assert not unpackaged.passed

    def test_retry_bound_judge_requires_numeric_limit(self) -> None:
        judgment = _judge_retry_bound("Retry up to 3 times before failing.")
        assert judgment.passed

        missing = _judge_retry_bound("Retry with exponential backoff before failing.")
        assert not missing.passed
        assert "numeric" in missing.reasoning

    def test_retry_fallback_judge_requires_exhaustion_and_action(self) -> None:
        judgment = _judge_retry_fallback(
            "After all retry attempts are exhausted, raise a clear error."
        )
        assert judgment.passed

        ordinal = _judge_retry_fallback(
            "If the pipeline fails on the 3rd attempt, stop retrying and "
            "raise the final connection exception."
        )
        assert ordinal.passed

        ordinal_subject = _judge_retry_fallback(
            "If the 3rd attempt also fails with a connection error, allow "
            "the exception to propagate."
        )
        assert ordinal_subject.passed

        negated_failure = _judge_retry_fallback(
            "Retry up to 3 times. If the 3rd attempt does not fail, return success."
        )
        assert not negated_failure.passed

        negated_action = _judge_retry_fallback(
            "If the 3rd attempt succeeds, do not fail the operation; return success."
        )
        assert not negated_action.passed

        final_attempt = _judge_retry_fallback(
            "Retry up to 3 times. If the final attempt still encounters a "
            "connection error, re-raise the exception."
        )
        assert final_attempt.passed

        retry_limit = _judge_retry_fallback(
            "Use a maximum of 3 attempts and return an error when the retry "
            "limit is reached."
        )
        assert retry_limit.passed

        numeric_all_attempts = _judge_retry_fallback(
            "If all 3 attempts fail, the final connection error must be "
            "raised to the caller."
        )
        assert numeric_all_attempts.passed

        missing = _judge_retry_fallback("Retry up to 3 times.")
        assert not missing.passed
        assert "exhaust" in missing.reasoning

    def test_retry_fallback_judge_accepts_all_attempts_failure_cause_tail(
        self,
    ) -> None:
        """A bounded failure cause may precede the explicit fallback action."""
        judgment = _judge_retry_fallback(
            "If all 3 attempts fail due to connection errors, run_pipeline "
            "must propagate the final connection error to the caller."
        )

        assert judgment.passed, judgment.reasoning

    @pytest.mark.parametrize(
        "guidance",
        (
            (
                "Propagate the final connection error when all 3 attempts "
                "fail due to connection errors."
            ),
            (
                "Raise the final error after all 3 attempts fail due to a "
                "transient connection error."
            ),
        ),
    )
    def test_retry_fallback_judge_accepts_inverse_failure_cause_tail(
        self, guidance: str
    ) -> None:
        """A bounded failure cause also supports action-first word order."""
        judgment = _judge_retry_fallback(guidance)

        assert judgment.passed, judgment.reasoning

    @pytest.mark.parametrize(
        "guidance",
        (
            "If all 3 attempts fail due to connection errors, keep retrying.",
            (
                "If all 3 attempts fail due to connection errors, the final "
                "connection error remains available for inspection."
            ),
            "If all 3 attempts fail due to connection errors, return success.",
            (
                "If all 3 attempts fail due to connection errors, run_pipeline "
                "must not propagate the final connection error."
            ),
            (
                "Do not propagate the final connection error when all 3 attempts "
                "fail due to connection errors."
            ),
            (
                "Keep retrying when all 3 attempts fail due to connection errors."
            ),
            (
                "The final connection error remains available for inspection when "
                "all 3 attempts fail due to connection errors."
            ),
            "Return success after all 3 attempts fail due to connection errors.",
            (
                "Propagate the final connection error when all 3 attempts fail due "
                "to connection errors. Keep retrying."
            ),
            (
                "Propagate the final connection error when not all 3 attempts fail "
                "due to connection errors."
            ),
        ),
    )
    def test_retry_fallback_judge_rejects_cause_tail_without_fallback(
        self, guidance: str
    ) -> None:
        """A failure cause does not weaken fallback-action requirements."""
        judgment = _judge_retry_fallback(guidance)

        assert not judgment.passed

    @pytest.mark.parametrize(
        "guidance",
        (
            (
                "The runner must allow for a maximum of 3 attempts. If the "
                "connection error persists after the 3rd attempt, run_pipeline "
                "must raise the exception to the user."
            ),
            "If the error remains after the 3rd attempt, raise it.",
            "When the exception persists after the 4th retry attempt, abort.",
            "When the exception remains after the 4th attempt, surface it.",
            "If failure persists after the 2nd attempt, return an error result.",
            "If the failure remains after the 2nd retry attempt, propagate it.",
            "After all retry attempts are exhausted. Raise the final error.",
        ),
    )
    def test_retry_fallback_judge_accepts_persistent_ordinal_failure(
        self, guidance: str
    ) -> None:
        """Persistent failure at the final ordinal attempt is exhaustion."""
        judgment = _judge_retry_fallback(guidance)

        assert judgment.passed, judgment.reasoning

    @pytest.mark.parametrize(
        "guidance",
        (
            "If the error remains after the 3rd attempt; as a fallback, return an error result.",
            "If the error remains after the 3rd attempt, as a fallback, return an error.",
            "If the error remains after the 3rd attempt. As a fallback, return an error.",
            "If all retry attempts are exhausted, fail with a clear error.",
            "If all retry attempts are exhausted; use cached data as the fallback.",
            "If all retry attempts are exhausted. Fallback to cached data.",
            "Raise the final error when retries are exhausted.",
            "Re-raise the exception when all retry attempts are exhausted!",
            "Propagate the exception once the maximum retry attempts are exhausted.",
            "Surface a clear error when all retry attempts fail.",
            "Abort the operation after all retries are exhausted.",
            "Skip the record when the retry limit is reached.",
            "Log the final error when all retry attempts fail.",
            "Return an error result when retries are exhausted.",
        ),
    )
    def test_retry_fallback_judge_preserves_explicit_fallback_grammar(
        self, guidance: str
    ) -> None:
        """Explicit fallback actions remain valid across punctuation forms."""
        judgment = _judge_retry_fallback(guidance)

        assert judgment.passed, judgment.reasoning

    @pytest.mark.parametrize(
        "guidance",
        (
            (
                "If the connection error does not persist after the 3rd "
                "attempt, return success."
            ),
            "If the connection error persists after the 3rd attempt, keep retrying.",
            "If all 3 attempts fail, keep retrying.",
            (
                "If all 3 attempts fail, the final connection error remains "
                "available for inspection."
            ),
            "If all 3 attempts fail, fallback diagnostics remain available.",
            (
                "If fetch_data raises a connection error, retry from the "
                "beginning. Use a maximum of 3 attempts. If the connection "
                "error persists after the 3rd attempt, keep retrying."
            ),
            (
                "Use a maximum of 3 attempts. If the connection error persists "
                "after the 3rd attempt, return success."
            ),
            (
                "Use a maximum of 3 attempts. If the connection error persists "
                "after the 3rd attempt, do not raise it; keep retrying."
            ),
            (
                "Use a maximum of 3 attempts. If the connection error persists "
                "after the 3rd attempt, avoid raising the exception."
            ),
            (
                "Log each fetch attempt for diagnostics. Use a maximum of 3 "
                "attempts. If the connection error persists after the 3rd "
                "attempt, keep retrying."
            ),
            (
                "Log each fetch attempt for diagnostics. Use a maximum of 3 "
                "attempts. If the connection error persists after the 3rd "
                "attempt."
            ),
            (
                "Use a maximum of 3 attempts. If the connection error persists "
                "after the 3rd attempt, keep retrying. Separately, log request "
                "metrics."
            ),
            (
                "If fetch_data raises a connection error and if the connection "
                "error persists after the 3rd attempt."
            ),
            (
                "If the connection error persists after the 3rd attempt, under "
                "no circumstances should the runner raise the final error."
            ),
            (
                "If the connection error persists after the 3rd attempt; the "
                "runner mustn't raise the final error."
            ),
            (
                "If the connection error persists after the 3rd attempt. The "
                "runner cannot raise the final error."
            ),
            (
                "If the connection error persists after the 3rd attempt, do not "
                "raise the final error."
            ),
            (
                "If the connection error persists after the 3rd attempt; avoid "
                "raising the final error."
            ),
            (
                "If the connection error persists after the 3rd attempt. Continue "
                "without raising the final error."
            ),
            (
                "If the connection error persists after the 3rd attempt. Continue "
                "processing normally. Record the final error in logs for later "
                "inspection."
            ),
            (
                "If the connection error persists after the 3rd attempt; continue "
                "normally, then log request metrics."
            ),
            (
                "If the connection error persists after the 3rd attempt. Return "
                "success."
            ),
            (
                "If the connection error persists after the 3rd attempt and if "
                "fetch_data raises another connection error."
            ),
            (
                "If the connection error persists after the 3rd attempt; inspect "
                "the request metrics; log the final error."
            ),
        ),
    )
    def test_retry_fallback_judge_rejects_non_fallback_conditions(
        self, guidance: str
    ) -> None:
        """Failure state alone, negation, or continued retry is no fallback."""
        judgment = _judge_retry_fallback(guidance)

        assert not judgment.passed

    @pytest.mark.parametrize(
        "guidance",
        (
            "Log parsing error when validation fails; if retries are exhausted, "
            "keep retrying.",
            "If retries are exhausted, raising the exception is forbidden.",
            "Raise no error when retries are exhausted.",
            "If retries are exhausted, logs indicate an error.",
            "If retries are exhausted. Raise an error. Keep retrying.",
            "Log the parsing error when validation fails; if all retry attempts "
            "are exhausted, keep retrying.",
            "If all retry attempts are exhausted, raising the exception is forbidden.",
            "If all retry attempts are exhausted, raising the exception is prohibited.",
            "Raise no error when all retry attempts are exhausted.",
            "If all retry attempts are exhausted, logs indicate an error.",
            "If all retry attempts are exhausted. Raise the final error. Keep retrying.",
            "If all retry attempts are exhausted, immediately raise no error.",
            "If all retry attempts are exhausted, raise the final error under no circumstances.",
            "If all retry attempts are exhausted, raise the final error without surfacing it.",
            "If all retry attempts are exhausted, raise the final error; continue normally.",
            "If all retry attempts are exhausted. Raise the final error. Return success.",
            "If all retry attempts are exhausted. Raise the final error; continue retrying.",
        ),
    )
    def test_retry_fallback_judge_rejects_postposed_negation_and_contradiction(
        self, guidance: str
    ) -> None:
        """Negation and immediate contradictions dominate an apparent action."""
        judgment = _judge_retry_fallback(guidance)

        assert not judgment.passed

    @pytest.mark.parametrize(
        "guidance",
        (
            "If all retry attempts are exhausted, immediately raise the error.",
            "If all retry attempts are exhausted, the runner must immediately raise the error.",
            "If all retry attempts are exhausted, gracefully abort the operation.",
            "Immediately re-raise the exception when all retry attempts are exhausted.",
            "The runner must gracefully propagate the error once retries are exhausted.",
            "Surface a clear error immediately after all retry attempts are exhausted.",
            "When all retry attempts fail, immediately return an error result.",
            "When all retry attempts fail, clearly log the final error.",
            "When the retry limit is reached, gracefully use cached data as the fallback.",
            "After all retries are exhausted; fall back to cached data.",
        ),
    )
    def test_retry_fallback_judge_accepts_modal_and_adverbial_actions(
        self, guidance: str
    ) -> None:
        """Bounded modal and adverb prefixes preserve affirmative actions."""
        judgment = _judge_retry_fallback(guidance)

        assert judgment.passed, judgment.reasoning

    @pytest.mark.parametrize(
        "guidance",
        (
            "After all attempts fail, raise the final error.",
            "After all retries fail, return an error.",
            "If the final attempt still encounters a connection error re-raise the exception.",
            "Do not retry again; raise the final error.",
            "Do not continue retrying and raise the final error.",
            "If retries are exhausted, the runner is required to raise the error.",
            "If retries are exhausted, the runner needs to raise the error.",
            "If retries are exhausted, the runner ought to raise the error.",
            "Keep retrying until all retries are exhausted; then raise the error.",
            "Retry up to 3 times. Retry until all attempts are exhausted; then raise the error.",
            "Retry up to 3 times. For safety, do not retry again; raise the error.",
        ),
    )
    def test_retry_fallback_judge_accepts_canonical_exhaustion_forms(
        self, guidance: str
    ) -> None:
        """Canonical stop conditions retain an explicit fallback action."""
        judgment = _judge_retry_fallback(guidance)

        assert judgment.passed, judgment.reasoning

    @pytest.mark.parametrize(
        "guidance",
        (
            "Retry 3 times. When the user is exhausted, return an error.",
            "If retries are exhausted, the runner must log request metrics.",
            "If retries are exhausted, the runner should use the normal result.",
            "If retries are exhausted. Raise the error. Then, keep retrying.",
            "If retries are exhausted. Raise the error. Otherwise, continue normally.",
            "If retries are exhausted. Raise the error. However, keep retrying.",
            "Before all retries are exhausted, raise the error.",
            "Unless retries are exhausted, raise the error.",
            "If not all attempts fail, raise the error.",
            "Prior to retry exhaustion, return an error.",
            "Retry 3 times. If authentication fails, do not retry; raise an auth error.",
            "Retry 3 times. If input is invalid, must not retry; raise a validation error.",
            "Retry 3 times. For invalid input, must not retry; return a validation error.",
            "Retry 3 times. On auth failure, do not retry; return an auth error.",
            "Retry 3 times. For invalid input. Then. Must not retry; return an error.",
            "Except when retries are exhausted, raise the error.",
            "Fewer than all retries are exhausted, raise the error.",
            "If retries are exhausted. Raise the error. And then. Keep retrying.",
            "If retries are exhausted. Raise the error. But then. Keep retrying.",
            "If retries are exhausted. Raise the error. Nevertheless. Keep retrying.",
        ),
    )
    def test_retry_fallback_judge_rejects_unrelated_or_deferred_actions(
        self, guidance: str
    ) -> None:
        """Unrelated subjects and connective-hidden contradictions are rejected."""
        judgment = _judge_retry_fallback(guidance)

        assert not judgment.passed

    @pytest.mark.parametrize("action_before", (False, True))
    @pytest.mark.parametrize("same_clause", (False, True))
    @pytest.mark.parametrize("negated", (False, True))
    @pytest.mark.parametrize("contradiction", (False, True))
    def test_retry_fallback_clause_state_cross_product(
        self,
        action_before: bool,
        same_clause: bool,
        negated: bool,
        contradiction: bool,
    ) -> None:
        """Pairing, order, negation, and contradiction define acceptance."""
        action = (
            "must not raise the final error"
            if negated
            else "must immediately raise the final error"
        )
        if same_clause and action_before:
            guidance = f"The runner {action} when all retry attempts are exhausted."
        elif same_clause:
            guidance = f"When all retry attempts are exhausted, the runner {action}."
        elif action_before:
            guidance = f"The runner {action}. When all retry attempts are exhausted."
        else:
            guidance = f"When all retry attempts are exhausted. The runner {action}."
        if contradiction:
            guidance += " Keep retrying."

        judgment = _judge_retry_fallback(guidance)

        expected = (
            not negated and not contradiction and (same_clause or not action_before)
        )
        assert judgment.passed is expected, guidance


@pytest.mark.real
class TestCallSiteEnumeration:
    """Verify the LLM enumerates each call site when changing a function's return type."""

    def test_change_enumerates_all_call_sites(self) -> None:
        """The modified prompt must mention all 4 call sites by name."""
        _skip_unless_real()

        modified_prompt, cost, model = change(
            input_prompt=CALL_SITE_INPUT_PROMPT,
            input_code=CALL_SITE_INPUT_CODE,
            change_prompt=CALL_SITE_CHANGE_PROMPT,
            budget=2.0,
            verbose=False,
        )

        judgment = _judge_call_site_names(modified_prompt)
        assert judgment.passed, (
            f"LLM did not enumerate all 4 call sites. "
            f"Judge: {judgment.reasoning} | Model: {model}, cost: ${cost:.4f} | "
            f"Output excerpt: {modified_prompt[:1000]}"
        )


@pytest.mark.real
class TestRetrySafety:
    """Verify the LLM includes retry bounds and fallback when adding retry logic."""

    def test_change_includes_retry_bound_and_fallback(self) -> None:
        """The modified prompt must specify a max retry count AND fallback behavior."""
        _skip_unless_real()

        modified_prompt, cost, model = change(
            input_prompt=RETRY_INPUT_PROMPT,
            input_code=RETRY_INPUT_CODE,
            change_prompt=RETRY_CHANGE_PROMPT,
            budget=2.0,
            verbose=False,
        )

        bound_judgment = _judge_retry_bound(modified_prompt)
        assert bound_judgment.passed, (
            f"LLM did not specify a retry bound. "
            f"Judge: {bound_judgment.reasoning} | Model: {model}, cost: ${cost:.4f} | "
            f"Output excerpt: {modified_prompt[:1000]}"
        )

        fallback_judgment = _judge_retry_fallback(modified_prompt)
        assert fallback_judgment.passed, (
            f"LLM did not define fallback behavior. "
            f"Judge: {fallback_judgment.reasoning} | Model: {model}, cost: ${cost:.4f} | "
            f"Output excerpt: {modified_prompt[:1000]}"
        )
