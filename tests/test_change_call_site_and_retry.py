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
    r"exhaust(?:ed|s|ion)?|"
    r"after\s+all\s+(?:retry\s+)?attempts?|"
    r"after\s+all\s+retries|"
    r"after\s+\d+\s+(?:failed\s+)?(?:retry\s+)?attempts?|"
    r"all\s+(?:retry\s+)?attempts?.{0,80}(?:fail|error|exception)|"
    r"all\s+\d+\s+(?:retry\s+)?attempts?.{0,80}(?:fail|error|exception)|"
    r"(?:if|when)\s+[\w\s]+fail(?:s|ed)?\s+on\s+(?:the\s+)?"
    r"\d+(?:st|nd|rd|th)\s+attempt|"
    r"(?:if|when)\s+(?:the\s+)?\d+(?:st|nd|rd|th)\s+attempt\s+"
    r"(?:(?:also|still)\s+)?fail(?:s|ed)?|"
    r"(?:if|when)\s+(?:the\s+)?(?:connection\s+)?"
    r"(?:error|exception|failure)\s+(?:still\s+)?"
    r"(?:persist(?:s|ed)?|remain(?:s|ed)?)\s+after\s+(?:the\s+)?"
    r"\d+(?:st|nd|rd|th)\s+(?:retry\s+)?attempt|"
    r"once\s+(?:the\s+)?(?:max(?:imum)?\s+)?(?:retry\s+)?attempts?\s+"
    r"(?:is\s+|are\s+)?(?:reached|exhausted)|"
    r"(?:once|when|if)\s+(?:the\s+)?max(?:imum)?\s+number\s+of\s+attempts?\s+"
    r"(?:is\s+|are\s+|has\s+been\s+)?(?:reached|exceeded|exhausted)|"
    r"(?:retry\s+)?limit\s+(?:is\s+|has\s+been\s+)?(?:reached|exceeded)|"
    r"(?:final|last)\s+(?:retry\s+)?attempt|"
    r"if\s+(?:it\s+)?still\s+fail(?:s|ed)?|"
    r"still\s+(?:encounter|encounters|raise|raises)\s+"
    r"(?:a\s+)?(?:connection\s+)?(?:error|exception)|"
    r"final\s+(?:connection\s+)?(?:error|exception)|"
    r"when\s+(?:all\s+)?(?:retry\s+)?attempts?\s+fail|"
    r"stop\s+retrying"
    r")\b",
    re.IGNORECASE,
)

_FALLBACK_ACTION_PATTERN = re.compile(
    r"\b(?:"
    r"(?:re-?)?rais(?:e|es|ed|ing)|"
    r"return(?:s|ed|ing)?|"
    r"log(?:s|ged|ging)?|"
    r"skip(?:s|ped|ping)?|"
    r"abort(?:s|ed|ing)?|"
    r"surfac(?:e|es|ed|ing)|"
    r"propagat(?:e|es|ed|ing)"
    r")\b|"
    r"\buse(?:s|d|ing)?\s+(?:(?:a|the)\s+)?fallback\b|"
    r"\b(?:fall(?:s|ing)?|fell)\s+back\b|"
    r"\bfail(?:s|ed|ing)?\s+closed\b",
    re.IGNORECASE,
)

_RETRY_CLAUSE_PATTERN = re.compile(r"[^,;.!?]+(?:[,;.!?]+|$)", re.DOTALL)

_RETRY_CONTINUATION_PATTERN = re.compile(
    r"\b(?:keep(?:s|ing)?|continu(?:e|es|ed|ing)|resum(?:e|es|ed|ing))\s+"
    r"(?:(?:to|with)\s+)?(?:retry(?:ing)?|retries)\b|"
    r"\btry\s+again\b|"
    r"\banother\s+(?:retry\s+)?attempt\b",
    re.IGNORECASE,
)

_NEGATED_FALLBACK_ACTION_PATTERN = re.compile(
    r"(?:"
    r"\b(?:do|does|did|must|should|shall|will|would|can|could|may|might)\s+"
    r"not\s+(?:ever\s+|to\s+)?|"
    r"\bnot\s+(?:ever\s+|to\s+)?|"
    r"\bnever\s+|"
    r"\bavoid(?:s|ed|ing)?\s+|"
    r"\bwithout\s+|"
    r"\brefrain(?:s|ed|ing)?\s+from\s+"
    r")$",
    re.IGNORECASE,
)

_SUCCESS_RETURN_PATTERN = re.compile(
    r"\breturn(?:s|ed|ing)?\s+(?:(?:a|an|the)\s+)?"
    r"(?:success(?:ful(?:ly)?)?|ok(?:ay)?|true|normally)\b",
    re.IGNORECASE,
)

_UNRELATED_ACTION_PREFIX_PATTERN = re.compile(
    r"^\s*(?:separately|independently|elsewhere|unrelated(?:ly)?|"
    r"for\s+diagnostics(?:\s+only)?)\b",
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


def _retry_clauses(prompt_output: str) -> tuple[str, ...]:
    """Split prose into bounded clauses without losing fallback punctuation."""
    return tuple(
        match.group(0).strip()
        for match in _RETRY_CLAUSE_PATTERN.finditer(prompt_output)
        if match.group(0).strip()
    )


def _fallback_action_state(clause: str) -> tuple[bool, bool]:
    """Return whether a clause has an affirmative action or rejects fallback."""
    if _RETRY_CONTINUATION_PATTERN.search(clause):
        return False, True
    if _UNRELATED_ACTION_PREFIX_PATTERN.search(clause):
        return False, True

    affirmative = False
    rejected = False
    for action in _FALLBACK_ACTION_PATTERN.finditer(clause):
        prefix = clause[max(0, action.start() - 48) : action.start()]
        if _NEGATED_FALLBACK_ACTION_PATTERN.search(prefix):
            rejected = True
            continue
        if _SUCCESS_RETURN_PATTERN.match(clause, action.start()):
            rejected = True
            continue
        affirmative = True

    if rejected:
        return False, True
    return affirmative, False


def _judge_retry_fallback(prompt_output: str) -> JudgmentResult:
    """Check that retry exhaustion has explicit fallback behavior."""
    clauses = _retry_clauses(prompt_output)
    has_exhaustion = False
    has_action = False
    for index, clause in enumerate(clauses):
        if not _RETRY_EXHAUSTION_PATTERN.search(clause):
            continue
        has_exhaustion = True
        action, rejected = _fallback_action_state(clause)
        if action and not rejected:
            has_action = True
            break
        if rejected or index + 1 >= len(clauses):
            continue
        action, rejected = _fallback_action_state(clauses[index + 1])
        if action and not rejected:
            has_action = True
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
        ),
    )
    def test_retry_fallback_judge_rejects_non_fallback_conditions(
        self, guidance: str
    ) -> None:
        """Failure state alone, negation, or continued retry is no fallback."""
        judgment = _judge_retry_fallback(guidance)

        assert not judgment.passed


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
