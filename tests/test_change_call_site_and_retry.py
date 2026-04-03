"""
Real-LLM regression tests for issue #939: call-site enumeration and retry safety.

Two tests, each making one change() call + one cheap LLM-as-judge call:
1. Call-site enumeration — verifies the LLM lists all 4 call sites by name
2. Retry safety — verifies the LLM specifies a max retry count AND fallback

Requires: PDD_RUN_REAL_LLM_TESTS=1 or --run-all
"""

import os

import pytest
from pydantic import BaseModel

from pdd.change import change
from pdd.llm_invoke import llm_invoke

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


def _skip_unless_real() -> None:
    """Skip unless real LLM tests are enabled."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM tests require API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all."
        )


class JudgmentResult(BaseModel):
    """Structured output for LLM-as-judge evaluation."""
    passed: bool
    reasoning: str


_CONTRADICTION_PHRASES = [
    "criterion is met",
    "criterion is clearly met",
    "is satisfied",
    "explicitly defines",
    "the answer is yes",
    "does meet",
    "does satisfy",
]


def _judge(prompt_output: str, question: str) -> JudgmentResult:
    """Use a cheap LLM to judge whether the output meets a criterion.

    Retries once at higher strength if the reasoning contradicts the verdict.
    """
    for attempt, strength in enumerate([0.3, 0.5]):
        result = llm_invoke(
            messages=[
                {
                    "role": "system",
                    "content": (
                        "You are a strict test evaluator. Answer the question about "
                        "the provided text. Set passed=true only if the criterion is "
                        "clearly and unambiguously met. Be strict. "
                        "IMPORTANT: Your 'passed' boolean MUST be consistent with "
                        "your reasoning. If your reasoning concludes the criterion "
                        "is met, set passed=true."
                    ),
                },
                {
                    "role": "user",
                    "content": f"TEXT:\n{prompt_output}\n\nQUESTION:\n{question}",
                },
            ],
            output_pydantic=JudgmentResult,
            strength=strength,
            temperature=0.0,
            verbose=False,
        )
        judgment: JudgmentResult = result["result"]

        # Detect reasoning/verdict contradiction and retry with stronger model
        if not judgment.passed and attempt == 0:
            reasoning_lower = judgment.reasoning.lower()
            if any(phrase in reasoning_lower for phrase in _CONTRADICTION_PHRASES):
                continue  # retry with higher strength
        return judgment
    return judgment


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

        judgment = _judge(
            modified_prompt,
            "Does this text explicitly mention ALL FOUR of these function "
            "names as call sites that need updating: ingest, transform, "
            "export_csv, audit_log? Each must appear by name, not just as "
            "a vague reference like 'all call sites'.",
        )
        assert judgment.passed, (
            f"LLM did not enumerate all 4 call sites. "
            f"Judge: {judgment.reasoning} | Model: {model}, cost: ${cost:.4f}"
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

        bound_judgment = _judge(
            modified_prompt,
            "Does this text specify a concrete maximum number of retry "
            "attempts (e.g., 'retry up to 3 times', 'max 5 attempts')? "
            "There must be an explicit numeric limit, not just the word 'retry'.",
        )
        assert bound_judgment.passed, (
            f"LLM did not specify a retry bound. "
            f"Judge: {bound_judgment.reasoning} | Model: {model}, cost: ${cost:.4f}"
        )

        fallback_judgment = _judge(
            modified_prompt,
            "Does this text define what should happen when all retry "
            "attempts are exhausted (e.g., raise an exception, log and "
            "skip, return an error)? There must be explicit fallback "
            "behavior, not just 'retry N times'.",
        )
        assert fallback_judgment.passed, (
            f"LLM did not define fallback behavior. "
            f"Judge: {fallback_judgment.reasoning} | Model: {model}, cost: ${cost:.4f}"
        )
