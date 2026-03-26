"""
Real-LLM tests for issue #939: verify change_LLM prompt hardening.

These tests call pdd.change.change() with crafted inputs and assert
the LLM actually follows the hardening guidance added in #939:
1. Enumerates call sites explicitly (not vague "all call sites")
2. Specifies max retry count and fallback when introducing retry logic

Requires: PDD_RUN_REAL_LLM_TESTS=1 or --run-all
"""

import os

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


# ---------------------------------------------------------------------------
# Fixtures: crafted prompts and code for each scenario
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

        prompt_lower = modified_prompt.lower()

        # All four call sites must be mentioned explicitly
        call_sites = ["ingest", "transform", "export_csv", "audit_log"]
        missing = [s for s in call_sites if s not in prompt_lower]
        assert not missing, (
            f"LLM failed to enumerate call sites: {missing}. "
            f"The hardened prompt should force explicit enumeration. "
            f"Model: {model}, cost: ${cost:.4f}"
        )


@pytest.mark.real
class TestRetrySafety:
    """Verify the LLM includes retry bounds and fallback when adding retry logic."""

    def test_change_includes_retry_bound(self) -> None:
        """The modified prompt must specify a maximum retry count."""
        _skip_unless_real()

        modified_prompt, cost, model = change(
            input_prompt=RETRY_INPUT_PROMPT,
            input_code=RETRY_INPUT_CODE,
            change_prompt=RETRY_CHANGE_PROMPT,
            budget=2.0,
            verbose=False,
        )

        prompt_lower = modified_prompt.lower()

        # Must contain a numeric retry limit
        has_retry_bound = any(
            phrase in prompt_lower
            for phrase in [
                "max", "maximum", "limit", "at most",
                "retry count", "retries", "attempts",
            ]
        )
        assert has_retry_bound, (
            "LLM did not specify a retry bound in the modified prompt. "
            "The hardened prompt should force a maximum retry count. "
            f"Model: {model}, cost: ${cost:.4f}"
        )

    def test_change_includes_fallback(self) -> None:
        """The modified prompt must define fallback behavior when retries are exhausted."""
        _skip_unless_real()

        modified_prompt, cost, model = change(
            input_prompt=RETRY_INPUT_PROMPT,
            input_code=RETRY_INPUT_CODE,
            change_prompt=RETRY_CHANGE_PROMPT,
            budget=2.0,
            verbose=False,
        )

        prompt_lower = modified_prompt.lower()

        has_fallback = any(
            phrase in prompt_lower
            for phrase in [
                "fallback", "fail", "error", "raise", "exception",
                "abort", "give up", "exhausted",
            ]
        )
        assert has_fallback, (
            "LLM did not define fallback behavior when retries are exhausted. "
            "The hardened prompt should force a defined fallback. "
            f"Model: {model}, cost: ${cost:.4f}"
        )
