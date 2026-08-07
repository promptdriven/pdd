"""
Reproduction tests for Issue #1225: test

Issue URL: https://github.com/promptdriven/pdd/issues/1225
Author: Serhan-Asad

Background:
-----------
Issue #1225 itself contains no actionable bug description — both the title
and body are the single word "test". The embedded PDD workflow state in the
issue comments, however, reveals that the agentic bug workflow failed on all
three completed steps (1–3) with identical errors from the Anthropic API:

    "api_error_status":429,
    "result":"You've hit your limit · resets 2:50am (UTC)",
    "duration_api_ms":0,
    "total_cost_usd":0

The ``duration_api_ms:0`` and ``total_cost_usd:0`` confirm the Claude Code CLI
rejected the request locally (subscription-tier weekly limit) before any API
call was made — this is NOT a transient API-tier 429 that would benefit from
the 60-second ``RATE_LIMIT_BACKOFF_FLOOR`` retry.

The specific time format in this issue is "2:50am" (hours:minutes + am/pm),
which differs from the "11pm" (hours-only) format exercised by the existing
``TestCredentialLimitClassification`` suite in ``test_agentic_common.py``.

What these tests verify:
1. The exact JSON envelope from the issue workflow state is classified as
   ``credential-limit`` (not as a transient rate-limit that would be retried).
2. The "resets 2:50am (UTC)" time format (HH:MMam/pm) correctly triggers the
   proximity + time-token guard in ``_classify_permanent_error``.
3. ``_is_permanent_error`` (the public wrapper) returns True for this error.

These tests pass on the current codebase — confirming the code correctly
handles this error pattern. They serve as regression tests to prevent
future changes from inadvertently reclassifying this pattern as transient.

Run with:
    pytest tests/test_issue_1225_reproduction.py -v
"""

import json
import os
from unittest.mock import patch, MagicMock

import pytest


# Exact JSON envelope from the issue #1225 workflow state (step 1 output).
# Unicode escape \\u00b7 is the middle dot "·".
ISSUE_1225_STEP1_ERROR = (
    'Exit code 1: {"type":"result","subtype":"success","is_error":true,'
    '"api_error_status":429,"duration_ms":552,"duration_api_ms":0,'
    '"num_turns":1,"result":"You\\u2019ve hit your limit \\u00b7 resets '
    '2:50am (UTC)","stop_reason":"stop_sequence",'
    '"session_id":"e259cf03-1052-416c-99cd-416b47e62aeb",'
    '"total_cost_usd":0,"usage":{"input_tokens":0}}'
)

# Minimal envelope with only the relevant fragment, using the literal
# Unicode character as it appears after JSON decoding.
ISSUE_1225_MINIMAL_ENVELOPE = (
    'Exit code 1: {"api_error_status":429,'
    '"result":"You\u2019ve hit your limit \u00b7 resets 2:50am (UTC)"}'
)

# Variant using straight apostrophe (as it appears in some CLI outputs).
ISSUE_1225_STRAIGHT_APOSTROPHE = (
    'Exit code 1: {"api_error_status":429,'
    '"result":"You\'ve hit your limit \u00b7 resets 2:50am (UTC)"}'
)


class TestIssue1225CredentialLimitDetection:
    """Regression tests for issue #1225: credential-limit detection with
    HH:MMam/pm time format (e.g. "resets 2:50am (UTC)").

    The existing ``TestCredentialLimitClassification`` covers "resets 11pm"
    (hour-only) and "resets May 18, 11pm" (date + hour-only). This class adds
    coverage for the HH:MM format first seen in issue #1225's workflow state.
    """

    def test_issue_1225_step1_error_classifies_as_credential_limit(self):
        """The exact step-1 error envelope from issue #1225's workflow state
        must classify as ``credential-limit``, not as a transient 429.

        The "resets 2:50am" time token starts with a digit ("2"), which the
        proximity regex matches via the ``\\d`` branch.  If this assertion
        fails, the orchestrator would apply the 60-second rate-limit backoff
        floor and burn three retry attempts on a limit that resets hours later.
        """
        from pdd.agentic_common import _classify_permanent_error

        result = _classify_permanent_error(ISSUE_1225_STEP1_ERROR)
        assert result == "credential-limit", (
            f"Expected 'credential-limit', got {result!r}. "
            "The subscription weekly-limit error with 'resets 2:50am (UTC)' "
            "must not be treated as a transient API-tier 429."
        )

    def test_minimal_envelope_resets_hhmm_ampm_classifies_as_credential_limit(self):
        """Minimal envelope: 'resets 2:50am (UTC)' must classify as credential-limit.

        This is the load-bearing format from issue #1225 — hours:minutes +
        am/pm suffix.  The regex time-token guard must accept this format.
        """
        from pdd.agentic_common import _classify_permanent_error

        result = _classify_permanent_error(ISSUE_1225_MINIMAL_ENVELOPE)
        assert result == "credential-limit", (
            f"Expected 'credential-limit', got {result!r}. "
            "The 'resets 2:50am' (HH:MMam) pattern must be recognised as "
            "a time token so credential-limit fires instead of transient retry."
        )

    def test_straight_apostrophe_variant_classifies_as_credential_limit(self):
        """Variant with straight apostrophe in \"You've\" also classifies correctly.

        Some CLI output variants use a straight apostrophe (U+0027) rather than
        the right single quotation mark (U+2019). Both must classify as credential-limit.
        """
        from pdd.agentic_common import _classify_permanent_error

        result = _classify_permanent_error(ISSUE_1225_STRAIGHT_APOSTROPHE)
        assert result == "credential-limit", (
            f"Expected 'credential-limit', got {result!r}. "
            "Straight-apostrophe variant must also trigger credential-limit."
        )

    def test_issue_1225_error_is_permanent(self):
        """``_is_permanent_error`` (public wrapper) must return True.

        Callers throughout the codebase use ``_is_permanent_error`` to decide
        whether to skip the retry/backoff loop.  A False here means three
        wasted 60-second waits before the issue is abandoned.
        """
        from pdd.agentic_common import _is_permanent_error

        assert _is_permanent_error(ISSUE_1225_STEP1_ERROR) is True, (
            "Expected True from _is_permanent_error for the issue #1225 "
            "credential-limit envelope; got False."
        )

    def test_resets_hhmm_format_various_times(self):
        """The regex must accept multiple HH:MM times (not just 2:50am)."""
        from pdd.agentic_common import _classify_permanent_error

        time_variants = [
            "resets 2:50am (UTC)",
            "resets 11:30pm (UTC)",
            "resets 3:15am (UTC)",
            "resets 12:00am (UTC)",
        ]
        for time_str in time_variants:
            envelope = (
                f'Exit code 1: {{"api_error_status":429,'
                f'"result":"You\'ve hit your limit \u00b7 {time_str}"}}'
            )
            result = _classify_permanent_error(envelope)
            assert result == "credential-limit", (
                f"Time format '{time_str}' was not classified as credential-limit; "
                f"got {result!r}. All HH:MM time formats must be recognised."
            )

    def test_issue_1225_error_not_treated_as_transient_rate_limit(self):
        """Even though ``_is_rate_limited`` fires on this envelope (it contains
        '429'), ``_classify_permanent_error`` must return a non-None value,
        proving that the credential-limit class takes priority over the
        transient rate-limit short-circuit.
        """
        from pdd.agentic_common import _classify_permanent_error, _is_rate_limited

        # Confirm _is_rate_limited sees this as a rate-limit signal ...
        assert _is_rate_limited(ISSUE_1225_MINIMAL_ENVELOPE) is True

        # ... but the permanent classifier still wins.
        result = _classify_permanent_error(ISSUE_1225_MINIMAL_ENVELOPE)
        assert result is not None, (
            "_classify_permanent_error returned None (treating as transient) "
            "even though this is a subscription weekly-limit (credential-limit). "
            "The _PERMANENT_ERROR_CLASSES check must run BEFORE _is_rate_limited."
        )
        assert result == "credential-limit"


# ---------------------------------------------------------------------------
# Fixtures for caller-behavior tests (single-provider false-positive path)
# ---------------------------------------------------------------------------

@pytest.fixture
def _single_anthropic_env():
    """Provides a single-anthropic-provider environment with no other providers."""
    with (
        patch.dict(os.environ, {}, clear=True),
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._has_agy_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._has_legacy_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._opencode_auth_file_has_credentials", return_value=False),
        patch("pdd.agentic_common._iter_opencode_config_texts", return_value=[]),
    ):
        yield


@pytest.fixture
def _mock_find_cli():
    with patch("pdd.agentic_common._find_cli_binary", return_value="/bin/claude"):
        yield


@pytest.fixture
def _mock_subprocess():
    with patch("pdd.agentic_common._subprocess_run") as m:
        yield m


@pytest.fixture
def _mock_model_data():
    with patch("pdd.agentic_common._load_model_data", return_value=None):
        yield


# Subprocess stdout that causes a credential-limit FALSE-POSITIVE:
# - returncode=0 (success path in _run_with_provider → success=True)
# - result starts with "Error:" (triggers is_false_positive=True)
# - total_cost_usd > 0.0 (triggers the Error:-check branch of is_false_positive)
# - contains 429 + "hit your limit · resets 2:50am" (matches _is_rate_limited AND
#   _classify_permanent_error="credential-limit")
#
# Why this matters: the bug is at agentic_common.py:2297, where the single-provider
# false-positive retry path calls _is_rate_limited() but NOT _classify_permanent_error()
# first. Credential-limit errors that arrive via exit-code-0 (false-positive path)
# are retried with a 60s backoff floor instead of breaking immediately.
_CREDENTIAL_LIMIT_FP_STDOUT = json.dumps({
    "result": (
        "Error: api_error_status: 429 You\u2019ve hit your limit"
        " \u00b7 resets 2:50am (UTC)"
    ),
    "total_cost_usd": 0.05,
})

# A genuine success response (used in contrast tests)
_GENUINE_SUCCESS_STDOUT = json.dumps({
    "result": (
        "Task completed successfully with detailed analysis and"
        " comprehensive recommendations covering all edge cases."
    ),
    "total_cost_usd": 0.10,
})


class TestSingleProviderCredentialLimitFalsePositiveBug:
    """Tests for the sibling bug in the single-provider false-positive retry path.

    Root cause (agentic_common.py line 2297):
        The single-provider false-positive path checks _is_rate_limited() to raise the
        60s backoff floor, but does NOT call _classify_permanent_error() first.
        The not-success path at lines 2358-2381 DOES call _classify_permanent_error()
        and breaks immediately for permanent errors.

    Consequence:
        A credential-limit error ("You've hit your limit · resets 2:50am") that arrives
        via exit code 0 with an "Error:"-prefixed result (false-positive path) is retried
        with a 60-second floor instead of breaking immediately, wasting retry budget and
        delay on a limit that won't clear for hours.

    These tests FAIL on current (buggy) code and PASS after the fix.
    """

    def test_credential_limit_false_positive_not_retried(
        self,
        _single_anthropic_env,
        _mock_find_cli,
        _mock_subprocess,
        _mock_model_data,
        tmp_path,
    ):
        """A credential-limit false-positive (exit 0, Error:-prefixed, cost > 0) in a
        single-provider config must NOT be retried — the loop must break on the first
        attempt.

        Bug: _is_rate_limited() is checked at line 2297 without first calling
        _classify_permanent_error(). The "429" in the credential-limit message matches
        _is_rate_limited(), so the loop applies a 60s backoff and retries instead of
        breaking.

        FAILS on buggy code: subprocess is called max_retries=3 times (two retries).
        PASSES after fix: subprocess is called once, then the loop breaks.
        """
        from pdd.agentic_common import run_agentic_task

        _mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout=_CREDENTIAL_LIMIT_FP_STDOUT,
            stderr="",
        )

        with patch("pdd.agentic_common.time.sleep"):  # prevent actual sleeping
            run_agentic_task("Do work", tmp_path, max_retries=3)

        assert _mock_subprocess.call_count == 1, (
            f"Expected subprocess to be called exactly once (credential-limit FP must "
            f"break immediately), but it was called {_mock_subprocess.call_count} time(s). "
            "The single-provider false-positive path is retrying a credential-limit error "
            "instead of breaking — _classify_permanent_error() must be checked before "
            "_is_rate_limited() at agentic_common.py:2297."
        )

    def test_credential_limit_false_positive_no_backoff_sleep(
        self,
        _single_anthropic_env,
        _mock_find_cli,
        _mock_subprocess,
        _mock_model_data,
        tmp_path,
    ):
        """A credential-limit false-positive must not trigger the 60-second backoff sleep.

        Bug: _is_rate_limited() returns True for the 429-containing credential-limit
        message, so the buggy code calls time.sleep(~60) before each retry. After the
        fix, _classify_permanent_error() returns 'credential-limit' first and the loop
        breaks without sleeping.

        FAILS on buggy code: time.sleep is called twice (for two retries with max_retries=3).
        PASSES after fix: time.sleep is never called.
        """
        from pdd.agentic_common import run_agentic_task

        _mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout=_CREDENTIAL_LIMIT_FP_STDOUT,
            stderr="",
        )

        with patch("pdd.agentic_common.time.sleep") as mock_sleep:
            run_agentic_task("Do work", tmp_path, max_retries=3)

        assert mock_sleep.call_count == 0, (
            f"Expected time.sleep to never be called for a credential-limit false-positive, "
            f"but it was called {mock_sleep.call_count} time(s) with args "
            f"{[c.args for c in mock_sleep.call_args_list]}. "
            "The 60s RATE_LIMIT_BACKOFF_FLOOR must not be applied to credential-limit errors."
        )

    def test_credential_limit_false_positive_prevents_retry_to_success(
        self,
        _single_anthropic_env,
        _mock_find_cli,
        _mock_subprocess,
        _mock_model_data,
        tmp_path,
    ):
        """When a credential-limit FP appears on attempt 1 in a single-provider config,
        the task must fail immediately — it must NOT retry and succeed on a later attempt.

        Scenario: subprocess returns two credential-limit FPs then a genuine success.
        Fixed code:  breaks on attempt 1  →  overall failure (success=False).
        Buggy code:  retries twice  →  succeeds on attempt 3  →  success=True.

        FAILS on buggy code: returns success=True (retried to the genuine success).
        PASSES after fix: returns success=False (broke on the first credential-limit FP).
        """
        from pdd.agentic_common import run_agentic_task

        fp_response = MagicMock(
            returncode=0, stdout=_CREDENTIAL_LIMIT_FP_STDOUT, stderr=""
        )
        success_response = MagicMock(
            returncode=0, stdout=_GENUINE_SUCCESS_STDOUT, stderr=""
        )
        # Two credential-limit FPs followed by a genuine success.
        _mock_subprocess.side_effect = [fp_response, fp_response, success_response]

        with patch("pdd.agentic_common.time.sleep"):
            success, _msg, _cost, _provider = run_agentic_task(
                "Do work", tmp_path, max_retries=3
            )

        assert success is False, (
            "Expected task to fail (credential-limit FP must not be retried to success), "
            "but run_agentic_task returned success=True. "
            "The single-provider false-positive path retried the credential-limit error "
            "and reached the genuine success response — _classify_permanent_error() must "
            "be checked before _is_rate_limited() at agentic_common.py:2297."
        )

    def test_credential_limit_false_positive_call_count_with_success_setup(
        self,
        _single_anthropic_env,
        _mock_find_cli,
        _mock_subprocess,
        _mock_model_data,
        tmp_path,
    ):
        """Complements the previous test: subprocess must be called exactly once when a
        credential-limit FP occurs, even when later calls would return genuine success.

        This verifies the call-count dimension of the same scenario as the previous test:
        the loop must break on the first credential-limit FP, so the genuine success
        response is never reached.

        FAILS on buggy code: subprocess called 3 times (2 FPs + 1 success).
        PASSES after fix: subprocess called once (FP → break).
        """
        from pdd.agentic_common import run_agentic_task

        fp_response = MagicMock(
            returncode=0, stdout=_CREDENTIAL_LIMIT_FP_STDOUT, stderr=""
        )
        success_response = MagicMock(
            returncode=0, stdout=_GENUINE_SUCCESS_STDOUT, stderr=""
        )
        _mock_subprocess.side_effect = [fp_response, fp_response, success_response]

        with patch("pdd.agentic_common.time.sleep"):
            run_agentic_task("Do work", tmp_path, max_retries=3)

        assert _mock_subprocess.call_count == 1, (
            f"Expected subprocess to be called exactly once (credential-limit FP must break "
            f"immediately), but it was called {_mock_subprocess.call_count} time(s). "
            "The loop must not advance to the genuine success response — "
            "_classify_permanent_error() must be checked before _is_rate_limited() "
            "at agentic_common.py:2297."
        )
