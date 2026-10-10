"""Regression coverage for the Step 9 acceptance-criteria gate (#2285).

Step 9 must not advance with a tests-pass token when its own final-verification
report explicitly emits ``**Acceptance criteria:** ACCEPTANCE_CRITERIA_UNMET``
(any original issue acceptance criterion still unmet/unverified/untested/
unimplemented). The gate is marker-based (Option B): it acts only on the
explicit UNMET marker and never guesses from arbitrary prose.
"""

from __future__ import annotations

import io
from pathlib import Path

from rich.console import Console

from pdd.agentic_e2e_fix_orchestrator import (
    _post_step9_resume_action,
    _resolve_step9_loop_token,
)


def _console() -> Console:
    return Console(file=io.StringIO(), force_terminal=False)


def test_unmet_acceptance_criterion_overrides_pass() -> None:
    """An explicit UNMET marker downgrades ALL_TESTS_PASS to CONTINUE_CYCLE."""
    output = """## Step 9: Final Verification (Cycle 1)

All 18/18 selected unit tests and 22/22 e2e tests pass, but these source
issue acceptance criteria remain unimplemented: body/prelaunch strength
source, startup receipt strength/time values.

**Acceptance criteria:** ACCEPTANCE_CRITERIA_UNMET
**Status:** ALL_TESTS_PASS
"""

    assert (
        _resolve_step9_loop_token(
            output,
            _console(),
            mock_contract_audit_required=False,
        )
        == "CONTINUE_CYCLE"
    )


def test_met_acceptance_criteria_keeps_existing_pass_path() -> None:
    """A MET marker preserves the normal Step 9 pass path (maps to LOCAL_TESTS_PASS)."""
    output = """## Step 9: Final Verification (Cycle 1)

Every original acceptance criterion is implemented, tested, and verified.

**Acceptance criteria:** ACCEPTANCE_CRITERIA_MET
**Status:** ALL_TESTS_PASS
"""

    assert (
        _resolve_step9_loop_token(
            output,
            _console(),
            mock_contract_audit_required=False,
        )
        == "LOCAL_TESTS_PASS"
    )


def test_bare_pass_without_marker_is_unchanged() -> None:
    """Option B: absence of any acceptance marker keeps pre-#2285 behavior."""
    assert (
        _resolve_step9_loop_token(
            "**Status:** ALL_TESTS_PASS",
            _console(),
            mock_contract_audit_required=False,
        )
        == "LOCAL_TESTS_PASS"
    )


def test_prose_mention_does_not_downgrade() -> None:
    """A prose mention cannot impersonate the exact UNMET result line."""
    output = """I considered whether ACCEPTANCE_CRITERIA_UNMET applied, but every
criterion is actually met.
**Status:** ALL_TESTS_PASS
"""

    assert (
        _resolve_step9_loop_token(
            output,
            _console(),
            mock_contract_audit_required=False,
        )
        == "LOCAL_TESTS_PASS"
    )


def test_cached_step9_unmet_criteria_advances_on_resume() -> None:
    """Resume must not trust a cached pass token that carries an UNMET marker."""
    unmet = _post_step9_resume_action(
        "**Acceptance criteria:** ACCEPTANCE_CRITERIA_UNMET\n"
        "**Status:** ALL_TESTS_PASS",
        current_cycle=1,
        max_cycles=3,
        console=_console(),
    )
    met = _post_step9_resume_action(
        "**Acceptance criteria:** ACCEPTANCE_CRITERIA_MET\n"
        "**Status:** ALL_TESTS_PASS",
        current_cycle=1,
        max_cycles=3,
        console=_console(),
    )

    assert unmet == "ADVANCE_CYCLE"
    assert met == "SUCCESS_FALL_THROUGH"


def test_step9_prompt_requires_acceptance_criteria_evaluation() -> None:
    """The Step 9 prompt must mandate acceptance-criteria evaluation and markers."""
    prompt = (
        Path(__file__).resolve().parents[1]
        / "pdd"
        / "prompts"
        / "agentic_e2e_fix_step9_verify_all_LLM.prompt"
    ).read_text(encoding="utf-8")

    for expected in (
        "acceptance criteria",
        "ACCEPTANCE_CRITERIA_MET",
        "ACCEPTANCE_CRITERIA_UNMET",
        "**Acceptance criteria:**",
    ):
        assert expected in prompt
