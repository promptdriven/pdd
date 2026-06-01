"""Unit tests for waiver status classification (issue #832)."""
from __future__ import annotations

from datetime import date

from pdd.contract_ir import Waiver
from pdd.waiver_policy import classify_waiver_status, summarize_waivers


def _waiver(**overrides: object) -> Waiver:
    base = Waiver(
        raw_id="W1",
        rule_id="R6",
        status="temporary",
        reason="Provider fixture unavailable.",
        approved_by="security-review",
        follow_up="Add test.",
        raw_block=(
            "W1:\n"
            "  Rule: R6\n"
            "  Reason: Provider fixture unavailable.\n"
            "  Approved by: security-review\n"
            "  Expires: 2099-06-01\n"
        ),
        expires=date(2099, 6, 1),
    )
    for key, value in overrides.items():
        setattr(base, key, value)
    return base


def test_classify_active_waiver() -> None:
    status = classify_waiver_status(_waiver(), {"R6"}, today=date(2026, 6, 1))
    assert status == "active"


def test_classify_expired_waiver() -> None:
    status = classify_waiver_status(
        _waiver(expires=date(2020, 1, 1)),
        {"R6"},
        today=date(2026, 6, 1),
    )
    assert status == "expired"


def test_classify_unknown_rule_waiver() -> None:
    status = classify_waiver_status(_waiver(rule_id="R99"), {"R1", "R6"})
    assert status == "unknown-rule"


def test_classify_malformed_missing_required_fields() -> None:
    status = classify_waiver_status(
        _waiver(reason="", approved_by="", expires=None, raw_block="W1:\n  Rule: R6\n"),
        {"R6"},
    )
    assert status == "malformed"


def test_classify_malformed_when_expires_key_present_but_unparseable() -> None:
    """An Expires: line satisfies the field requirement even if the date is invalid."""
    waiver = _waiver(
        expires=None,
        raw_block=(
            "W1:\n"
            "  Rule: R6\n"
            "  Reason: Provider fixture unavailable.\n"
            "  Approved by: security-review\n"
            "  Expires: not-a-date\n"
        ),
    )
    status = classify_waiver_status(waiver, {"R6"})
    assert status == "active"


def test_summarize_waivers_returns_machine_readable_rows() -> None:
    rows = summarize_waivers([_waiver()], {"R6"}, today=date(2026, 6, 1))
    assert len(rows) == 1
    row = rows[0]
    assert row["id"] == "W1"
    assert row["rule_id"] == "R6"
    assert row["status"] == "active"
    assert row["expires"] == "2099-06-01"
    assert row["approved_by"] == "security-review"
