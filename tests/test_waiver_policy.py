"""Tests for waiver status classification helpers."""
from __future__ import annotations

from datetime import date

from pdd.contract_ir import Waiver
from pdd.waiver_policy import classify_waiver_status, has_unparseable_expires


def _waiver(**kwargs: object) -> Waiver:
    defaults = {
        "raw_id": "W1",
        "rule_id": "R1",
        "status": "temporary",
        "reason": "Fixture unavailable.",
        "approved_by": "security-review",
        "expires": date(2099, 6, 1),
        "follow_up": "",
        "raw_block": (
            "W1:\n"
            "  Rule: R1\n"
            "  Reason: Fixture unavailable.\n"
            "  Approved by: security-review\n"
            "  Expires: 2099-06-01\n"
        ),
    }
    defaults.update(kwargs)
    return Waiver(**defaults)  # type: ignore[arg-type]


def test_unparseable_expires_is_malformed_not_active() -> None:
    waiver = _waiver(
        expires=None,
        raw_block=(
            "W1:\n"
            "  Rule: R1\n"
            "  Reason: Fixture unavailable.\n"
            "  Approved by: security-review\n"
            "  Expires: not-a-date\n"
        ),
    )
    assert has_unparseable_expires(waiver)
    assert classify_waiver_status(waiver, {"R1"}) == "malformed"


def test_missing_expires_field_is_malformed() -> None:
    waiver = _waiver(
        expires=None,
        raw_block=(
            "W1:\n"
            "  Rule: R1\n"
            "  Reason: Fixture unavailable.\n"
            "  Approved by: security-review\n"
        ),
    )
    assert not has_unparseable_expires(waiver)
    assert classify_waiver_status(waiver, {"R1"}) == "malformed"


def test_parseable_expires_is_active() -> None:
    waiver = _waiver()
    assert classify_waiver_status(waiver, {"R1"}) == "active"
