"""Tests from prompt (bootstrap fixture — replace via record_pdd_fixtures.py)."""
from __future__ import annotations

from refund_handler import process_refund


def test_R1_active_user_refund() -> None:
    result = process_refund(user_id="user-1", amount_cents=100, refund_id="r1")
    assert result["ok"] is True
    assert result["receipt_id"]


def test_R2_idempotent_repeat() -> None:
    first = process_refund(user_id="user-1", amount_cents=50, refund_id="r2")
    second = process_refund(user_id="user-1", amount_cents=50, refund_id="r2")
    assert first == second
