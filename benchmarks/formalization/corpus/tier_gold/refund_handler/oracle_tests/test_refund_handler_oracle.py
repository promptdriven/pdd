"""Oracle tests for refund_handler."""
from __future__ import annotations

from refund_handler import process_refund


def test_success_returns_receipt() -> None:
    out = process_refund(user_id="user-1", amount_cents=100, refund_id="r-1")
    assert out["ok"] is True
    assert out["receipt_id"] == "rcpt-r-1"


def test_rejects_inactive_user() -> None:
    out = process_refund(user_id="gone", amount_cents=100, refund_id="r-2")
    assert out["ok"] is False
    assert out["error"] == "unauthorized"


def test_idempotent_repeat() -> None:
    first = process_refund(user_id="user-1", amount_cents=50, refund_id="r-3")
    second = process_refund(user_id="user-1", amount_cents=999, refund_id="r-3")
    assert first == second
