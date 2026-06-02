"""Tests from A0 prompt (bootstrap fixture)."""
from __future__ import annotations

from refund_handler import process_refund


def test_valid_amount_ok() -> None:
    result = process_refund(user_id="user-1", amount_cents=10, refund_id="a0-1")
    assert result["ok"] is True
