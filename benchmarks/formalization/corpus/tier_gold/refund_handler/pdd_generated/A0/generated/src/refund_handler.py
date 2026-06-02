"""Bootstrap A0 generate output (replace via record_pdd_fixtures.py)."""
from __future__ import annotations


def process_refund(*, user_id: str, amount_cents: int, refund_id: str) -> dict:
    """Naive A0 stub — no idempotency."""
    if amount_cents <= 0:
        return {"ok": False, "receipt_id": None, "error": "invalid_amount"}
    return {"ok": True, "receipt_id": f"rcpt-{refund_id}", "error": None}
