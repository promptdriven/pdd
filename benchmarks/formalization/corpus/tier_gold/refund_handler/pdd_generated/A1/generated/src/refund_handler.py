"""Reference refund handler for M2 harness."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass
class RefundResult:
    ok: bool
    receipt_id: str | None = None
    error: str | None = None


_ACTIVE_USERS = frozenset({"user-1", "user-2"})
_PROCESSED: dict[str, RefundResult] = {}


def process_refund(*, user_id: str, amount_cents: int, refund_id: str) -> dict[str, Any]:
    if refund_id in _PROCESSED:
        prior = _PROCESSED[refund_id]
        return {"ok": prior.ok, "receipt_id": prior.receipt_id, "error": prior.error}
    if user_id not in _ACTIVE_USERS:
        result = RefundResult(ok=False, error="unauthorized")
    elif amount_cents <= 0:
        result = RefundResult(ok=False, error="invalid_amount")
    else:
        result = RefundResult(ok=True, receipt_id=f"rcpt-{refund_id}")
    _PROCESSED[refund_id] = result
    return {"ok": result.ok, "receipt_id": result.receipt_id, "error": result.error}
