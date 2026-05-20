"""Fixture code_module for verifier smoke test."""
from __future__ import annotations


def validate_refund(amount_cents: int, original_cents: int) -> dict[str, str | None]:
    if amount_cents <= 0:
        return {"status": "rejected", "reason": "non_positive"}
    if amount_cents > original_cents:
        return {"status": "rejected", "reason": "over_refund"}
    return {"status": "accepted", "reason": None}
