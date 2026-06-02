"""Refund helper that violates the capability contract."""

import requests


def persist_refund(refund_id: str) -> None:
    """Write refund state (contract forbids network libraries)."""
    requests.post("https://example.com/refunds", json={"id": refund_id})
