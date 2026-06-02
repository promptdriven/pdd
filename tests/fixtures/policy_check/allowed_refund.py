"""Refund helper allowed to read configuration."""

import os


def refund_via_provider(amount: int) -> bool:
    """Process a refund using provider configuration."""
    _ = os.getenv("REFUND_API_URL")
    return amount > 0
