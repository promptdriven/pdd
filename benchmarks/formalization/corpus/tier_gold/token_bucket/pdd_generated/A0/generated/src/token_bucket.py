"""Bootstrap A0 generate output (replace via record_pdd_fixtures.py)."""
from __future__ import annotations


class TokenBucket:
    """Minimal A0 stub — no refill semantics."""

    def __init__(self, *, capacity: float, refill_rate: float) -> None:
        self._remaining = int(capacity)

    def allow(self, request_id: str = "") -> bool:
        if self._remaining <= 0:
            return False
        self._remaining -= 1
        return True
