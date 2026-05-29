"""Reference token-bucket rate limiter for M2 harness."""
from __future__ import annotations

import time


class TokenBucket:
    """Token bucket with steady refill and burst capacity."""

    def __init__(self, *, capacity: float, refill_rate: float) -> None:
        self.capacity = float(capacity)
        self.refill_rate = float(refill_rate)
        self.tokens = self.capacity
        self._last = time.monotonic()
        self._seen: set[str] = set()

    def _refill(self) -> None:
        now = time.monotonic()
        elapsed = now - self._last
        self._last = now
        self.tokens = min(self.capacity, self.tokens + elapsed * self.refill_rate)

    def allow(self, request_id: str = "") -> bool:
        if request_id and request_id in self._seen:
            return True
        self._refill()
        if self.tokens < 1.0:
            return False
        self.tokens -= 1.0
        if request_id:
            self._seen.add(request_id)
        return True
