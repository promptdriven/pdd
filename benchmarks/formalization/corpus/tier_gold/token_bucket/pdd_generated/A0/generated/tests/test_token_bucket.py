"""Tests from A0 prompt (bootstrap fixture)."""
from __future__ import annotations

from token_bucket import TokenBucket


def test_allows_until_empty() -> None:
    bucket = TokenBucket(capacity=2.0, refill_rate=0.0)
    assert bucket.allow() is True
    assert bucket.allow() is True
    assert bucket.allow() is False
