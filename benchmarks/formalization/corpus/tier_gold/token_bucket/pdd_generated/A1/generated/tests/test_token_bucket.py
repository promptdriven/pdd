"""Tests from prompt (bootstrap fixture — replace via record_pdd_fixtures.py)."""
from __future__ import annotations

import time

from token_bucket import TokenBucket


def test_R1_allow_decrements() -> None:
    bucket = TokenBucket(capacity=2.0, refill_rate=0.0)
    assert bucket.allow() is True
    assert bucket.allow() is True
    assert bucket.allow() is False


def test_R3_refill() -> None:
    bucket = TokenBucket(capacity=1.0, refill_rate=10.0)
    assert bucket.allow() is True
    assert bucket.allow() is False
    time.sleep(0.15)
    assert bucket.allow() is True
