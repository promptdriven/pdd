"""Oracle tests for token_bucket."""
from __future__ import annotations

import time

from token_bucket import TokenBucket


def test_allows_until_empty() -> None:
    bucket = TokenBucket(capacity=2.0, refill_rate=0.0)
    assert bucket.allow() is True
    assert bucket.allow() is True
    assert bucket.allow() is False


def test_refills_over_time() -> None:
    bucket = TokenBucket(capacity=1.0, refill_rate=10.0)
    assert bucket.allow() is True
    assert bucket.allow() is False
    time.sleep(0.15)
    assert bucket.allow() is True


def test_duplicate_request_id_is_safe() -> None:
    bucket = TokenBucket(capacity=1.0, refill_rate=0.0)
    assert bucket.allow("req-1") is True
    assert bucket.allow("req-1") is True
