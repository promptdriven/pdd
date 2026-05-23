
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest

from src.token_bucket_after import TokenBucket


# ---------------------------------------------------------------------------
# R1 - Reject non-positive capacity
# ---------------------------------------------------------------------------
def test_r1_zero_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket(0)


def test_r1_negative_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket(-5)


def test_r1_non_int_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket(3.5)


def test_r1_bool_capacity_rejected():
    # booleans are not accepted as ints per the vocabulary
    with pytest.raises(ValueError):
        TokenBucket(True)


def test_r1_string_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket("10")


# ---------------------------------------------------------------------------
# R2 - Default tokens to capacity
# ---------------------------------------------------------------------------
def test_r2_default_tokens_equal_capacity():
    bucket = TokenBucket(10)
    assert bucket.tokens_available == 10
    assert bucket.capacity == 10


def test_r2_explicit_initial_tokens_respected():
    bucket = TokenBucket(10, tokens_available=4)
    assert bucket.tokens_available == 4


def test_r2_explicit_zero_initial_tokens():
    bucket = TokenBucket(10, tokens_available=0)
    assert bucket.tokens_available == 0


def test_r2_initial_tokens_above_capacity_rejected():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=10)


def test_r2_negative_initial_tokens_rejected():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=-1)


# ---------------------------------------------------------------------------
# R3 - Successful consume returns True
# ---------------------------------------------------------------------------
def test_r3_consume_partial_returns_true_and_decrements():
    bucket = TokenBucket(10)
    assert bucket.consume(4) is True
    assert bucket.tokens_available == 6


def test_r3_consume_exact_amount_returns_true():
    bucket = TokenBucket(10, tokens_available=4)
    assert bucket.consume(4) is True
    assert bucket.tokens_available == 0


def test_r3_consume_zero_succeeds_without_change():
    bucket = TokenBucket(10, tokens_available=5)
    assert bucket.consume(0) is True
    assert bucket.tokens_available == 5


# ---------------------------------------------------------------------------
# R4 - Failed consume returns False and does NOT mutate state
# ---------------------------------------------------------------------------
def test_r4_consume_more_than_available_returns_false():
    bucket = TokenBucket(10, tokens_available=3)
    assert bucket.consume(5) is False
    assert bucket.tokens_available == 3


def test_r4_consume_just_above_available_returns_false():
    bucket = TokenBucket(10, tokens_available=7)
    assert bucket.consume(8) is False
    assert bucket.tokens_available == 7


def test_r4_consume_from_empty_bucket_returns_false():
    bucket = TokenBucket(10, tokens_available=0)
    assert bucket.consume(1) is False
    assert bucket.tokens_available == 0


# ---------------------------------------------------------------------------
# R5 - Refill adds tokens
# ---------------------------------------------------------------------------
def test_r5_refill_adds_when_within_capacity():
    bucket = TokenBucket(10, tokens_available=2)
    bucket.refill(5)
    assert bucket.tokens_available == 7


def test_r5_refill_zero_is_noop():
    bucket = TokenBucket(10, tokens_available=4)
    bucket.refill(0)
    assert bucket.tokens_available == 4


def test_r5_refill_exactly_to_capacity():
    bucket = TokenBucket(10, tokens_available=3)
    bucket.refill(7)
    assert bucket.tokens_available == 10


# ---------------------------------------------------------------------------
# R6 - Refill caps at capacity
# ---------------------------------------------------------------------------
def test_r6_refill_over_capacity_caps():
    bucket = TokenBucket(10, tokens_available=8)
    bucket.refill(5)
    assert bucket.tokens_available == 10


def test_r6_refill_far_above_capacity_caps():
    bucket = TokenBucket(10, tokens_available=0)
    bucket.refill(1_000_000)
    assert bucket.tokens_available == 10


def test_r6_refill_full_bucket_stays_full():
    bucket = TokenBucket(10)
    bucket.refill(3)
    assert bucket.tokens_available == 10


# ---------------------------------------------------------------------------
# R7 - Capacity property
# ---------------------------------------------------------------------------
def test_r7_capacity_property_returns_constructor_value():
    bucket = TokenBucket(10)
    assert bucket.capacity == 10


def test_r7_capacity_unchanged_after_consume_and_refill():
    bucket = TokenBucket(10)
    bucket.consume(3)
    bucket.refill(1)
    assert bucket.capacity == 10


def test_r7_capacity_is_read_only():
    bucket = TokenBucket(10)
    with pytest.raises(AttributeError):
        bucket.capacity = 99  # property has no setter


# ---------------------------------------------------------------------------
# Combined / sequence behaviour
# ---------------------------------------------------------------------------
def test_sequence_consume_then_refill():
    bucket = TokenBucket(10)
    assert bucket.consume(7) is True
    assert bucket.tokens_available == 3
    bucket.refill(2)
    assert bucket.tokens_available == 5
    assert bucket.consume(6) is False
    assert bucket.tokens_available == 5
    assert bucket.consume(5) is True
    assert bucket.tokens_available == 0


def test_consume_negative_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.consume(-1)


def test_refill_negative_raises():
    bucket = TokenBucket(10, tokens_available=5)
    with pytest.raises(ValueError):
        bucket.refill(-1)


# ---------------------------------------------------------------------------
# Z3-based formal proofs of the invariant 0 <= tokens_available <= capacity
# over a single consume/refill step. These are FORMAL_CANDIDATE properties:
# pure, deterministic, finite-state arithmetic rules that mirror R3..R6.
# ---------------------------------------------------------------------------
z3 = pytest.importorskip("z3")


def test_z3_consume_preserves_invariant():
    # For all integer states (capacity, tokens, requested) satisfying
    # the bucket invariant and requested >= 0, the post-state of consume
    # must still satisfy 0 <= tokens' <= capacity.
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    requested = z3.Int("requested")

    pre = z3.And(
        capacity > 0,
        tokens >= 0,
        tokens <= capacity,
        requested >= 0,
    )

    # consume model: if requested <= tokens, tokens' = tokens - requested,
    # else tokens' = tokens (no mutation on failure).
    tokens_post = z3.If(requested <= tokens, tokens - requested, tokens)

    invariant = z3.And(tokens_post >= 0, tokens_post <= capacity)

    solver = z3.Solver()
    # Look for a counterexample: pre holds but invariant breaks.
    solver.add(pre, z3.Not(invariant))
    assert solver.check() == z3.unsat


def test_z3_refill_preserves_invariant_and_caps():
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    amount = z3.Int("amount")

    pre = z3.And(
        capacity > 0,
        tokens >= 0,
        tokens <= capacity,
        amount >= 0,
    )

    # refill model: tokens' = min(capacity, tokens + amount)
    sum_ = tokens + amount
    tokens_post = z3.If(sum_ > capacity, capacity, sum_)

    invariant = z3.And(tokens_post >= tokens, tokens_post <= capacity)

    solver = z3.Solver()
    solver.add(pre, z3.Not(invariant))
    assert solver.check() == z3.unsat


def test_z3_failed_consume_does_not_mutate():
    # When requested > tokens, the model must leave tokens unchanged.
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    requested = z3.Int("requested")

    pre = z3.And(
        capacity > 0,
        tokens >= 0,
        tokens <= capacity,
        requested > tokens,
    )

    tokens_post = z3.If(requested <= tokens, tokens - requested, tokens)

    solver = z3.Solver()
    solver.add(pre, tokens_post != tokens)
    assert solver.check() == z3.unsat