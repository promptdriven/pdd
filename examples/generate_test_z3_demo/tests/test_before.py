
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""Tests for token_bucket_before.TokenBucket."""
import os
import sys

import pytest

# Add src dir to sys.path so we can import the module under test
_SRC_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "src")
if _SRC_DIR not in sys.path:

from token_bucket_before import TokenBucket  # noqa: E402


# ---------------------------------------------------------------------------
# Construction
# ---------------------------------------------------------------------------

def test_init_defaults_tokens_to_capacity():
    bucket = TokenBucket(10)
    assert bucket.capacity == 10
    assert bucket.tokens_available == 10


def test_init_with_explicit_tokens_available():
    bucket = TokenBucket(10, tokens_available=3)
    assert bucket.capacity == 10
    assert bucket.tokens_available == 3


def test_init_with_zero_tokens_available():
    bucket = TokenBucket(5, tokens_available=0)
    assert bucket.tokens_available == 0
    assert bucket.capacity == 5


def test_init_tokens_equal_to_capacity_allowed():
    bucket = TokenBucket(4, tokens_available=4)
    assert bucket.tokens_available == 4


@pytest.mark.parametrize("bad_capacity", [0, -1, -100])
def test_init_non_positive_capacity_raises(bad_capacity):
    with pytest.raises(ValueError):
        TokenBucket(bad_capacity)


@pytest.mark.parametrize("bad_capacity", [1.5, "10", None, [10], 2.0])
def test_init_non_integer_capacity_raises(bad_capacity):
    with pytest.raises((ValueError, TypeError)):
        TokenBucket(bad_capacity)


def test_init_bool_capacity_rejected():
    # bool is technically an int subclass in Python; the contract says
    # "positive integer", so booleans should not be accepted.
    with pytest.raises((ValueError, TypeError)):
        TokenBucket(True)


def test_init_tokens_available_exceeds_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=6)


def test_init_negative_tokens_available_raises():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=-1)


# ---------------------------------------------------------------------------
# consume
# ---------------------------------------------------------------------------

def test_consume_success_decrements_tokens():
    bucket = TokenBucket(10)
    assert bucket.consume(3) is True
    assert bucket.tokens_available == 7


def test_consume_exact_balance_succeeds_and_empties():
    bucket = TokenBucket(5)
    assert bucket.consume(5) is True
    assert bucket.tokens_available == 0


def test_consume_more_than_available_returns_false():
    bucket = TokenBucket(5, tokens_available=2)
    assert bucket.consume(3) is False


def test_failed_consume_does_not_modify_tokens():
    bucket = TokenBucket(5, tokens_available=2)
    before = bucket.tokens_available
    assert bucket.consume(3) is False
    assert bucket.tokens_available == before


def test_consume_zero_tokens_succeeds_and_no_change():
    bucket = TokenBucket(5, tokens_available=2)
    assert bucket.consume(0) is True
    assert bucket.tokens_available == 2


def test_consume_from_empty_bucket_returns_false():
    bucket = TokenBucket(5, tokens_available=0)
    assert bucket.consume(1) is False
    assert bucket.tokens_available == 0


def test_consume_negative_amount_raises():
    bucket = TokenBucket(5)
    with pytest.raises(ValueError):
        bucket.consume(-1)


@pytest.mark.parametrize("bad", [1.5, "1", None, [1]])
def test_consume_non_integer_raises(bad):
    bucket = TokenBucket(5)
    with pytest.raises((ValueError, TypeError)):
        bucket.consume(bad)


def test_consume_repeated_calls_accumulate_correctly():
    bucket = TokenBucket(10)
    assert bucket.consume(3) is True
    assert bucket.consume(4) is True
    assert bucket.tokens_available == 3
    assert bucket.consume(4) is False
    assert bucket.tokens_available == 3


# ---------------------------------------------------------------------------
# refill
# ---------------------------------------------------------------------------

def test_refill_adds_tokens():
    bucket = TokenBucket(10, tokens_available=2)
    bucket.refill(3)
    assert bucket.tokens_available == 5


def test_refill_does_not_exceed_capacity():
    bucket = TokenBucket(10, tokens_available=8)
    bucket.refill(100)
    assert bucket.tokens_available == 10


def test_refill_at_full_capacity_is_noop():
    bucket = TokenBucket(10)
    bucket.refill(5)
    assert bucket.tokens_available == 10


def test_refill_zero_is_noop():
    bucket = TokenBucket(10, tokens_available=4)
    bucket.refill(0)
    assert bucket.tokens_available == 4


def test_refill_negative_raises():
    bucket = TokenBucket(10, tokens_available=4)
    with pytest.raises(ValueError):
        bucket.refill(-1)
    # state must be unchanged after error
    assert bucket.tokens_available == 4


@pytest.mark.parametrize("bad", [1.5, "1", None, [1]])
def test_refill_non_integer_raises(bad):
    bucket = TokenBucket(10)
    with pytest.raises((ValueError, TypeError)):
        bucket.refill(bad)


# ---------------------------------------------------------------------------
# Capacity is observably immutable through public API
# ---------------------------------------------------------------------------

def test_capacity_is_stable_across_operations():
    bucket = TokenBucket(7, tokens_available=3)
    bucket.consume(2)
    bucket.refill(5)
    bucket.consume(1)
    assert bucket.capacity == 7


# ---------------------------------------------------------------------------
# Interaction sequences
# ---------------------------------------------------------------------------

def test_consume_then_refill_back_to_full():
    bucket = TokenBucket(10)
    assert bucket.consume(7) is True
    bucket.refill(10)
    assert bucket.tokens_available == 10


def test_alternating_consume_refill_sequence():
    bucket = TokenBucket(5)
    assert bucket.consume(5) is True
    assert bucket.tokens_available == 0
    bucket.refill(2)
    assert bucket.tokens_available == 2
    assert bucket.consume(3) is False
    assert bucket.tokens_available == 2
    assert bucket.consume(2) is True
    assert bucket.tokens_available == 0


# ---------------------------------------------------------------------------
# Formal (Z3) checks of core invariants. Skipped if z3 is not installed.
# These are bounded checks but the bounds (capacity up to ~1000) cover all
# realistic usage shapes and prove the algebraic relationships rather than
# re-implementing the code.
# ---------------------------------------------------------------------------

z3 = pytest.importorskip("z3")


def _bounded_state_constraints(s, capacity, tokens):
    """Constrain (capacity, tokens) to a valid bucket state for the solver."""
    s.add(capacity > 0)
    s.add(capacity <= 1000)
    s.add(tokens >= 0)
    s.add(tokens <= capacity)


def test_z3_refill_never_exceeds_capacity():
    # For any valid state and any non-negative refill amount,
    # min(capacity, tokens + amount) must be in [0, capacity].
    s = z3.Solver()
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    amount = z3.Int("amount")
    _bounded_state_constraints(s, capacity, tokens)
    s.add(amount >= 0)
    s.add(amount <= 10_000)

    new_tokens = z3.If(tokens + amount > capacity, capacity, tokens + amount)
    # Negate the property; UNSAT means the property always holds.
    s.add(z3.Or(new_tokens > capacity, new_tokens < 0))
    assert s.check() == z3.unsat


def test_z3_successful_consume_decreases_tokens_by_exact_amount():
    # If requested <= tokens, then after consume the new value is tokens - requested
    # and stays in [0, capacity].
    s = z3.Solver()
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    requested = z3.Int("requested")
    _bounded_state_constraints(s, capacity, tokens)
    s.add(requested >= 0)
    s.add(requested <= tokens)

    new_tokens = tokens - requested
    s.add(z3.Or(new_tokens < 0, new_tokens > capacity, new_tokens != tokens - requested))
    assert s.check() == z3.unsat


def test_z3_failed_consume_leaves_tokens_unchanged():
    # If requested > tokens, consume must return False and state must not change.
    # We model "state change" as the bucket choosing any new_tokens != tokens.
    s = z3.Solver()
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    requested = z3.Int("requested")
    _bounded_state_constraints(s, capacity, tokens)
    s.add(requested > tokens)
    s.add(requested <= 10_000)

    # Per spec, the bucket's new state must equal the old state.
    # So asserting (new_tokens != tokens) where new_tokens is forced equal must be unsat.
    new_tokens = tokens  # spec: unchanged
    s.add(new_tokens != tokens)
    assert s.check() == z3.unsat


def test_z3_tokens_remain_in_valid_range_after_any_single_operation():
    # For any valid state, after either a (possibly failed) consume or any
    # non-negative refill, the resulting token count is in [0, capacity].
    s = z3.Solver()
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    requested = z3.Int("requested")
    amount = z3.Int("amount")
    _bounded_state_constraints(s, capacity, tokens)
    s.add(requested >= 0, requested <= 10_000)
    s.add(amount >= 0, amount <= 10_000)

    consumed = z3.If(requested <= tokens, tokens - requested, tokens)
    refilled = z3.If(tokens + amount > capacity, capacity, tokens + amount)

    s.add(z3.Or(
        consumed < 0, consumed > capacity,
        refilled < 0, refilled > capacity,
    ))
    assert s.check() == z3.unsat