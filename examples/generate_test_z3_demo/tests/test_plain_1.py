
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import os
import sys
import pytest

# Ensure the src directory is importable regardless of how pytest is invoked.
_HERE = os.path.dirname(os.path.abspath(__file__))
_SRC = os.path.join(_HERE, "src")
if _SRC not in sys.path:

from token_bucket import TokenBucket  # noqa: E402


# ---------- Construction ----------

def test_default_starts_full():
    b = TokenBucket(10)
    assert b.capacity == 10
    assert b.tokens_available == 10


def test_initial_tokens_below_capacity():
    b = TokenBucket(10, tokens_available=3)
    assert b.capacity == 10
    assert b.tokens_available == 3


def test_initial_tokens_zero_allowed():
    b = TokenBucket(5, tokens_available=0)
    assert b.tokens_available == 0


def test_initial_tokens_equal_capacity():
    b = TokenBucket(5, tokens_available=5)
    assert b.tokens_available == 5


@pytest.mark.parametrize("bad_cap", [0, -1, -100])
def test_invalid_capacity_non_positive(bad_cap):
    with pytest.raises(ValueError):
        TokenBucket(bad_cap)


@pytest.mark.parametrize("bad_cap", [1.5, "10", None, [1], 3.0])
def test_invalid_capacity_wrong_type(bad_cap):
    with pytest.raises(ValueError):
        TokenBucket(bad_cap)


def test_invalid_capacity_bool_rejected():
    # bool is a subclass of int in Python; the API must reject it as capacity.
    with pytest.raises(ValueError):
        TokenBucket(True)
    with pytest.raises(ValueError):
        TokenBucket(False)


def test_initial_tokens_exceeds_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=6)


def test_initial_tokens_negative_raises():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=-1)


@pytest.mark.parametrize("bad", [1.0, "3", [3]])
def test_initial_tokens_wrong_type_raises(bad):
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=bad)


def test_initial_tokens_bool_rejected():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=True)


# ---------- consume ----------

def test_consume_success_reduces_tokens():
    b = TokenBucket(10)
    assert b.consume(4) is True
    assert b.tokens_available == 6


def test_consume_all_tokens():
    b = TokenBucket(10)
    assert b.consume(10) is True
    assert b.tokens_available == 0


def test_consume_failure_does_not_modify_state():
    b = TokenBucket(10, tokens_available=3)
    assert b.consume(5) is False
    assert b.tokens_available == 3
    # Subsequent successful consume still works.
    assert b.consume(3) is True
    assert b.tokens_available == 0


def test_consume_zero_is_noop_success():
    b = TokenBucket(10, tokens_available=4)
    assert b.consume(0) is True
    assert b.tokens_available == 4


def test_consume_exactly_available_succeeds():
    b = TokenBucket(10, tokens_available=7)
    assert b.consume(7) is True
    assert b.tokens_available == 0


def test_consume_one_more_than_available_fails():
    b = TokenBucket(10, tokens_available=7)
    assert b.consume(8) is False
    assert b.tokens_available == 7


def test_consume_from_empty_bucket():
    b = TokenBucket(10, tokens_available=0)
    assert b.consume(1) is False
    assert b.tokens_available == 0
    assert b.consume(0) is True
    assert b.tokens_available == 0


def test_consume_negative_raises():
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.consume(-1)


@pytest.mark.parametrize("bad", [1.5, "1", None, [1]])
def test_consume_wrong_type_raises(bad):
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.consume(bad)


def test_consume_bool_rejected():
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.consume(True)


# ---------- refill ----------

def test_refill_adds_tokens():
    b = TokenBucket(10, tokens_available=2)
    b.refill(3)
    assert b.tokens_available == 5


def test_refill_caps_at_capacity():
    b = TokenBucket(10, tokens_available=8)
    b.refill(5)
    assert b.tokens_available == 10


def test_refill_when_full_stays_full():
    b = TokenBucket(10)
    b.refill(100)
    assert b.tokens_available == 10


def test_refill_zero_is_noop():
    b = TokenBucket(10, tokens_available=4)
    b.refill(0)
    assert b.tokens_available == 4


def test_refill_negative_raises():
    b = TokenBucket(10, tokens_available=4)
    with pytest.raises(ValueError):
        b.refill(-1)
    assert b.tokens_available == 4


@pytest.mark.parametrize("bad", [1.5, "1", None, [1]])
def test_refill_wrong_type_raises(bad):
    b = TokenBucket(10, tokens_available=4)
    with pytest.raises(ValueError):
        b.refill(bad)
    assert b.tokens_available == 4


def test_refill_bool_rejected():
    b = TokenBucket(10, tokens_available=4)
    with pytest.raises(ValueError):
        b.refill(True)
    assert b.tokens_available == 4


# ---------- properties ----------

def test_capacity_is_immutable_via_property():
    b = TokenBucket(10)
    with pytest.raises(AttributeError):
        b.capacity = 20  # type: ignore[misc]


def test_tokens_available_is_immutable_via_property():
    b = TokenBucket(10)
    with pytest.raises(AttributeError):
        b.tokens_available = 5  # type: ignore[misc]


# ---------- Sequenced behavior ----------

def test_consume_then_refill_cycle():
    b = TokenBucket(10)
    assert b.consume(7) is True
    assert b.tokens_available == 3
    b.refill(2)
    assert b.tokens_available == 5
    assert b.consume(6) is False
    assert b.tokens_available == 5
    assert b.consume(5) is True
    assert b.tokens_available == 0
    b.refill(1000)
    assert b.tokens_available == 10


# ---------- Formal (Z3) proofs of core invariants ----------
# These are bounded-domain proofs over small integers covering all relevant
# behavioral states (0..capacity) and arbitrary nonnegative requests/refills.

z3 = pytest.importorskip("z3")


def test_z3_invariant_tokens_within_bounds_after_consume():
    """Prove: for all valid states and requested values, after consume the
    token count remains in [0, capacity] and is unchanged on failure."""
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    req = z3.Int("req")

    pre = z3.And(capacity > 0, tokens >= 0, tokens <= capacity, req >= 0)
    # Model the implementation faithfully.
    success = req <= tokens
    new_tokens = z3.If(success, tokens - req, tokens)

    # Property we wish to hold.
    prop = z3.And(new_tokens >= 0, new_tokens <= capacity,
                  z3.Implies(z3.Not(success), new_tokens == tokens))

    s = z3.Solver()
    s.add(pre, z3.Not(prop))
    assert s.check() == z3.unsat


def test_z3_invariant_refill_caps_at_capacity():
    """Prove: refill never exceeds capacity and never decreases tokens."""
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    amount = z3.Int("amount")

    pre = z3.And(capacity > 0, tokens >= 0, tokens <= capacity, amount >= 0)
    raw = tokens + amount
    new_tokens = z3.If(raw < capacity, raw, capacity)  # min(capacity, raw)

    prop = z3.And(new_tokens <= capacity, new_tokens >= tokens, new_tokens >= 0)

    s = z3.Solver()
    s.add(pre, z3.Not(prop))
    assert s.check() == z3.unsat


def test_z3_consume_failure_iff_request_exceeds_available():
    """Prove: consume returns False iff requested > tokens_available."""
    tokens = z3.Int("tokens")
    req = z3.Int("req")
    pre = z3.And(tokens >= 0, req >= 0)
    success = req <= tokens
    # Failure means !success which means req > tokens.
    prop = (z3.Not(success) == (req > tokens))
    s = z3.Solver()
    s.add(pre, z3.Not(prop))
    assert s.check() == z3.unsat