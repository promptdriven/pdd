
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest
from src.token_bucket import TokenBucket


# ---------- Construction ----------

def test_init_default_starts_full():
    b = TokenBucket(10)
    assert b.capacity == 10
    assert b.tokens_available == 10


def test_init_with_initial_tokens():
    b = TokenBucket(10, tokens_available=3)
    assert b.capacity == 10
    assert b.tokens_available == 3


def test_init_with_zero_initial_tokens():
    b = TokenBucket(5, tokens_available=0)
    assert b.tokens_available == 0
    assert b.capacity == 5


def test_init_initial_equal_to_capacity():
    b = TokenBucket(7, tokens_available=7)
    assert b.tokens_available == 7


@pytest.mark.parametrize("cap", [0, -1, -100])
def test_init_non_positive_capacity_raises(cap):
    with pytest.raises(ValueError):
        TokenBucket(cap)


@pytest.mark.parametrize("cap", [1.5, "10", None, [], 2.0])
def test_init_non_integer_capacity_raises(cap):
    with pytest.raises(ValueError):
        TokenBucket(cap)


def test_init_bool_capacity_raises():
    # bool is a subclass of int in Python; should still be rejected
    with pytest.raises(ValueError):
        TokenBucket(True)
    with pytest.raises(ValueError):
        TokenBucket(False)


def test_init_initial_tokens_negative_raises():
    with pytest.raises(ValueError):
        TokenBucket(10, tokens_available=-1)


def test_init_initial_tokens_above_capacity_raises():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=6)


@pytest.mark.parametrize("tok", [1.5, "3", [], 2.0])
def test_init_non_integer_initial_tokens_raises(tok):
    with pytest.raises(ValueError):
        TokenBucket(10, tokens_available=tok)


def test_init_bool_initial_tokens_raises():
    with pytest.raises(ValueError):
        TokenBucket(10, tokens_available=True)


# ---------- consume ----------

def test_consume_success_decreases_tokens():
    b = TokenBucket(10)
    assert b.consume(4) is True
    assert b.tokens_available == 6


def test_consume_exact_amount_succeeds():
    b = TokenBucket(5)
    assert b.consume(5) is True
    assert b.tokens_available == 0


def test_consume_more_than_available_fails_and_preserves_state():
    b = TokenBucket(10, tokens_available=3)
    assert b.consume(4) is False
    assert b.tokens_available == 3


def test_consume_zero_succeeds_and_does_not_change_state():
    b = TokenBucket(10, tokens_available=5)
    assert b.consume(0) is True
    assert b.tokens_available == 5


def test_consume_when_empty_fails():
    b = TokenBucket(10, tokens_available=0)
    assert b.consume(1) is False
    assert b.tokens_available == 0


def test_consume_multiple_sequential():
    b = TokenBucket(10)
    assert b.consume(3) is True
    assert b.consume(3) is True
    assert b.consume(5) is False  # only 4 left
    assert b.tokens_available == 4
    assert b.consume(4) is True
    assert b.tokens_available == 0


def test_consume_negative_raises():
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.consume(-1)


@pytest.mark.parametrize("val", [1.5, "1", None, []])
def test_consume_non_integer_raises(val):
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.consume(val)


def test_consume_bool_raises():
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.consume(True)


# ---------- refill ----------

def test_refill_adds_tokens():
    b = TokenBucket(10, tokens_available=2)
    b.refill(3)
    assert b.tokens_available == 5


def test_refill_does_not_exceed_capacity():
    b = TokenBucket(10, tokens_available=8)
    b.refill(100)
    assert b.tokens_available == 10


def test_refill_zero_is_noop():
    b = TokenBucket(10, tokens_available=4)
    b.refill(0)
    assert b.tokens_available == 4


def test_refill_full_bucket_stays_full():
    b = TokenBucket(5)
    b.refill(1)
    assert b.tokens_available == 5


def test_refill_negative_raises():
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.refill(-1)


@pytest.mark.parametrize("val", [1.5, "1", None, []])
def test_refill_non_integer_raises(val):
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.refill(val)


def test_refill_bool_raises():
    b = TokenBucket(10)
    with pytest.raises(ValueError):
        b.refill(True)


# ---------- properties / interaction ----------

def test_capacity_immutable_via_public_api():
    b = TokenBucket(10)
    with pytest.raises(AttributeError):
        b.capacity = 99
    assert b.capacity == 10


def test_tokens_available_immutable_via_public_api():
    b = TokenBucket(10)
    with pytest.raises(AttributeError):
        b.tokens_available = 99
    assert b.tokens_available == 10


def test_consume_then_refill_cycle():
    b = TokenBucket(10)
    assert b.consume(7) is True
    assert b.tokens_available == 3
    b.refill(5)
    assert b.tokens_available == 8
    b.refill(10)
    assert b.tokens_available == 10
    assert b.consume(10) is True
    assert b.tokens_available == 0
    assert b.consume(1) is False


# ---------- Z3-based invariant proofs (formal candidates) ----------
# These are bounded/algebraic checks over the abstract semantics of the bucket.

def test_z3_consume_preserves_invariant_0_le_tokens_le_capacity():
    z3 = pytest.importorskip("z3")
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    req = z3.Int("req")
    s = z3.Solver()
    s.add(capacity > 0)
    s.add(tokens >= 0, tokens <= capacity)
    s.add(req >= 0)
    # New tokens after consume per spec
    new_tokens = z3.If(req > tokens, tokens, tokens - req)
    # Try to find a counterexample to invariant
    s.add(z3.Or(new_tokens < 0, new_tokens > capacity))
    assert s.check() == z3.unsat


def test_z3_refill_preserves_invariant_0_le_tokens_le_capacity():
    z3 = pytest.importorskip("z3")
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    amount = z3.Int("amount")
    s = z3.Solver()
    s.add(capacity > 0)
    s.add(tokens >= 0, tokens <= capacity)
    s.add(amount >= 0)
    sum_ = tokens + amount
    new_tokens = z3.If(sum_ > capacity, capacity, sum_)
    s.add(z3.Or(new_tokens < 0, new_tokens > capacity))
    assert s.check() == z3.unsat


def test_z3_failed_consume_does_not_change_tokens():
    z3 = pytest.importorskip("z3")
    tokens = z3.Int("tokens")
    req = z3.Int("req")
    s = z3.Solver()
    s.add(tokens >= 0)
    s.add(req >= 0)
    s.add(req > tokens)  # failure condition
    # On failure, tokens must remain tokens; model spec uses If(req > tokens, tokens, tokens - req)
    new_tokens = z3.If(req > tokens, tokens, tokens - req)
    s.add(new_tokens != tokens)
    assert s.check() == z3.unsat


def test_z3_refill_monotonic_non_decreasing():
    z3 = pytest.importorskip("z3")
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    amount = z3.Int("amount")
    s = z3.Solver()
    s.add(capacity > 0)
    s.add(tokens >= 0, tokens <= capacity)
    s.add(amount >= 0)
    sum_ = tokens + amount
    new_tokens = z3.If(sum_ > capacity, capacity, sum_)
    s.add(new_tokens < tokens)
    assert s.check() == z3.unsat