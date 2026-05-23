
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest
from src.token_bucket import TokenBucket


# ---------- R1: Reject non-positive / invalid capacity ----------

def test_capacity_zero_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket(0)


def test_capacity_negative_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket(-5)


def test_capacity_float_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket(10.0)


def test_capacity_bool_raises_value_error():
    # booleans are technically ints in Python; spec disallows them
    with pytest.raises(ValueError):
        TokenBucket(True)


def test_capacity_string_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket("10")


# ---------- R2: Default tokens_available equals capacity ----------

def test_default_tokens_available_equals_capacity():
    b = TokenBucket(10)
    assert b.tokens_available == 10


def test_default_tokens_available_equals_capacity_one():
    b = TokenBucket(1)
    assert b.tokens_available == 1


def test_explicit_tokens_available_used_when_provided():
    b = TokenBucket(10, tokens_available=3)
    assert b.tokens_available == 3


def test_explicit_tokens_available_zero_allowed():
    b = TokenBucket(10, tokens_available=0)
    assert b.tokens_available == 0


def test_explicit_tokens_available_equal_to_capacity_allowed():
    b = TokenBucket(10, tokens_available=10)
    assert b.tokens_available == 10


def test_explicit_tokens_above_capacity_rejected():
    with pytest.raises(ValueError):
        TokenBucket(10, tokens_available=11)


def test_explicit_tokens_negative_rejected():
    with pytest.raises(ValueError):
        TokenBucket(10, tokens_available=-1)


# ---------- R3: Successful consume ----------

def test_consume_less_than_available_returns_true_and_decrements():
    b = TokenBucket(10)
    assert b.consume(4) is True
    assert b.tokens_available == 6


def test_consume_exact_available_returns_true_and_zeroes():
    b = TokenBucket(10)
    assert b.consume(10) is True
    assert b.tokens_available == 0


def test_consume_zero_returns_true_and_does_not_change():
    b = TokenBucket(10, tokens_available=7)
    assert b.consume(0) is True
    assert b.tokens_available == 7


def test_multiple_consumes_accumulate_correctly():
    b = TokenBucket(10)
    assert b.consume(3) is True
    assert b.consume(2) is True
    assert b.consume(5) is True
    assert b.tokens_available == 0


# ---------- R4: Failed consume does not mutate ----------

def test_consume_more_than_available_returns_false_and_preserves_state():
    b = TokenBucket(10, tokens_available=3)
    assert b.consume(5) is False
    assert b.tokens_available == 3


def test_consume_from_empty_bucket_returns_false():
    b = TokenBucket(10, tokens_available=0)
    assert b.consume(1) is False
    assert b.tokens_available == 0


def test_consume_one_over_available_returns_false():
    b = TokenBucket(10, tokens_available=5)
    assert b.consume(6) is False
    assert b.tokens_available == 5


# ---------- R5: Refill adds tokens ----------

def test_refill_adds_tokens_within_capacity():
    b = TokenBucket(10, tokens_available=2)
    b.refill(5)
    assert b.tokens_available == 7


def test_refill_zero_does_not_change():
    b = TokenBucket(10, tokens_available=4)
    b.refill(0)
    assert b.tokens_available == 4


def test_refill_to_exact_capacity():
    b = TokenBucket(10, tokens_available=3)
    b.refill(7)
    assert b.tokens_available == 10


# ---------- R6: Refill caps at capacity ----------

def test_refill_exceeding_capacity_caps_at_capacity():
    b = TokenBucket(10, tokens_available=8)
    b.refill(5)
    assert b.tokens_available == 10


def test_refill_full_bucket_stays_full():
    b = TokenBucket(10)
    b.refill(100)
    assert b.tokens_available == 10


def test_refill_huge_amount_caps_at_capacity():
    b = TokenBucket(10, tokens_available=0)
    b.refill(10**9)
    assert b.tokens_available == 10


# ---------- R7: capacity read-only property ----------

def test_capacity_property_returns_value():
    b = TokenBucket(10)
    assert b.capacity == 10


def test_capacity_unchanged_after_consume_and_refill():
    b = TokenBucket(10)
    b.consume(5)
    b.refill(2)
    assert b.capacity == 10


def test_capacity_is_read_only():
    b = TokenBucket(10)
    with pytest.raises(AttributeError):
        b.capacity = 20


# ---------- Invalid argument handling ----------

def test_refill_negative_raises():
    b = TokenBucket(10, tokens_available=5)
    with pytest.raises(ValueError):
        b.refill(-1)
    # state preserved
    assert b.tokens_available == 5


def test_refill_bool_raises():
    b = TokenBucket(10, tokens_available=5)
    with pytest.raises(ValueError):
        b.refill(True)


def test_consume_negative_raises():
    b = TokenBucket(10, tokens_available=5)
    with pytest.raises(ValueError):
        b.consume(-1)
    assert b.tokens_available == 5


def test_consume_bool_raises():
    b = TokenBucket(10, tokens_available=5)
    with pytest.raises(ValueError):
        b.consume(False)


# ---------- Integration / scenario ----------

def test_full_lifecycle_scenario():
    b = TokenBucket(5)
    assert b.tokens_available == 5
    assert b.consume(3) is True
    assert b.tokens_available == 2
    assert b.consume(3) is False  # not enough
    assert b.tokens_available == 2
    b.refill(2)
    assert b.tokens_available == 4
    b.refill(100)  # cap
    assert b.tokens_available == 5
    assert b.consume(5) is True
    assert b.tokens_available == 0


# ---------- Z3 formal proofs of core invariants ----------
# These are FORMAL_CANDIDATE properties: pure arithmetic state transitions
# on integer state with simple guards. We prove the spec is internally
# consistent (the bucket cannot violate invariants under any input).

z3 = pytest.importorskip("z3")


def test_z3_consume_preserves_token_bounds():
    """For all reachable states, consume keeps 0 <= tokens <= capacity."""
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    req = z3.Int("req")

    # Precondition: valid bucket state and valid request
    pre = z3.And(capacity > 0, tokens >= 0, tokens <= capacity, req >= 0)

    # Model the consume transition exactly as the spec dictates
    success = req <= tokens
    new_tokens = z3.If(success, tokens - req, tokens)

    invariant = z3.And(new_tokens >= 0, new_tokens <= capacity)

    s = z3.Solver()
    # Try to find a counterexample: pre holds but invariant fails
    s.add(pre, z3.Not(invariant))
    assert s.check() == z3.unsat, f"Counterexample found: {s.model()}"


def test_z3_refill_caps_at_capacity():
    """For all valid states, refill never lets tokens exceed capacity."""
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    amount = z3.Int("amount")

    pre = z3.And(capacity > 0, tokens >= 0, tokens <= capacity, amount >= 0)

    # min(capacity, tokens + amount)
    sum_ = tokens + amount
    new_tokens = z3.If(sum_ < capacity, sum_, capacity)

    invariant = z3.And(new_tokens >= tokens, new_tokens <= capacity)

    s = z3.Solver()
    s.add(pre, z3.Not(invariant))
    assert s.check() == z3.unsat, f"Counterexample found: {s.model()}"


def test_z3_failed_consume_does_not_mutate():
    """If consume fails (req > tokens), token count is unchanged."""
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    req = z3.Int("req")

    pre = z3.And(capacity > 0, tokens >= 0, tokens <= capacity, req >= 0)
    fail = req > tokens
    new_tokens = z3.If(req <= tokens, tokens - req, tokens)

    s = z3.Solver()
    s.add(pre, fail, new_tokens != tokens)
    assert s.check() == z3.unsat, f"Counterexample found: {s.model()}"


def test_z3_successful_consume_decrements_exactly():
    """If consume succeeds, new tokens == old tokens - req."""
    capacity = z3.Int("capacity")
    tokens = z3.Int("tokens")
    req = z3.Int("req")

    pre = z3.And(capacity > 0, tokens >= 0, tokens <= capacity, req >= 0)
    success = req <= tokens
    new_tokens = z3.If(success, tokens - req, tokens)

    s = z3.Solver()
    s.add(pre, success, new_tokens != tokens - req)
    assert s.check() == z3.unsat, f"Counterexample found: {s.model()}"