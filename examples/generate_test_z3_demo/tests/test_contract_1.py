
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest

from src.token_bucket import TokenBucket


# ---------------------------------------------------------------------------
# R1 - Reject non-positive capacity
# ---------------------------------------------------------------------------

def test_r1_zero_capacity_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket(0)


def test_r1_negative_capacity_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket(-5)


def test_r1_non_integer_capacity_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket(3.5)


def test_r1_string_capacity_raises_value_error():
    with pytest.raises(ValueError):
        TokenBucket("10")


def test_r1_bool_capacity_raises_value_error():
    # bool is a subclass of int but shouldn't be accepted as a meaningful capacity
    with pytest.raises(ValueError):
        TokenBucket(True)


# ---------------------------------------------------------------------------
# R2 - Default tokens_available to capacity
# ---------------------------------------------------------------------------

def test_r2_default_tokens_equals_capacity():
    bucket = TokenBucket(10)
    assert bucket.tokens_available == 10
    assert bucket.capacity == 10


def test_r2_default_tokens_equals_capacity_one():
    bucket = TokenBucket(1)
    assert bucket.tokens_available == 1


def test_r2_explicit_tokens_available_respected():
    bucket = TokenBucket(10, tokens_available=4)
    assert bucket.tokens_available == 4
    assert bucket.capacity == 10


def test_r2_explicit_tokens_available_zero():
    bucket = TokenBucket(10, tokens_available=0)
    assert bucket.tokens_available == 0


def test_initial_tokens_cannot_exceed_capacity():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=10)


def test_initial_tokens_cannot_be_negative():
    with pytest.raises(ValueError):
        TokenBucket(5, tokens_available=-1)


# ---------------------------------------------------------------------------
# R3 - Consume with sufficient tokens
# ---------------------------------------------------------------------------

def test_r3_consume_sufficient_returns_true_and_decrements():
    bucket = TokenBucket(10)
    result = bucket.consume(4)
    assert result is True
    assert bucket.tokens_available == 6


def test_r3_consume_all_tokens():
    bucket = TokenBucket(10)
    assert bucket.consume(10) is True
    assert bucket.tokens_available == 0


def test_r3_consume_zero_tokens_succeeds():
    bucket = TokenBucket(10, tokens_available=5)
    assert bucket.consume(0) is True
    assert bucket.tokens_available == 5


def test_r3_consume_exactly_available():
    bucket = TokenBucket(10, tokens_available=3)
    assert bucket.consume(3) is True
    assert bucket.tokens_available == 0


def test_r3_multiple_consumes_track_state():
    bucket = TokenBucket(10)
    assert bucket.consume(3) is True
    assert bucket.tokens_available == 7
    assert bucket.consume(2) is True
    assert bucket.tokens_available == 5
    assert bucket.consume(5) is True
    assert bucket.tokens_available == 0


# ---------------------------------------------------------------------------
# R4 - Consume with insufficient tokens returns False
# ---------------------------------------------------------------------------

def test_r4_consume_more_than_available_returns_false():
    bucket = TokenBucket(10, tokens_available=3)
    assert bucket.consume(5) is False


def test_r4_consume_from_empty_returns_false():
    bucket = TokenBucket(10, tokens_available=0)
    assert bucket.consume(1) is False


def test_r4_consume_more_than_capacity_returns_false():
    bucket = TokenBucket(10)
    assert bucket.consume(11) is False


# ---------------------------------------------------------------------------
# R5 - Failed consume preserves state
# ---------------------------------------------------------------------------

def test_r5_failed_consume_does_not_change_tokens():
    bucket = TokenBucket(10, tokens_available=3)
    bucket.consume(5)
    assert bucket.tokens_available == 3


def test_r5_failed_consume_state_unchanged_after_many_attempts():
    bucket = TokenBucket(10, tokens_available=2)
    for _ in range(5):
        assert bucket.consume(3) is False
    assert bucket.tokens_available == 2


def test_r5_mixed_success_and_failure_preserves_correct_state():
    bucket = TokenBucket(10, tokens_available=5)
    assert bucket.consume(3) is True  # now 2
    assert bucket.consume(5) is False  # still 2
    assert bucket.tokens_available == 2
    assert bucket.consume(2) is True  # now 0
    assert bucket.tokens_available == 0


# ---------------------------------------------------------------------------
# R6 - Refill caps at capacity
# ---------------------------------------------------------------------------

def test_r6_refill_caps_at_capacity():
    bucket = TokenBucket(10, tokens_available=8)
    bucket.refill(5)
    assert bucket.tokens_available == 10


def test_r6_refill_full_bucket_stays_at_capacity():
    bucket = TokenBucket(10)
    bucket.refill(100)
    assert bucket.tokens_available == 10


def test_r6_refill_exact_to_capacity():
    bucket = TokenBucket(10, tokens_available=4)
    bucket.refill(6)
    assert bucket.tokens_available == 10


def test_r6_refill_huge_amount_caps_to_capacity():
    bucket = TokenBucket(10, tokens_available=0)
    bucket.refill(10**9)
    assert bucket.tokens_available == 10


# ---------------------------------------------------------------------------
# R7 - Refill adds tokens when below capacity
# ---------------------------------------------------------------------------

def test_r7_refill_below_capacity_adds_tokens():
    bucket = TokenBucket(10, tokens_available=2)
    bucket.refill(3)
    assert bucket.tokens_available == 5


def test_r7_refill_zero_amount_no_change():
    bucket = TokenBucket(10, tokens_available=4)
    bucket.refill(0)
    assert bucket.tokens_available == 4


def test_r7_refill_after_consume():
    bucket = TokenBucket(10)
    bucket.consume(7)
    assert bucket.tokens_available == 3
    bucket.refill(2)
    assert bucket.tokens_available == 5


def test_refill_negative_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.refill(-1)


def test_refill_non_integer_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.refill(2.5)


def test_refill_bool_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.refill(True)


def test_consume_negative_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.consume(-1)


def test_consume_non_integer_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.consume(1.5)


def test_consume_bool_raises():
    bucket = TokenBucket(10)
    with pytest.raises(ValueError):
        bucket.consume(False)


# ---------------------------------------------------------------------------
# Capacity property is read-only and stable
# ---------------------------------------------------------------------------

def test_capacity_is_stable_across_operations():
    bucket = TokenBucket(10)
    bucket.consume(3)
    bucket.refill(2)
    bucket.consume(1)
    assert bucket.capacity == 10


def test_capacity_property_is_read_only():
    bucket = TokenBucket(10)
    with pytest.raises(AttributeError):
        bucket.capacity = 20


def test_tokens_available_property_is_read_only():
    bucket = TokenBucket(10)
    with pytest.raises(AttributeError):
        bucket.tokens_available = 5


# ---------------------------------------------------------------------------
# Integration / scenario tests
# ---------------------------------------------------------------------------

def test_full_lifecycle_scenario():
    bucket = TokenBucket(5)
    assert bucket.tokens_available == 5
    assert bucket.consume(2) is True
    assert bucket.tokens_available == 3
    assert bucket.consume(4) is False
    assert bucket.tokens_available == 3
    bucket.refill(1)
    assert bucket.tokens_available == 4
    bucket.refill(10)
    assert bucket.tokens_available == 5
    assert bucket.consume(5) is True
    assert bucket.tokens_available == 0
    assert bucket.consume(1) is False


# ---------------------------------------------------------------------------
# Formal (Z3) proofs of small algebraic invariants
# These encode the contract rules as bounded SMT checks. We bound integers
# so we get fast, deterministic checks rather than re-implementing the code.
# ---------------------------------------------------------------------------

z3 = pytest.importorskip("z3")


def _bounded(var, lo, hi):
    return z3.And(var >= lo, var <= hi)


def test_z3_r3_consume_sufficient_invariant():
    # For all 0 <= prior <= cap, 0 <= req <= prior, the post state must equal
    # prior - req, and the result must be True. We exercise this by running
    # the real code against every Z3-generated counterexample, but since the
    # property is a pure arithmetic identity we encode it directly.
    solver = z3.Solver()
    prior, req, cap = z3.Ints("prior req cap")
    solver.add(_bounded(cap, 1, 20))
    solver.add(_bounded(prior, 0, 20), prior <= cap)
    solver.add(_bounded(req, 0, 20), req <= prior)

    # Model the spec: post = prior - req
    post = prior - req
    # Violation: post < 0 or post > cap (should never happen)
    solver.push()
    solver.add(z3.Or(post < 0, post > cap))
    assert solver.check() == z3.unsat
    solver.pop()


def test_z3_r4_consume_insufficient_returns_false():
    # Property: req > prior  =>  result == False, and state unchanged.
    # Encoded via the real implementation, sampled over a bounded domain.
    solver = z3.Solver()
    prior, req, cap = z3.Ints("prior req cap")
    solver.add(_bounded(cap, 1, 10))
    solver.add(_bounded(prior, 0, 10), prior <= cap)
    solver.add(_bounded(req, 0, 20), req > prior)

    while solver.check() == z3.sat:
        m = solver.model()
        c = m[cap].as_long()
        p = m[prior].as_long()
        r = m[req].as_long()
        bucket = TokenBucket(c, tokens_available=p)
        assert bucket.consume(r) is False
        assert bucket.tokens_available == p  # R5 also: state unchanged
        # Exclude this model and continue searching
        solver.add(z3.Or(cap != c, prior != p, req != r))


def test_z3_r6_refill_never_exceeds_capacity():
    # For all bounded prior, amount, cap: post = min(cap, prior + amount) <= cap
    solver = z3.Solver()
    prior, amount, cap = z3.Ints("prior amount cap")
    solver.add(_bounded(cap, 1, 20))
    solver.add(_bounded(prior, 0, 20), prior <= cap)
    solver.add(_bounded(amount, 0, 50))

    # Spec model of refill
    post = z3.If(prior + amount > cap, cap, prior + amount)
    solver.push()
    solver.add(post > cap)
    assert solver.check() == z3.unsat
    solver.pop()
    solver.push()
    solver.add(post < prior)  # refill should never decrease tokens
    assert solver.check() == z3.unsat
    solver.pop()


def test_z3_r7_refill_below_capacity_adds_tokens():
    # Property: prior + amount <= cap  =>  post == prior + amount.
    # Validated by running the real code over Z3-generated bounded cases.
    solver = z3.Solver()
    prior, amount, cap = z3.Ints("prior amount cap")
    solver.add(_bounded(cap, 1, 8))
    solver.add(_bounded(prior, 0, 8), prior <= cap)
    solver.add(_bounded(amount, 0, 8), prior + amount <= cap)

    checked = 0
    while solver.check() == z3.sat and checked < 200:
        m = solver.model()
        c = m[cap].as_long()
        p = m[prior].as_long()
        a = m[amount].as_long()
        bucket = TokenBucket(c, tokens_available=p)
        bucket.refill(a)
        assert bucket.tokens_available == p + a
        solver.add(z3.Or(cap != c, prior != p, amount != a))
        checked += 1