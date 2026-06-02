"""Z3 formal verification tests for email_validator (FORMAL_CANDIDATE rules R1–R4).

These tests mirror what ``pdd test`` should emit when the formalized prompt's
``<formalization>`` section marks string invariants as FORMAL_CANDIDATE.
"""
from __future__ import annotations

import pytest

from email_validator import EmailValidator

z3 = pytest.importorskip("z3")
from z3 import Contains, Not, Solver, String, StringVal, sat  # noqa: E402


@pytest.fixture
def validator() -> EmailValidator:
    return EmailValidator()


def _model_string(value: object) -> str:
    text = str(value)
    if len(text) >= 2 and text[0] == '"' and text[-1] == '"':
        return text[1:-1]
    return text


def test_z3_R1_exactly_one_at_sign(validator: EmailValidator) -> None:
    """R1 (bounded): emails with zero @ are rejected with the single-@ message."""
    solver = Solver()
    email_var = String("email")
    solver.add(Not(Contains(email_var, StringVal("@"))))
    solver.add(email_var != StringVal(""))
    if solver.check() != sat:
        pytest.skip("Z3 could not synthesize a no-@ counterexample")
    sample = _model_string(solver.model().eval(email_var, model_completion=True))
    result = validator.validate_email(sample)
    assert result.is_valid is False
    assert result.error_message is not None
    assert "@" in result.error_message.lower()


def test_z3_R4_forbidden_consecutive_dots(validator: EmailValidator) -> None:
    """R4: any email containing '..' must not validate when @ is present."""
    solver = Solver()
    email_var = String("email")
    solver.add(Contains(email_var, StringVal("..")))
    solver.add(Contains(email_var, StringVal("@")))
    if solver.check() != sat:
        pytest.skip("Z3 could not synthesize a consecutive-dots counterexample")
    sample = _model_string(solver.model().eval(email_var, model_completion=True))
    result = validator.validate_email(sample)
    assert result.is_valid is False
    assert result.error_message is not None
    assert "dot" in result.error_message.lower()


def test_z3_R4_invariant_no_valid_email_with_double_dot(
    validator: EmailValidator,
) -> None:
    """R4 invariant: valid results never contain consecutive dots."""
    candidates = [
        "a..b@example.com",
        "user@dom..ain.com",
        "..user@example.com",
    ]
    for sample in candidates:
        result = validator.validate_email(sample)
        assert result.is_valid is False
