"""Tests for email_validator benchmark (A1 coverage + A2 baseline)."""
from __future__ import annotations

import pytest

from email_validator import EmailValidator, ValidationResult


@pytest.fixture
def validator() -> EmailValidator:
    return EmailValidator()


def test_R1_single_at_sign(validator: EmailValidator) -> None:
    result = validator.validate_email("user@example.com")
    assert result.is_valid is True
    assert validator.validate_email("a@@b.com").is_valid is False


def test_R2_local_part_nonempty(validator: EmailValidator) -> None:
    result = validator.validate_email("@example.com")
    assert result.is_valid is False
    assert "local" in (result.error_message or "").lower()


def test_R3_domain_contains_dot(validator: EmailValidator) -> None:
    result = validator.validate_email("user@localhost")
    assert result.is_valid is False


def test_R4_no_consecutive_dots(validator: EmailValidator) -> None:
    result = validator.validate_email("a..b@example.com")
    assert result.is_valid is False


def test_R5_none_raises_type_error(validator: EmailValidator) -> None:
    with pytest.raises(TypeError, match="email cannot be None"):
        validator.validate_email(None)  # type: ignore[arg-type]


def test_R6_empty_after_normalize(validator: EmailValidator) -> None:
    result = validator.validate_email("   ")
    assert result.is_valid is False
    assert result.error_message == "Email cannot be empty"


def test_valid_unicode_local(validator: EmailValidator) -> None:
    result = validator.validate_email("üser@example.com")
    assert isinstance(result, ValidationResult)
    assert result.is_valid is True
