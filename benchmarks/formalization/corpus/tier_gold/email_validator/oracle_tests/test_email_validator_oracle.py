"""Oracle tests for email_validator (not generated from the benchmark prompt)."""
from __future__ import annotations

import pytest

from email_validator import validate_email


def test_valid_address() -> None:
    assert validate_email("user@example.com") is True


def test_rejects_empty() -> None:
    assert validate_email("") is False
    assert validate_email("   ") is False


def test_rejects_missing_at() -> None:
    assert validate_email("userexample.com") is False


def test_rejects_double_at() -> None:
    assert validate_email("a@@b.com") is False


def test_rejects_no_domain_dot() -> None:
    assert validate_email("user@localhost") is False


def test_none_raises() -> None:
    with pytest.raises(TypeError):
        validate_email(None)  # type: ignore[arg-type]
