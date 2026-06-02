"""Tests from prompt (bootstrap fixture — replace via record_pdd_fixtures.py)."""
from __future__ import annotations

from email_validator import validate_email


def test_R1_valid_email() -> None:
    assert validate_email("user@example.com") is True


def test_R2_invalid_email() -> None:
    assert validate_email("not-an-email") is False


def test_R3_empty_rejected() -> None:
    assert validate_email("") is False
    assert validate_email("   ") is False
