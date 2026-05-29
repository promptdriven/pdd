"""Tests from A0 prompt (bootstrap fixture — replace via record_pdd_fixtures.py)."""
from __future__ import annotations

import pytest

from email_validator import validate_email


def test_accepts_simple_address() -> None:
    assert validate_email("a@b.co") is True


def test_rejects_no_at() -> None:
    assert validate_email("abc") is False


def test_none_raises() -> None:
    with pytest.raises(TypeError):
        validate_email(None)  # type: ignore[arg-type]
