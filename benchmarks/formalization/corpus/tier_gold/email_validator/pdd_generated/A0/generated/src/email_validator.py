"""Bootstrap A0 generate output (replace via record_pdd_fixtures.py)."""
from __future__ import annotations


def validate_email(email: str) -> bool:
    """Naive A0-style validator — intentionally weaker than A1."""
    if email is None:
        raise TypeError("email cannot be None")
    return "@" in str(email).strip()
