"""Reference implementation for M2 harness (bool API per A0)."""
from __future__ import annotations


def validate_email(email: str) -> bool:
    if email is None:
        raise TypeError("email cannot be None")
    normalized = email.strip().lower()
    if not normalized or ".." in normalized or normalized.count("@") != 1:
        return False
    local, domain = normalized.split("@", 1)
    if not local or "." not in domain:
        return False
    return True
