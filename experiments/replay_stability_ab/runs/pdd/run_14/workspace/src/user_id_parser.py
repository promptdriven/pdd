"""Baseline user id parser used for replay-stability experiments."""

import re

_RESERVED = frozenset({"admin", "root", "system"})
_VALID_PATTERN = re.compile(r"^[a-z0-9_-]{3,20}$")


def _extract(raw: object) -> str | None:
    """Return the raw id string from supported input shapes, or None."""
    if isinstance(raw, str):
        text = raw.strip()
        if ":" not in text:
            return None
        prefix, user_id = text.split(":", 1)
        if prefix != "user":
            return None
        return user_id

    if isinstance(raw, dict):
        try:
            if "user_id" in raw:
                val = raw["user_id"]
                if isinstance(val, str):
                    return val
            if "user" in raw:
                nested = raw["user"]
                if isinstance(nested, dict) and "id" in nested:
                    val = nested["id"]
                    if isinstance(val, str):
                        return val
        except Exception:
            return None

    return None


def parse_user_id(raw: object) -> str | None:
    """Extract, normalise, and validate a user id from various input shapes."""
    try:
        raw_id = _extract(raw)
        if raw_id is None:
            return None

        cleaned = raw_id.strip().lower()

        if not _VALID_PATTERN.match(cleaned):
            return None

        if cleaned in _RESERVED:
            return None

        return cleaned
    except Exception:
        return None
