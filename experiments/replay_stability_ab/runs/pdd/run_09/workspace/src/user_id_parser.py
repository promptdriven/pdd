# src/user_id_parser.py

import re

_VALID_PATTERN = re.compile(r'^[a-z0-9_-]{3,20}$')
_RESERVED_IDS = frozenset({'admin', 'root', 'system'})


def _validate(user_id: str) -> str | None:
    """Normalize and validate an extracted user ID. Return it or None."""
    normalized = user_id.strip().lower()
    if not _VALID_PATTERN.fullmatch(normalized):
        return None
    if normalized in _RESERVED_IDS:
        return None
    return normalized


def _extract_from_string(raw: str) -> str | None:
    """Extract ID from 'user:<id>' format."""
    prefix = "user:"
    if not raw.startswith(prefix):
        return None
    return raw[len(prefix):]


def _extract_from_dict(raw: dict) -> str | None:
    """Extract ID from {"user_id": "<id>"} or {"user": {"id": "<id>"}} format."""
    # Try flat form first
    if "user_id" in raw:
        val = raw["user_id"]
        if isinstance(val, str):
            return val

    # Try nested form
    if "user" in raw:
        user = raw["user"]
        if isinstance(user, dict) and "id" in user:
            val = user["id"]
            if isinstance(val, str):
                return val

    return None


def parse_user_id(raw: object) -> str | None:
    """
    Parse and validate a user ID from various input formats.

    Accepts:
      - str:  "user:<id>"
      - dict: {"user_id": "<id>"} or {"user": {"id": "<id>"}}

    Returns the normalized (trimmed, lowercased) ID if valid, otherwise None.
    """
    try:
        extracted: str | None = None

        if isinstance(raw, str):
            extracted = _extract_from_string(raw)
        elif isinstance(raw, dict):
            extracted = _extract_from_dict(raw)

        if extracted is None:
            return None

        return _validate(extracted)

    except Exception:
        return None