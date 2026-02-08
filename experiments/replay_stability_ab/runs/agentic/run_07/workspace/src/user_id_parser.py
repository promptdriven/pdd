"""Robust user id parser used for replay-stability experiments."""

import re

_VALID_PATTERN = re.compile(r'^[a-z0-9_-]{3,20}$')
_RESERVED_IDS = frozenset({'admin', 'root', 'system'})


def _extract_id(raw: object) -> str | None:
    """Extract a raw ID string from the supported input formats."""
    if isinstance(raw, str):
        text = raw.strip()
        if ':' not in text:
            return None
        prefix, user_id = text.split(':', 1)
        if prefix != 'user':
            return None
        return user_id.strip()

    if isinstance(raw, dict):
        # Flat form: {"user_id": "<id>"}
        if 'user_id' in raw:
            val = raw['user_id']
            if isinstance(val, str):
                return val.strip()

        # Nested form: {"user": {"id": "<id>"}}
        user_val = raw.get('user')
        if isinstance(user_val, dict):
            id_val = user_val.get('id')
            if isinstance(id_val, str):
                return id_val.strip()

    return None


def _validate_id(user_id: str) -> str | None:
    """Normalize and validate an extracted ID. Returns normalized ID or None."""
    normalized = user_id.lower()
    if not _VALID_PATTERN.match(normalized):
        return None
    if normalized in _RESERVED_IDS:
        return None
    return normalized


def parse_user_id(raw: object) -> str | None:
    """Extract, normalize, and validate a user id from various input formats.

    Accepts:
      - String: "user:<id>"
      - Dict: {"user_id": "<id>"} or {"user": {"id": "<id>"}}

    Returns the normalized (trimmed, lowercased) ID if valid, else None.
    Never raises for expected bad input types or malformed payloads.
    Does not mutate input dictionaries.
    """
    extracted = _extract_id(raw)
    if not extracted:
        return None
    return _validate_id(extracted)
