"""Robust user id parser used for replay-stability experiments."""

import re

_ID_RE = re.compile(r'^[a-z0-9_-]{3,20}$')
_RESERVED = {'admin', 'root', 'system'}


def parse_user_id(raw: object) -> str | None:
    """Extract and validate a user id from various input formats.

    Supported inputs:
      - str:  "user:<id>"
      - dict: {"user_id": "<id>"} or {"user": {"id": "<id>"}}

    Returns normalized (stripped, lowered) id if valid, otherwise None.
    Never raises on bad input. Does not mutate input dicts.
    """
    candidate = _extract(raw)
    if candidate is None:
        return None

    normalized = candidate.strip().lower()
    if not normalized:
        return None
    if not _ID_RE.match(normalized):
        return None
    if normalized in _RESERVED:
        return None

    return normalized


def _extract(raw: object) -> str | None:
    """Pull a candidate id string from the raw input."""
    if isinstance(raw, str):
        text = raw.strip()
        if ':' not in text:
            return None
        prefix, _, value = text.partition(':')
        if prefix != 'user':
            return None
        return value

    if isinstance(raw, dict):
        # Try flat form first
        uid = raw.get('user_id')
        if isinstance(uid, str):
            return uid

        # Try nested form
        user = raw.get('user')
        if isinstance(user, dict):
            nested_id = user.get('id')
            if isinstance(nested_id, str):
                return nested_id

    return None
