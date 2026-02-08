"""Robust user id parser used for replay-stability experiments."""

import re

_ALLOWED = re.compile(r'^[a-z0-9_-]{3,20}$')
_RESERVED_IDS = frozenset(('admin', 'root', 'system'))


def parse_user_id(raw: object) -> str | None:
    """Parse, normalize, and validate a user id from multiple input shapes.

    Accepted formats:
        - "user:<id>"  (string)
        - {"user_id": "<id>"}  (dict, flat)
        - {"user": {"id": "<id>"}}  (dict, nested)

    Returns lowercase validated id or None. Never raises.
    Input dicts are not mutated.
    """
    raw_id = _get_raw_id(raw)
    if raw_id is None:
        return None
    cleaned = raw_id.strip().lower()
    if not _ALLOWED.match(cleaned):
        return None
    if cleaned in _RESERVED_IDS:
        return None
    return cleaned


def _get_raw_id(raw: object) -> str | None:
    if isinstance(raw, str):
        s = raw.strip()
        if ':' not in s:
            return None
        prefix, rest = s.split(':', 1)
        return rest if prefix == 'user' else None

    if isinstance(raw, dict):
        v = raw.get('user_id')
        if isinstance(v, str):
            return v
        u = raw.get('user')
        if isinstance(u, dict):
            i = u.get('id')
            if isinstance(i, str):
                return i

    return None
