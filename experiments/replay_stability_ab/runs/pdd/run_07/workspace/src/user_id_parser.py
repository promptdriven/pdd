"""Baseline user id parser used for replay-stability experiments."""

import re

_RESERVED = frozenset({"admin", "root", "system"})
_VALID_RE = re.compile(r"^[a-z0-9_-]{3,20}$")


def _validate(uid: str) -> str | None:
    """Trim, lowercase, and validate a candidate id string."""
    uid = uid.strip().lower()
    if not uid or not _VALID_RE.match(uid) or uid in _RESERVED:
        return None
    return uid


def _extract_from_str(raw: str) -> str | None:
    """Extract raw id from ``'user:<id>'`` format."""
    text = raw.strip()
    if ":" not in text:
        return None
    prefix, rest = text.split(":", 1)
    if prefix != "user":
        return None
    return rest.strip() or None


def _extract_from_dict(raw: dict) -> str | None:
    """Extract raw id from dict (two accepted shapes)."""
    if "user_id" in raw:
        val = raw["user_id"]
        if isinstance(val, str) and val.strip():
            return val.strip()
    if "user" in raw:
        user = raw["user"]
        if isinstance(user, dict) and "id" in user:
            val = user["id"]
            if isinstance(val, str) and val.strip():
                return val.strip()
    return None


def parse_user_id(raw: object) -> str | None:
    """Extract and validate a user id from *raw*.

    Accepts:
      - str: ``"user:<id>"``
      - dict: ``{"user_id": "<id>"}`` or ``{"user": {"id": "<id>"}}``

    IDs are trimmed, lowercased, and validated (a-z 0-9 _ -, 3-20 chars,
    not reserved). Returns None for anything invalid. Never raises.
    """
    try:
        if isinstance(raw, str):
            candidate = _extract_from_str(raw)
        elif isinstance(raw, dict):
            candidate = _extract_from_dict(raw)
        else:
            return None
        if candidate is None:
            return None
        return _validate(candidate)
    except Exception:
        return None
