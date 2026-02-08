"""User id parser for replay-stability experiments."""

from __future__ import annotations

import re

_VALID_RE = re.compile(r"^[a-z0-9_-]{3,20}$")
_RESERVED = {"admin", "root", "system"}


def _normalize_candidate(value: object) -> str | None:
    if not isinstance(value, str):
        return None
    cleaned = value.strip().lower()
    if not cleaned:
        return None
    if cleaned in _RESERVED:
        return None
    if not _VALID_RE.fullmatch(cleaned):
        return None
    return cleaned


def parse_user_id(raw: object) -> str | None:
    """Parse a valid user id from supported payload shapes.

    Supported input:
    - "user:<id>"
    - {"user_id": "<id>"}
    - {"user": {"id": "<id>"}}
    """
    if isinstance(raw, str):
        text = raw.strip()
        if ":" not in text:
            return None
        prefix, candidate = text.split(":", 1)
        if prefix != "user":
            return None
        return _normalize_candidate(candidate)

    if isinstance(raw, dict):
        if "user_id" in raw:
            return _normalize_candidate(raw.get("user_id"))

        user_obj = raw.get("user")
        if isinstance(user_obj, dict):
            return _normalize_candidate(user_obj.get("id"))

    return None
