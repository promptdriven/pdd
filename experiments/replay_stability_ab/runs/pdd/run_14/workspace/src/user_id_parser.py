"""Baseline user id parser used for replay-stability experiments."""

import collections
import re

ParseResult = collections.namedtuple("ParseResult", ["user_id", "source"])

_RESERVED = frozenset({"admin", "root", "system"})
_VALID_PATTERN = re.compile(r"^[a-z0-9_-]{3,20}$")


def _extract(raw: object) -> tuple[str, str] | None:
    """Return the (raw_id, source) from supported input shapes, or None."""
    if isinstance(raw, str):
        text = raw.strip()
        if ":" not in text:
            return None
        prefix, remainder = text.split(":", 1)
        if prefix == "user":
            return (remainder, "string")
        if prefix == "email":
            if "@" not in remainder:
                return None
            username, _ = remainder.split("@", 1)
            if not username:
                return None
            return (username, "email")
        return None

    if isinstance(raw, dict):
        try:
            if "user_id" in raw:
                val = raw["user_id"]
                if isinstance(val, str):
                    return (val, "dict_flat")
            if "user" in raw:
                nested = raw["user"]
                if isinstance(nested, dict) and "id" in nested:
                    val = nested["id"]
                    if isinstance(val, str):
                        return (val, "dict_nested")
        except Exception:
            return None

    return None


def parse_user_id(raw, reserved_ids=None, strict=False) -> ParseResult | None:
    """Extract, normalise, and validate a user id from various input shapes."""
    try:
        result = _extract(raw)
        if result is None:
            return None

        raw_id, source = result
        cleaned = raw_id.strip().lower()

        if not _VALID_PATTERN.match(cleaned):
            return None

        blocked = _RESERVED if reserved_ids is None else reserved_ids
        if cleaned in blocked:
            return None

        if strict and re.search(r"[_-]{2}", cleaned):
            return None

        return ParseResult(user_id=cleaned, source=source)
    except Exception:
        return None


def parse_user_ids(items: list, reserved_ids=None, strict=False) -> list[ParseResult | None]:
    """Batch-process multiple items through parse_user_id."""
    return [parse_user_id(item, reserved_ids=reserved_ids, strict=strict) for item in items]
