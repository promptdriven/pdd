"""Baseline user id parser used for replay-stability experiments."""

import collections
import re

ParseResult = collections.namedtuple("ParseResult", ["user_id", "source"])

_RESERVED = {"admin", "root", "system"}
_VALID_PATTERN = re.compile(r"^[a-z0-9_-]{3,20}$")


def parse_user_id(raw: object, reserved_ids=None) -> ParseResult | None:
    """Extract and validate a user id from string or dict input."""
    if reserved_ids is None:
        reserved_ids = _RESERVED
    extracted = _extract(raw)
    if extracted is None:
        return None
    value, source = extracted
    normalized = value.strip().lower()
    if not _VALID_PATTERN.match(normalized):
        return None
    if normalized in reserved_ids:
        return None
    return ParseResult(user_id=normalized, source=source)


def parse_user_ids(items: list, reserved_ids=None) -> list[ParseResult | None]:
    """Process a batch of items through parse_user_id, preserving order."""
    return [parse_user_id(item, reserved_ids=reserved_ids) for item in items]


def _extract(raw: object) -> tuple[str, str] | None:
    """Pull the raw id string and source out of the supported input shapes."""
    if isinstance(raw, str):
        if ":" not in raw:
            return None
        prefix, _, value = raw.partition(":")
        if prefix == "user":
            return (value, "string")
        if prefix == "email":
            stripped = value.strip()
            if "@" not in stripped:
                return None
            return (stripped.split("@", 1)[0], "email")
        return None

    if isinstance(raw, dict):
        if "user_id" in raw:
            v = raw["user_id"]
            return (v, "dict_flat") if isinstance(v, str) else None
        user = raw.get("user")
        if isinstance(user, dict):
            v = user.get("id")
            return (v, "dict_nested") if isinstance(v, str) else None

    return None
