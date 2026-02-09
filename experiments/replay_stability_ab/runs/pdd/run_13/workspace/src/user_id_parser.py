from typing import Any, Optional, List, Set, Tuple

import collections
import re

ParseResult = collections.namedtuple("ParseResult", ["user_id", "source"])

_DEFAULT_RESERVED: Set[str] = {"admin", "root", "system"}
_VALID_PATTERN: re.Pattern[str] = re.compile(r'^[a-z0-9_-]{3,20}$')


def parse_user_id(raw: Any, reserved_ids: Optional[Set[str]] = None, strict: bool = False) -> Optional[ParseResult]:
    """Parse and validate a user ID from various input formats.

    Accepts:
      - "user:<id>"          -> source = "string"
      - "email:<local>@<dom>" -> source = "email"
      - {"user_id": "<id>"}  -> source = "dict_flat"
      - {"user": {"id": "<id>"}} -> source = "dict_nested"

    Returns a ParseResult(user_id, source), or None if invalid.
    """
    reserved = _DEFAULT_RESERVED if reserved_ids is None else reserved_ids
    result = _extract(raw)

    if result is None:
        return None

    extracted, source = result

    # Normalize: strip whitespace, lowercase
    normalized = extracted.strip().lower()

    # Validate format and length
    if not _VALID_PATTERN.match(normalized):
        return None

    # Check reserved
    if normalized in reserved:
        return None

    # Strict mode: reject consecutive special characters
    if strict and any(pair in normalized for pair in ("__", "--", "_-", "-_")):
        return None

    return ParseResult(user_id=normalized, source=source)


def parse_user_ids(items: List[Any], reserved_ids: Optional[Set[str]] = None, strict: bool = False) -> List[Optional[ParseResult]]:
    """Batch-process a list of items through parse_user_id.

    Returns a list of the same length where result[i] corresponds to items[i].
    Invalid items produce None in that position.
    """
    return [parse_user_id(item, reserved_ids=reserved_ids, strict=strict) for item in items]


def _extract(raw: Any) -> Optional[Tuple[str, str]]:
    """Extract the raw ID string and source label from the supported input formats."""
    if isinstance(raw, str):
        if raw.startswith("user:"):
            return (raw[5:], "string")
        if raw.startswith("email:"):
            rest = raw[6:]
            at_idx = rest.find("@")
            if at_idx == -1:
                return None
            return (rest[:at_idx], "email")
        return None

    if isinstance(raw, dict):
        # Try {"user_id": "<id>"} first
        if "user_id" in raw:
            val = raw["user_id"]
            return (val, "dict_flat") if isinstance(val, str) else None

        # Try {"user": {"id": "<id>"}}
        user = raw.get("user")
        if isinstance(user, dict):
            val = user.get("id")
            return (val, "dict_nested") if isinstance(val, str) else None

        return None

    return None