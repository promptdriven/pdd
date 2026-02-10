import collections
import re
from typing import List, Optional, Set, Union, Any

ParseResult = collections.namedtuple("ParseResult", ["user_id", "source"])

_DEFAULT_RESERVED = {"admin", "root", "system"}
_VALID_PATTERN = re.compile(r'^[a-z0-9_-]{3,20}$')
_CONSECUTIVE_SPECIAL = re.compile(r'[_-]{2}')


def parse_user_id(
    raw: Any, 
    reserved_ids: Optional[Set[str]] = None, 
    strict: bool = False
) -> Optional[ParseResult]:
    """
    Parses a user ID from various input formats and validates it.
    
    Args:
        raw: The input data (string or dict).
        reserved_ids: A set of strings that are not allowed as user IDs.
        strict: If True, disallows consecutive underscores or hyphens.
        
    Returns:
        A ParseResult namedtuple if valid, otherwise None.
    """
    try:
        user_id = None
        source = None

        if isinstance(raw, str):
            if raw.startswith("user:"):
                user_id = raw[5:]
                source = "string"
            elif raw.startswith("email:"):
                email_part = raw[6:]
                if "@" in email_part:
                    user_id = email_part.split("@", 1)[0]
                    source = "email"
                else:
                    return None
            else:
                return None

        elif isinstance(raw, dict):
            if "user_id" in raw:
                user_id = raw["user_id"]
                source = "dict_flat"
            elif "user" in raw and isinstance(raw.get("user"), dict) and "id" in raw["user"]:
                user_id = raw["user"]["id"]
                source = "dict_nested"
            else:
                return None
        else:
            return None

        if not isinstance(user_id, str):
            return None

        user_id = user_id.strip().lower()

        if not _VALID_PATTERN.match(user_id):
            return None

        reserved = _DEFAULT_RESERVED if reserved_ids is None else reserved_ids
        if user_id in reserved:
            return None

        if strict and _CONSECUTIVE_SPECIAL.search(user_id):
            return None

        return ParseResult(user_id=user_id, source=source)

    except Exception:
        return None


def parse_user_ids(
    items: List[Any], 
    reserved_ids: Optional[Set[str]] = None, 
    strict: bool = False
) -> List[Optional[ParseResult]]:
    """
    Parses a list of user ID inputs.
    """
    return [parse_user_id(item, reserved_ids=reserved_ids, strict=strict) for item in items]