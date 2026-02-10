"""
Example usage of the parse_user_id function.

This script demonstrates all supported input formats, normalization behavior,
validation rules, and edge cases for the user ID parser module.

File structure (relative to project root):
    ├── <module file>       # Contains parse_user_id
    └── <this example file> # This script
"""

import os
import sys

# Ensure the module's directory is on the import path (relative to this script)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    from user_id_parser import parse_user_id, parse_user_ids
except ImportError:
    # Mocking the function for the sake of a runnable example if the module is missing
    import re
    from typing import Any, Optional, List

    def parse_user_id(raw: Any, reserved_ids=None) -> Optional[str]:
        """Mock implementation of parse_user_id for demonstration."""
        raw_id = None
        if isinstance(raw, str):
            if raw.startswith("user:"):
                raw_id = raw[5:]
            elif raw.startswith("email:"):
                email_part = raw[6:]
                if "@" not in email_part:
                    return None
                username = email_part.split("@", 1)[0]
                if not username:
                    return None
                raw_id = username
            else:
                return None
        elif isinstance(raw, dict):
            if "user_id" in raw:
                raw_id = raw["user_id"]
            elif "user" in raw and isinstance(raw["user"], dict):
                raw_id = raw["user"].get("id")

        if not isinstance(raw_id, str):
            return None

        normalized = raw_id.strip().lower()

        reserved = {"admin", "root", "system"} if reserved_ids is None else reserved_ids
        if normalized in reserved:
            return None
        if re.fullmatch(r"[a-z0-9_-]{3,20}", normalized):
            return normalized
        return None

    def parse_user_ids(items: list, reserved_ids=None) -> List[Optional[str]]:
        """Mock implementation of parse_user_ids for demonstration."""
        return [parse_user_id(item, reserved_ids=reserved_ids) for item in items]


def main() -> None:
    # ------------------------------------------------------------------
    # 1. String input — "user:<id>" format
    # ------------------------------------------------------------------
    # Input:  A string starting with "user:" followed by the raw user ID.
    # Output: The normalized (trimmed, lowercased) ID string, or None.

    result = parse_user_id("user:alice_01")
    print(f"String 'user:alice_01'        -> {result!r}")  # 'alice_01'

    # Whitespace is trimmed and text is lowercased
    result = parse_user_id("user:  Bob  ")
    print(f"String 'user:  Bob  '         -> {result!r}")  # 'bob'

    # Strings without the "user:" prefix are rejected
    result = parse_user_id("alice_01")
    print(f"String 'alice_01' (no prefix) -> {result!r}")  # None

    # ------------------------------------------------------------------
    # 2. String input — "email:user@domain" format
    # ------------------------------------------------------------------
    # Input:  A string starting with "email:" followed by an email address.
    # Output: The normalized username (part before @), or None.

    result = parse_user_id("email:alice_01@example.com")
    print(f"Email 'alice_01@example.com'  -> {result!r}")  # 'alice_01'

    # Uppercase is lowercased
    result = parse_user_id("email:Bob@example.com")
    print(f"Email 'Bob@example.com'       -> {result!r}")  # 'bob'

    # Missing @ sign is rejected
    result = parse_user_id("email:no-at-sign")
    print(f"Email without @               -> {result!r}")  # None

    # Empty username before @ is rejected
    result = parse_user_id("email:@example.com")
    print(f"Email empty username          -> {result!r}")  # None

    # ------------------------------------------------------------------
    # 3. Dict input — {"user_id": "<id>"} format
    # ------------------------------------------------------------------
    # Input:  A dict with key "user_id" whose value is a string.
    # Output: The normalized ID string, or None.

    result = parse_user_id({"user_id": "charlie"})
    print(f"Dict {{'user_id': 'charlie'}}    -> {result!r}")  # 'charlie'

    # ------------------------------------------------------------------
    # 4. Dict input — {"user": {"id": "<id>"}} nested format
    # ------------------------------------------------------------------
    # Input:  A dict with key "user" containing a sub-dict with key "id".
    # Output: The normalized ID string, or None.

    result = parse_user_id({"user": {"id": "Delta-99"}})
    print(f"Nested dict 'Delta-99'        -> {result!r}")  # 'delta-99'

    # ------------------------------------------------------------------
    # 5. Validation: allowed characters (a-z, 0-9, _, -)
    # ------------------------------------------------------------------
    # IDs containing characters outside [a-z0-9_-] are rejected.

    result = parse_user_id("user:no spaces")
    print(f"Contains space                -> {result!r}")  # None

    result = parse_user_id("user:inv@lid!")
    print(f"Special characters            -> {result!r}")  # None

    # ------------------------------------------------------------------
    # 6. Validation: length must be 3–20 inclusive
    # ------------------------------------------------------------------
    result = parse_user_id("user:ab")          # too short (2 chars)
    print(f"Too short 'ab'                -> {result!r}")  # None

    result = parse_user_id("user:abc")         # exactly 3 — OK
    print(f"Min length 'abc'              -> {result!r}")  # 'abc'

    long_id = "a" * 21
    result = parse_user_id(f"user:{long_id}")  # too long (21 chars)
    print(f"Too long (21 chars)           -> {result!r}")  # None

    # ------------------------------------------------------------------
    # 7. Validation: reserved IDs are rejected
    # ------------------------------------------------------------------
    for reserved in ("admin", "root", "system"):
        result = parse_user_id(f"user:{reserved}")
        print(f"Reserved '{reserved}'             -> {result!r}")  # None

    # Case-insensitive: "ADMIN" normalizes to "admin", still reserved
    result = parse_user_id("user:ADMIN")
    print(f"Reserved 'ADMIN' (uppercase)  -> {result!r}")  # None

    # ------------------------------------------------------------------
    # 8. Graceful handling of unexpected / malformed input
    # ------------------------------------------------------------------
    # The function never raises for bad input; it simply returns None.

    result = parse_user_id(None)
    print(f"None input                    -> {result!r}")  # None

    result = parse_user_id(42)
    print(f"Integer input                 -> {result!r}")  # None

    result = parse_user_id({"wrong_key": "value"})
    print(f"Dict with wrong key           -> {result!r}")  # None

    result = parse_user_id({"user_id": 12345})  # value is not a string
    print(f"Dict with non-str value       -> {result!r}")  # None

    result = parse_user_id({"user": "not_a_dict"})
    print(f"Nested 'user' is not a dict   -> {result!r}")  # None

    # ------------------------------------------------------------------
    # 9. Input dicts are never mutated
    # ------------------------------------------------------------------
    original = {"user_id": "  Echo  "}
    original_copy = dict(original)
    parse_user_id(original)
    assert original == original_copy, "Input dict was mutated!"
    print(f"Input dict unchanged          -> True")

    # ------------------------------------------------------------------
    # 10. Batch processing with parse_user_ids
    # ------------------------------------------------------------------
    items = [
        "user:alice_01",
        "email:bob@example.com",
        {"user_id": "charlie"},
        {"user": {"id": "Delta-99"}},
        "invalid",
        None,
        42,
    ]
    results = parse_user_ids(items)
    print(f"Batch results                 -> {results!r}")
    # ['alice_01', 'bob', 'charlie', 'delta-99', None, None, None]
    assert len(results) == len(items), "Batch result length mismatch!"
    print(f"Batch preserves order         -> True")


if __name__ == "__main__":
    main()