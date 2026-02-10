"""
Example usage of the parse_user_id function.

This script demonstrates all supported input formats, normalization behavior,
validation rules, and edge cases for the user ID parser module.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from user_id_parser import parse_user_id


def main():
    # ──────────────────────────────────────────────
    # 1. String input — "user:<id>" format
    # ──────────────────────────────────────────────
    # Input:  A string starting with "user:" followed by the raw user ID.
    # Output: The normalized (trimmed, lowercased) ID string, or None if invalid.

    result = parse_user_id("user:alice_01")
    print(f"String 'user:alice_01'        -> {result}")  # "alice_01"

    # Whitespace is trimmed and text is lowercased
    result = parse_user_id("user:  Bob  ")
    print(f"String 'user:  Bob  '         -> {result}")  # "bob"

    # Strings without the "user:" prefix are rejected
    result = parse_user_id("alice_01")
    print(f"String 'alice_01' (no prefix) -> {result}")  # None

    # ──────────────────────────────────────────────
    # 2. Dict input — {"user_id": "<id>"} format
    # ──────────────────────────────────────────────
    # Input:  A dict with key "user_id" whose value is a string.
    # Output: Normalized ID or None.

    result = parse_user_id({"user_id": "charlie"})
    print(f"Dict {{'user_id': 'charlie'}}    -> {result}")  # "charlie"

    # ──────────────────────────────────────────────
    # 3. Dict input — {"user": {"id": "<id>"}} nested format
    # ──────────────────────────────────────────────
    # Input:  A dict with key "user" containing a nested dict with key "id".
    # Output: Normalized ID or None.

    result = parse_user_id({"user": {"id": "Dave-99"}})
    print(f"Dict nested 'Dave-99'         -> {result}")  # "dave-99"

    # ──────────────────────────────────────────────
    # 4. Validation: allowed characters (a-z, 0-9, _, -)
    # ──────────────────────────────────────────────
    # IDs containing characters outside the allowed set are rejected.

    result = parse_user_id("user:no spaces")
    print(f"Contains space                -> {result}")  # None

    result = parse_user_id("user:inv@lid!")
    print(f"Special characters            -> {result}")  # None

    # ──────────────────────────────────────────────
    # 5. Validation: length must be 3–20 inclusive
    # ──────────────────────────────────────────────

    result = parse_user_id("user:ab")
    print(f"Too short ('ab', len=2)       -> {result}")  # None

    result = parse_user_id("user:abc")
    print(f"Min length ('abc', len=3)     -> {result}")  # "abc"

    result = parse_user_id("user:" + "a" * 21)
    print(f"Too long (len=21)             -> {result}")  # None

    # ──────────────────────────────────────────────
    # 6. Validation: reserved IDs are rejected
    # ──────────────────────────────────────────────
    # "admin", "root", and "system" are reserved (checked after lowercasing).

    for reserved in ("admin", "Root", "SYSTEM"):
        result = parse_user_id(f"user:{reserved}")
        print(f"Reserved '{reserved}'             -> {result}")  # None

    # ──────────────────────────────────────────────
    # 7. Graceful handling of unexpected input types
    # ──────────────────────────────────────────────
    # The function never raises for bad input; it simply returns None.

    result = parse_user_id(12345)
    print(f"Integer input                 -> {result}")  # None

    result = parse_user_id(None)
    print(f"None input                    -> {result}")  # None

    result = parse_user_id(["user:alice"])
    print(f"List input                    -> {result}")  # None

    result = parse_user_id({"user_id": 999})
    print(f"Dict with non-string value    -> {result}")  # None

    result = parse_user_id({})
    print(f"Empty dict                    -> {result}")  # None

    # ──────────────────────────────────────────────
    # 8. Input dicts are never mutated
    # ──────────────────────────────────────────────
    payload = {"user_id": "safe_user"}
    parse_user_id(payload)
    print(f"Dict after call (unchanged)   -> {payload}")  # {"user_id": "safe_user"}


if __name__ == "__main__":
    main()