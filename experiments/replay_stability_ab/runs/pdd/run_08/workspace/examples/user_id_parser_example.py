#!/usr/bin/env python3
"""Example usage of the parse_user_id function from user_id_parser.

This script demonstrates every supported input format and edge case
for parse_user_id, which extracts, normalizes, and validates user IDs.

Module location : src/user_id_parser.py  (relative to project root)
Example location: examples/user_id_parser_example.py

Function signature
------------------
parse_user_id(raw: object) -> str | None

Parameters
----------
raw : object
    The input to parse. Accepted formats:
      • str  – must follow the pattern "user:<id>"
               e.g. "user:alice_99"
      • dict – either flat  {"user_id": "<id>"}
               or nested    {"user": {"id": "<id>"}}
    Any other type (int, list, None, …) is gracefully rejected.

Returns
-------
str | None
    The normalized user ID (trimmed of surrounding whitespace, lowercased)
    if ALL of the following hold:
      • Contains only a-z, 0-9, underscore (_), or hyphen (-)
      • Length is between 3 and 20 characters inclusive
      • Is not a reserved ID ("admin", "root", "system")
    Otherwise returns None.
"""

import os
import sys

# ---------------------------------------------------------------------------
# Path setup – make the project root importable
# ---------------------------------------------------------------------------
_THIS_DIR: str = os.path.dirname(os.path.abspath(__file__))
_PROJECT_ROOT: str = os.path.dirname(_THIS_DIR)  # one level up from examples/
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)

from src.user_id_parser import parse_user_id


def main() -> None:
    """Run all parse_user_id examples and print the results."""

    # ------------------------------------------------------------------
    # 1. String input  –  "user:<id>" format
    # ------------------------------------------------------------------
    print("=== String inputs (\"user:<id>\" format) ===")

    result = parse_user_id("user:alice_99")
    print(f"  'user:alice_99'          -> {result!r}")   # 'alice_99'

    # Leading/trailing whitespace in the ID is trimmed, then lowercased
    result = parse_user_id("user:  Bob-Smith  ")
    print(f"  'user:  Bob-Smith  '     -> {result!r}")   # 'bob-smith'

    # Missing "user:" prefix → None
    result = parse_user_id("alice_99")
    print(f"  'alice_99' (no prefix)   -> {result!r}")   # None

    # Too short (< 3 chars after normalization)
    result = parse_user_id("user:ab")
    print(f"  'user:ab' (too short)    -> {result!r}")   # None

    # Too long (> 20 chars)
    long_id: str = "a" * 21
    result = parse_user_id("user:" + long_id)
    print(f"  'user:{long_id}' (too long) -> {result!r}")  # None

    # Invalid characters
    result = parse_user_id("user:no spaces!")
    print(f"  'user:no spaces!'        -> {result!r}")   # None

    print()

    # ------------------------------------------------------------------
    # 2. Dict input  –  flat form {"user_id": "<id>"}
    # ------------------------------------------------------------------
    print('=== Dict inputs (flat form {"user_id": "<id>"}) ===')

    result = parse_user_id({"user_id": "charlie-7"})
    print(f"  {{\"user_id\": \"charlie-7\"}}       -> {result!r}")  # 'charlie-7'

    result = parse_user_id({"user_id": "  Delta  "})
    print(f"  {{\"user_id\": \"  Delta  \"}}       -> {result!r}")  # 'delta'

    print()

    # ------------------------------------------------------------------
    # 3. Dict input  –  nested form {"user": {"id": "<id>"}}
    # ------------------------------------------------------------------
    print('=== Dict inputs (nested form {"user": {"id": "<id>"}}) ===')

    result = parse_user_id({"user": {"id": "eve_2024"}})
    print(f"  {{\"user\": {{\"id\": \"eve_2024\"}}}}  -> {result!r}")  # 'eve_2024'

    result = parse_user_id({"user": {"id": "  Frank  "}})
    print(f"  {{\"user\": {{\"id\": \"  Frank  \"}}}} -> {result!r}")  # 'frank'

    print()

    # ------------------------------------------------------------------
    # 4. Reserved IDs are rejected
    # ------------------------------------------------------------------
    print("=== Reserved IDs (always rejected) ===")
    for reserved in ["admin", "root", "system"]:
        result = parse_user_id(f"user:{reserved}")
        print(f"  'user:{reserved}' -> {result!r}")  # None for each

    # Case-insensitive: "Admin" normalizes to "admin" → still reserved
    result = parse_user_id("user:Admin")
    print(f"  'user:Admin'             -> {result!r}")  # None

    print()

    # ------------------------------------------------------------------
    # 5. Unsupported / malformed input types → None (never raises)
    # ------------------------------------------------------------------
    print("=== Unsupported or malformed inputs (all return None) ===")

    result = parse_user_id(None)
    print(f"  None                     -> {result!r}")

    result = parse_user_id(42)
    print(f"  42 (int)                 -> {result!r}")

    result = parse_user_id(["user:alice"])
    print(f"  ['user:alice'] (list)    -> {result!r}")

    result = parse_user_id({})
    print(f"  {{}} (empty dict)          -> {result!r}")

    result = parse_user_id({"user_id": 12345})
    print(f"  {{\"user_id\": 12345}}       -> {result!r}")  # non-string value

    print()
    print("Done – all examples executed successfully.")


if __name__ == "__main__":
    main()