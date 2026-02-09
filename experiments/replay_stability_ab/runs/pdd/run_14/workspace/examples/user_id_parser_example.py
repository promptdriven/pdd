#!/usr/bin/env python3
"""Example usage of the user_id_parser module.

This script demonstrates how to parse, normalise, and validate user IDs from
various input shapes using parse_user_id and parse_user_ids.

Module location : src/user_id_parser.py  (relative to project root)
Example location: examples/user_id_parser_example.py (relative to project root)

Key concepts
------------
* **parse_user_id(raw, reserved_ids=None, strict=False) -> ParseResult | None**
    - raw : object
        Accepted shapes:
          - str  "user:<id>"           – extracts <id>
          - str  "email:<local>@<dom>"  – extracts <local> part
          - dict {"user_id": "<id>"}    – extracts <id>
          - dict {"user": {"id": "<id>"}} – extracts nested <id>
    - reserved_ids : set | frozenset | None
        IDs to reject.  Defaults to {"admin", "root", "system"}.
    - strict : bool
        When True, rejects IDs containing consecutive underscores or hyphens
        (e.g. "foo__bar" or "a--b").
    - Returns: ParseResult(user_id=str, source=str) on success, or None on
      failure.  ``user_id`` is the cleaned, lowercased identifier; ``source``
      is one of "string", "email", "dict_flat", or "dict_nested".

* **parse_user_ids(items, reserved_ids=None, strict=False) -> list[ParseResult | None]**
    - items : list
        A list of raw inputs (any mix of the shapes above).
    - Returns: A list of ParseResult | None, one per input item.
"""

import os
import sys

# ---------------------------------------------------------------------------
# Path setup – ensure the project root (workspace) is on sys.path so that
# "from src.user_id_parser import ..." resolves correctly.
# ---------------------------------------------------------------------------
_workspace = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, _workspace)

from src.user_id_parser import parse_user_id, parse_user_ids, ParseResult

# ---------------------------------------------------------------------------
# 1. Parsing from a "user:<id>" string
# ---------------------------------------------------------------------------
print("=== 1. String input (user:<id>) ===")
result = parse_user_id("user:alice_01")
# Expected: ParseResult(user_id='alice_01', source='string')
print(f"  Input : 'user:alice_01'")
print(f"  Output: {result}")
print(f"  user_id={result.user_id}, source={result.source}")
print()

# ---------------------------------------------------------------------------
# 2. Parsing from an "email:<local>@<domain>" string
# ---------------------------------------------------------------------------
print("=== 2. String input (email:<local>@<domain>) ===")
result_email = parse_user_id("email:Bob_Smith@example.com")
# The local part "Bob_Smith" is lowercased to "bob_smith"
print(f"  Input : 'email:Bob_Smith@example.com'")
print(f"  Output: {result_email}")
print()

# ---------------------------------------------------------------------------
# 3. Parsing from a flat dict  {"user_id": "<id>"}
# ---------------------------------------------------------------------------
print("=== 3. Dict input (flat) ===")
flat_dict = {"user_id": "  Charlie123  "}
result_flat = parse_user_id(flat_dict)
# Whitespace is trimmed and lowercased -> "charlie123"
print(f"  Input : {flat_dict}")
print(f"  Output: {result_flat}")
print()

# ---------------------------------------------------------------------------
# 4. Parsing from a nested dict  {"user": {"id": "<id>"}}
# ---------------------------------------------------------------------------
print("=== 4. Dict input (nested) ===")
nested_dict = {"user": {"id": "delta-99"}}
result_nested = parse_user_id(nested_dict)
print(f"  Input : {nested_dict}")
print(f"  Output: {result_nested}")
print()

# ---------------------------------------------------------------------------
# 5. Validation failures – all return None
# ---------------------------------------------------------------------------
print("=== 5. Invalid / rejected inputs (all return None) ===")

invalid_cases = [
    ("user:ab",                 "too short (min length 3)"),
    ("user:AAAAAAAAAAAAAAAAAAAAAA", "too long (max length 20)"),
    ("user:has space",           "contains invalid character (space)"),
    ("user:admin",               "reserved id (admin)"),
    ("user:root",                "reserved id (root)"),
    ("no_prefix_here",           "missing 'user:' or 'email:' prefix"),
    (42,                         "unsupported type (int)"),
    ({"wrong_key": "value"},     "dict without recognised key"),
    ("email:@example.com",       "email with empty local part"),
]

for raw, reason in invalid_cases:
    res = parse_user_id(raw)
    print(f"  {str(raw):42s} -> {res}  ({reason})")
print()

# ---------------------------------------------------------------------------
# 6. Custom reserved IDs
# ---------------------------------------------------------------------------
print("=== 6. Custom reserved_ids ===")
# Override the default blocked set; now 'admin' is allowed but 'bot' is blocked.
custom_blocked = frozenset({"bot", "service"})

result_admin = parse_user_id("user:admin", reserved_ids=custom_blocked)
result_bot   = parse_user_id("user:bot",   reserved_ids=custom_blocked)
print(f"  'user:admin' with custom reserved -> {result_admin}")
print(f"  'user:bot'   with custom reserved -> {result_bot}")
print()

# ---------------------------------------------------------------------------
# 7. Strict mode – rejects consecutive underscores / hyphens
# ---------------------------------------------------------------------------
print("=== 7. Strict mode ===")
result_lax    = parse_user_id("user:foo__bar", strict=False)
result_strict = parse_user_id("user:foo__bar", strict=True)
print(f"  'user:foo__bar'  strict=False -> {result_lax}")
print(f"  'user:foo__bar'  strict=True  -> {result_strict}")
print()

# ---------------------------------------------------------------------------
# 8. Batch processing with parse_user_ids
# ---------------------------------------------------------------------------
print("=== 8. Batch processing (parse_user_ids) ===")
batch = [
    "user:alpha",
    {"user_id": "bravo"},
    {"user": {"id": "charlie"}},
    "email:delta@test.io",
    "bad input",
    42,
]
results = parse_user_ids(batch, strict=False)
for raw_item, res in zip(batch, results):
    print(f"  {str(raw_item):35s} -> {res}")
print()

# ---------------------------------------------------------------------------
# 9. Accessing ParseResult fields
# ---------------------------------------------------------------------------
print("=== 9. ParseResult is a namedtuple ===")
pr = parse_user_id("user:echo-007")
print(f"  type      : {type(pr).__name__}")
print(f"  user_id   : {pr.user_id}")
print(f"  source    : {pr.source}")
print(f"  as tuple  : {tuple(pr)}")
print(f"  as dict   : {pr._asdict()}")
print()

print("Done.")