"""Example usage of the user_id_parser module.

This script demonstrates how to use `parse_user_id` to extract and validate
user IDs from various input formats.

File layout (relative to project root):
    src/user_id_parser.py   -- the module under use
    examples/               -- this example script lives here
"""

import os
import sys

# ---------------------------------------------------------------------------
# Path setup: ensure the project 'src' directory is importable
# ---------------------------------------------------------------------------
pdd_path = os.environ["PDD_PATH"]
sys.path.insert(0, os.path.join(pdd_path, "src"))

from user_id_parser import parse_user_id

# ===================================================================
# 1. String input  --  "user:<id>" format
# ===================================================================
# parse_user_id(raw: object) -> str | None
#
# Parameters
# ----------
# raw : object
#     The input to parse.  Accepted shapes:
#       • str  – must follow the pattern "user:<id>"
#       • dict – either {"user_id": "<id>"} or {"user": {"id": "<id>"}}
#     Any other type returns None.
#
# Returns
# -------
# str | None
#     The normalized user ID (stripped of whitespace, lowercased) if it
#     passes all validation rules, otherwise None.
#
# Validation rules applied to the extracted ID:
#   • Allowed characters: a-z, 0-9, underscore (_), hyphen (-)
#   • Length: 3 to 20 characters inclusive
#   • Must NOT be a reserved ID: "admin", "root", "system"

print("=== String inputs (\"user:<id>\") ===")

result = parse_user_id("user:alice_01")
print(f"  'user:alice_01'           -> {result!r}")   # 'alice_01'

# Whitespace around the ID is trimmed, and letters are lowercased.
result = parse_user_id("user:  Bob-42  ")
print(f"  'user:  Bob-42  '         -> {result!r}")   # 'bob-42'

# Too short (fewer than 3 characters after trimming)
result = parse_user_id("user:ab")
print(f"  'user:ab'                 -> {result!r}")   # None

# Missing the "user:" prefix
result = parse_user_id("alice_01")
print(f"  'alice_01' (no prefix)    -> {result!r}")   # None

# Reserved ID is rejected
result = parse_user_id("user:admin")
print(f"  'user:admin' (reserved)   -> {result!r}")   # None

print()

# ===================================================================
# 2. Dict input  --  flat form {"user_id": "<id>"}
# ===================================================================
print('=== Dict inputs (flat form) ===')

result = parse_user_id({"user_id": "charlie-x"})
print(f"  {{\"user_id\": \"charlie-x\"}}          -> {result!r}")  # 'charlie-x'

result = parse_user_id({"user_id": "!!invalid!!"})
print(f"  {{\"user_id\": \"!!invalid!!\"}}        -> {result!r}")  # None

print()

# ===================================================================
# 3. Dict input  --  nested form {"user": {"id": "<id>"}}
# ===================================================================
print('=== Dict inputs (nested form) ===')

result = parse_user_id({"user": {"id": "dave_99"}})
print(f"  {{\"user\": {{\"id\": \"dave_99\"}}}}       -> {result!r}")  # 'dave_99'

result = parse_user_id({"user": {"id": "root"}})
print(f"  {{\"user\": {{\"id\": \"root\"}}}} (reserved) -> {result!r}")  # None

print()

# ===================================================================
# 4. Unsupported / malformed inputs  --  always returns None safely
# ===================================================================
print('=== Unsupported / malformed inputs ===')

result = parse_user_id(12345)
print(f"  int 12345                 -> {result!r}")   # None

result = parse_user_id(None)
print(f"  None                      -> {result!r}")   # None

result = parse_user_id(["user:alice_01"])
print(f"  list                      -> {result!r}")   # None

result = parse_user_id({})
print(f"  empty dict                -> {result!r}")   # None

print()
print("All examples completed successfully.")