"""Example usage of the user_id_parser module.

This script demonstrates how to use parse_user_id() to extract, normalize,
and validate user IDs from various input formats.

File structure (relative to project root):
    src/user_id_parser.py   -- the module under use
    examples/               -- this example script lives here
"""

import os
import sys

# ---------------------------------------------------------------------------
# Path setup: ensure the workspace root is on sys.path so we can import
# from src.user_id_parser.
# ---------------------------------------------------------------------------
_this_dir = os.path.dirname(os.path.abspath(__file__))
_workspace_root = os.path.abspath(os.path.join(_this_dir, ".."))
if _workspace_root not in sys.path:
    sys.path.insert(0, _workspace_root)

from src.user_id_parser import parse_user_id

# ===================================================================
# 1. String input  --  format: "user:<id>"
# ===================================================================
# parse_user_id(raw: object) -> str | None
#
# Parameters
# ----------
# raw : object
#     Either a string in the form "user:<id>" or a dict (see below).
#     Any other type is gracefully ignored and returns None.
#
# Returns
# -------
# str | None
#     The normalized (trimmed, lowercased) user ID if it passes
#     validation, otherwise None.
#     Valid IDs contain only a-z, 0-9, underscore, or hyphen,
#     are 3-20 characters long, and are not one of the reserved
#     words: "admin", "root", "system".

print("=== String inputs (format 'user:<id>')")

result = parse_user_id("user:alice_01")
print(f"parse_user_id('user:alice_01')        -> {result!r}")  # 'alice_01'

# Whitespace around the ID is trimmed, and the ID is lowercased.
result = parse_user_id("user:  Bob  ")
print(f"parse_user_id('user:  Bob  ')         -> {result!r}")  # 'bob'

# A plain string without the "user:" prefix is rejected.
result = parse_user_id("alice_01")
print(f"parse_user_id('alice_01')             -> {result!r}")  # None

# ===================================================================
# 1b. String input  --  format: "email:user@domain"
# ===================================================================
print("\n=== String inputs (format 'email:user@domain') ===")

result = parse_user_id("email:frank_99@example.com")
print(f"parse_user_id('email:frank_99@example.com')  -> {result!r}")  # 'frank_99'

# Whitespace in the username part is trimmed and lowercased.
result = parse_user_id("email:  Grace  @example.com")
print(f"parse_user_id('email:  Grace  @example.com') -> {result!r}")  # 'grace'

# Missing '@' returns None.
result = parse_user_id("email:nodomain")
print(f"parse_user_id('email:nodomain')              -> {result!r}")  # None

# Empty username before '@' returns None.
result = parse_user_id("email:@example.com")
print(f"parse_user_id('email:@example.com')          -> {result!r}")  # None

# ===================================================================
# 2. Dict input  --  form A: {"user_id": "<id>"}
# ===================================================================
print("\n=== Dict inputs (form A: {'user_id': '<id>'}) ===")

result = parse_user_id({"user_id": "charlie"})
print(f"parse_user_id({{'user_id': 'charlie'}})           -> {result!r}")  # 'charlie'

result = parse_user_id({"user_id": "  Delta-99  "})
print(f"parse_user_id({{'user_id': '  Delta-99  '}})      -> {result!r}")  # 'delta-99'

# ===================================================================
# 3. Dict input  --  form B: {"user": {"id": "<id>"}}
# ===================================================================
print("\n=== Dict inputs (form B: {'user': {'id': '<id>'}}) ===")

result = parse_user_id({"user": {"id": "echo_42"}})
print(f"parse_user_id({{'user': {{'id': 'echo_42'}}}})    -> {result!r}")  # 'echo_42'

# ===================================================================
# 4. Validation failures  --  all return None
# ===================================================================
print("\n=== Validation failures (all return None) ===")

# Too short (< 3 characters after normalization).
result = parse_user_id("user:ab")
print(f"Too short       : parse_user_id('user:ab')              -> {result!r}")

# Too long (> 20 characters).
result = parse_user_id("user:" + "a" * 21)
print(f"Too long        : parse_user_id('user:{'a'*21}')  -> {result!r}")

# Invalid characters (spaces, dots, etc. in the ID body).
result = parse_user_id("user:bad.name!")
print(f"Bad chars       : parse_user_id('user:bad.name!')       -> {result!r}")

# Reserved IDs are rejected.
result = parse_user_id("user:admin")
print(f"Reserved 'admin': parse_user_id('user:admin')           -> {result!r}")

result = parse_user_id("user:ROOT")
print(f"Reserved 'root' : parse_user_id('user:ROOT')            -> {result!r}")

result = parse_user_id("user:System")
print(f"Reserved 'system': parse_user_id('user:System')         -> {result!r}")

# ===================================================================
# 5. Unsupported / malformed input  --  returns None, never raises
# ===================================================================
print("\n=== Unsupported / malformed input (all return None, no exceptions) ===")

result = parse_user_id(12345)
print(f"Integer input   : parse_user_id(12345)                  -> {result!r}")

result = parse_user_id(None)
print(f"None input      : parse_user_id(None)                   -> {result!r}")

result = parse_user_id({"unrelated_key": "value"})
print(f"Wrong dict key  : parse_user_id({{'unrelated_key': ..}}) -> {result!r}")

result = parse_user_id({"user_id": 999})
print(f"Non-str value   : parse_user_id({{'user_id': 999}})      -> {result!r}")

print("\nDone.")