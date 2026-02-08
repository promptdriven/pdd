#!/usr/bin/env python3
"""Example usage of the user_id_parser module.

This script demonstrates how to call ``parse_user_id`` with various inputs
and interpret its return values.  The module file lives at
``src/user_id_parser.py`` (relative to the workspace root).
"""

import os
import sys

# ---------------------------------------------------------------------------
# Path setup – make the workspace ``src/`` directory importable so we can
# reach ``user_id_parser`` regardless of where this script is executed from.
# ---------------------------------------------------------------------------
_here = os.path.dirname(os.path.abspath(__file__))
_workspace = os.path.join(_here, "..")
src_path = os.path.join(_workspace, "src")
if src_path not in sys.path:
    sys.path.insert(0, src_path)

from user_id_parser import parse_user_id


def main() -> None:
    """Run a series of examples that exercise ``parse_user_id``."""

    # ------------------------------------------------------------------
    # 1. Valid string inputs
    # ------------------------------------------------------------------
    print("=== Valid string inputs ===")

    result = parse_user_id("user:abc123")
    print(f"parse_user_id('user:abc123')        -> {result!r}")  # 'abc123'

    result = parse_user_id("  user:abc123  ")
    print(f"parse_user_id('  user:abc123  ')    -> {result!r}")  # 'abc123'

    result = parse_user_id("user:  some_id  ")
    print(f"parse_user_id('user:  some_id  ')   -> {result!r}")  # 'some_id'

    result = parse_user_id("user:id-with-dashes")
    print(f"parse_user_id('user:id-with-dashes')-> {result!r}")  # 'id-with-dashes'

    result = parse_user_id("user:MiXeD_Case")
    print(f"parse_user_id('user:MiXeD_Case')   -> {result!r}")  # 'mixed_case' (lowercased)

    print()

    # ------------------------------------------------------------------
    # 2. Valid dict inputs
    # ------------------------------------------------------------------
    print("=== Valid dict inputs ===")

    result = parse_user_id({"user_id": "abc"})
    print(f"parse_user_id(dict user_id)         -> {result!r}")  # 'abc'

    result = parse_user_id({"user": {"id": "nested_id"}})
    print(f"parse_user_id(dict nested)          -> {result!r}")  # 'nested_id'

    result = parse_user_id({"user_id": "  Upper_Case  "})
    print(f"parse_user_id(dict trimmed+lower)   -> {result!r}")  # 'upper_case'

    print()

    # ------------------------------------------------------------------
    # 3. Invalid / rejected inputs
    # ------------------------------------------------------------------
    print("=== Invalid inputs (all return None) ===")

    result = parse_user_id("admin:abc123")
    print(f"parse_user_id('admin:abc123')       -> {result!r}")  # None

    result = parse_user_id("userabc123")
    print(f"parse_user_id('userabc123')         -> {result!r}")  # None

    result = parse_user_id("user:")
    print(f"parse_user_id('user:')              -> {result!r}")  # None

    result = parse_user_id("user:   ")
    print(f"parse_user_id('user:   ')           -> {result!r}")  # None

    result = parse_user_id("user:has:colons")
    print(f"parse_user_id('user:has:colons')    -> {result!r}")  # None (invalid chars)

    result = parse_user_id("user:admin")
    print(f"parse_user_id('user:admin')         -> {result!r}")  # None (reserved)

    result = parse_user_id("user:root")
    print(f"parse_user_id('user:root')          -> {result!r}")  # None (reserved)

    result = parse_user_id("user:system")
    print(f"parse_user_id('user:system')        -> {result!r}")  # None (reserved)

    result = parse_user_id("user:ab")
    print(f"parse_user_id('user:ab')            -> {result!r}")  # None (too short)

    result = parse_user_id(None)
    print(f"parse_user_id(None)                 -> {result!r}")  # None

    result = parse_user_id(12345)
    print(f"parse_user_id(12345)                -> {result!r}")  # None

    result = parse_user_id([])
    print(f"parse_user_id([])                   -> {result!r}")  # None

    print()

    # ------------------------------------------------------------------
    # 4. Practical pattern – safe use in a processing pipeline
    # ------------------------------------------------------------------
    print("=== Pipeline example ===")

    raw_inputs = [
        "user:alice",
        "user:bob_42",
        "  user:  charlie  ",
        {"user_id": "dict_user"},
        {"user": {"id": "nested_one"}},
        "service:internal",
        "",
        42,
        None,
    ]

    parsed = []
    for raw in raw_inputs:
        uid = parse_user_id(raw)
        if uid is not None:
            parsed.append(uid)
        else:
            print(f"  Skipped invalid input: {raw!r}")

    print(f"  Successfully parsed user ids: {parsed}")
    # Expected: ['alice', 'bob_42', 'charlie', 'dict_user', 'nested_one']

    # ------------------------------------------------------------------
    # 5. Write results to an output file for verification
    # ------------------------------------------------------------------
    os.makedirs("./output", exist_ok=True)
    output_path = os.path.join("./output", "parsed_user_ids.txt")
    with open(output_path, "w") as f:
        for uid in parsed:
            f.write(uid + "\n")
    print(f"\nParsed ids written to {output_path}")


if __name__ == "__main__":
    main()
