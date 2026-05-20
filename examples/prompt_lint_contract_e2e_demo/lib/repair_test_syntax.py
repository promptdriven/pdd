#!/usr/bin/env python3
"""Repair LLM-generated pytest files (orphan sys.path if, import order)."""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(_REPO))

from pdd.generate_test import finalize_python_test_content  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("test_file", type=Path, help="Path to tests/test_foo_work_*.py")
    args = parser.parse_args()
    path = args.test_file
    if not path.is_file():
        print(f"ERROR: not found: {path}", file=sys.stderr)
        return 1
    raw = path.read_text(encoding="utf-8")
    try:
        fixed = finalize_python_test_content(raw)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    path.write_text(fixed, encoding="utf-8")
    compile(fixed, str(path), "exec")
    print(f"OK: repaired {path} ({len(fixed)} bytes, syntax valid)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
