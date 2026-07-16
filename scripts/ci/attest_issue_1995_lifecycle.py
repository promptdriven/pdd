"""Validate issue-1995 collection and skip parity without rerunning pytest."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    """Check collection and skip counts in one completed lifecycle log."""
    parser = argparse.ArgumentParser()
    parser.add_argument("lifecycle", type=Path)
    parser.add_argument("--expected-collected", type=int, required=True)
    parser.add_argument("--expected-skipped", type=int, required=True)
    arguments = parser.parse_args()
    try:
        records = [
            json.loads(line)
            for line in arguments.lifecycle.read_text(encoding="utf-8").splitlines()
        ]
    except (OSError, json.JSONDecodeError) as error:
        print(f"invalid lifecycle JSONL: {error}", file=sys.stderr)
        return 2
    collections = [
        record for record in records if record.get("event") == "collection.finish"
    ]
    if len(collections) != 1:
        print("expected one completed collection", file=sys.stderr)
        return 3
    collected = collections[0].get("item_count")
    skipped_nodes = {
        record.get("nodeid")
        for record in records
        if record.get("event") == "node.report" and record.get("outcome") == "skipped"
    }
    if collected != arguments.expected_collected:
        print(
            f"collected {collected}, expected {arguments.expected_collected}",
            file=sys.stderr,
        )
        return 4
    if len(skipped_nodes) != arguments.expected_skipped:
        print(
            f"skipped {len(skipped_nodes)}, expected {arguments.expected_skipped}",
            file=sys.stderr,
        )
        return 5
    print(
        json.dumps(
            {
                "schema_version": 1,
                "collected": collected,
                "skipped": len(skipped_nodes),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
