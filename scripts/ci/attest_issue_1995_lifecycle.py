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
    parser.add_argument("--expected-outcomes", type=int, required=True)
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
    terminal_outcomes: dict[str, str] = {}
    for record in records:
        if record.get("event") != "node.report":
            continue
        nodeid = record.get("nodeid")
        outcome = record.get("outcome")
        phase = record.get("phase")
        if not isinstance(nodeid, str) or not isinstance(outcome, str):
            continue
        if outcome == "skipped" or phase == "call":
            terminal_outcomes[nodeid] = outcome
    if len(terminal_outcomes) != arguments.expected_outcomes:
        print(
            f"outcomes {len(terminal_outcomes)}, expected {arguments.expected_outcomes}",
            file=sys.stderr,
        )
        return 4
    skipped = sum(outcome == "skipped" for outcome in terminal_outcomes.values())
    if skipped != arguments.expected_skipped:
        print(
            f"skipped {skipped}, expected {arguments.expected_skipped}",
            file=sys.stderr,
        )
        return 5
    print(
        json.dumps(
            {
                "schema_version": 1,
                "collection_size": collections[0].get("item_count"),
                "outcomes": len(terminal_outcomes),
                "skipped": skipped,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
