"""Validate one issue-1995 run against its own durable node inventory."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path


def _load(path: Path) -> list[dict]:
    """Load complete JSONL records."""
    try:
        return [
            json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
        ]
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"invalid lifecycle JSONL: {error}") from error


def _validated_inventory(
    records: list[dict], allowed_paths: list[str]
) -> tuple[list[str], str, dict[str, int]]:
    """Return the authenticated collection identity."""
    inventories = [
        record for record in records if record.get("event") == "collection.inventory"
    ]
    if len(inventories) != 1:
        raise ValueError("expected one durable collection inventory")
    inventory = inventories[0]
    nodeids = inventory.get("nodeids")
    if (
        not isinstance(nodeids, list)
        or any(not isinstance(nodeid, str) for nodeid in nodeids)
        or nodeids != sorted(set(nodeids))
    ):
        raise ValueError("collection node IDs are not a unique sorted string list")
    encoded = ("\n".join(nodeids) + "\n").encode("utf-8")
    digest = hashlib.sha256(encoded).hexdigest()
    per_file = dict(
        sorted(Counter(nodeid.split("::", 1)[0] for nodeid in nodeids).items())
    )
    if (
        inventory.get("item_count") != len(nodeids)
        or inventory.get("nodeid_sha256") != digest
        or inventory.get("per_file") != per_file
    ):
        raise ValueError("collection inventory identity fields do not match node IDs")
    if set(per_file) != set(allowed_paths):
        raise ValueError(
            "collection contains paths outside the exact six-file selection"
        )
    return nodeids, digest, per_file


def _terminal_outcomes(records: list[dict], nodeids: list[str]) -> dict[str, str]:
    """Return one terminal result for every node reached by this run."""
    terminal: dict[str, str] = {}
    for record in records:
        if record.get("event") != "node.report":
            continue
        nodeid = record.get("nodeid")
        outcome = record.get("outcome")
        phase = record.get("phase")
        if not isinstance(nodeid, str) or not isinstance(outcome, str):
            continue
        if phase == "setup" and outcome in {"failed", "skipped"}:
            terminal[nodeid] = outcome
        elif phase == "call":
            terminal[nodeid] = outcome
        elif phase == "teardown":
            if outcome == "failed":
                terminal[nodeid] = outcome
            elif outcome == "skipped" and nodeid not in terminal:
                terminal[nodeid] = outcome
    unknown = sorted(set(terminal) - set(nodeids))
    if unknown:
        raise ValueError(f"terminal reports contain uncollected nodes: {unknown}")
    return terminal


def _finished_nodes(records: list[dict], nodeids: list[str]) -> set[str]:
    """Validate and return nodes whose setup/call/teardown lifecycle closed."""
    counts = Counter(
        record.get("nodeid")
        for record in records
        if record.get("event") == "node.finish"
    )
    if None in counts:
        raise ValueError("node finish record lacks a node ID")
    unknown = sorted(set(counts) - set(nodeids))
    if unknown:
        raise ValueError(f"finish records contain uncollected nodes: {unknown}")
    duplicates = sorted(nodeid for nodeid, count in counts.items() if count != 1)
    if duplicates:
        raise ValueError(f"nodes have duplicate finish records: {duplicates}")
    return set(counts)


def main() -> int:
    """Validate inventory identity, selected paths, and terminal coverage."""
    parser = argparse.ArgumentParser()
    parser.add_argument("lifecycle", type=Path)
    parser.add_argument("--allowed-path", action="append", required=True)
    arguments = parser.parse_args()
    try:
        records = _load(arguments.lifecycle)
        nodeids, digest, per_file = _validated_inventory(
            records, arguments.allowed_path
        )
        terminal = _terminal_outcomes(records, nodeids)
        finished = _finished_nodes(records, nodeids)
        session_finished = any(
            record.get("event") == "session.finish" for record in records
        )
        complete = (
            session_finished
            and finished == set(nodeids)
            and set(terminal) == set(nodeids)
        )
        if session_finished and not complete:
            raise ValueError("completed session lacks terminal coverage for every node")
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1
    print(
        json.dumps(
            {
                "schema_version": 1,
                "node_count": len(nodeids),
                "nodeid_sha256": digest,
                "per_file": per_file,
                "terminal_count": len(terminal),
                "node_finish_count": len(finished),
                "skipped": sum(outcome == "skipped" for outcome in terminal.values()),
                "outcome_counts": dict(sorted(Counter(terminal.values()).items())),
                "session_finished": session_finished,
                "complete": complete,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
