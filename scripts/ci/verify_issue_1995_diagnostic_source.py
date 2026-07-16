"""Fail closed unless an issue-1995 diagnostic head preserves its subject bytes."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def _git(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ("git", *arguments), text=True, capture_output=True, check=False
    )


def main() -> int:
    """Validate HEAD and its path-scoped byte differences."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--subject", required=True)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--allow", action="append", default=[])
    arguments = parser.parse_args()

    actual = _git("rev-parse", "HEAD")
    if actual.returncode != 0:
        print(actual.stderr.strip(), file=sys.stderr)
        return 2
    actual_head = actual.stdout.strip()
    if actual_head != arguments.expected_head:
        print(
            f"checked HEAD {actual_head} != expected {arguments.expected_head}",
            file=sys.stderr,
        )
        return 3
    subject = _git("cat-file", "-e", f"{arguments.subject}^{{commit}}")
    if subject.returncode != 0:
        print(f"missing intended subject {arguments.subject}", file=sys.stderr)
        return 4

    changed = _git(
        "diff", "--name-only", "--no-renames", arguments.subject, actual_head, "--"
    )
    if changed.returncode != 0:
        print(changed.stderr.strip(), file=sys.stderr)
        return 5
    changed_paths = {line for line in changed.stdout.splitlines() if line}
    allowed_paths = {str(Path(path)) for path in arguments.allow}
    unexpected = sorted(changed_paths - allowed_paths)
    if unexpected:
        print(
            "non-diagnostic paths differ from intended subject: "
            + ", ".join(unexpected),
            file=sys.stderr,
        )
        return 6

    print(
        json.dumps(
            {
                "schema_version": 1,
                "actual_head": actual_head,
                "expected_head": arguments.expected_head,
                "intended_subject": arguments.subject,
                "changed_diagnostic_paths": sorted(changed_paths),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
