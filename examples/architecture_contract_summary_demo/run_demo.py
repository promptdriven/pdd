#!/usr/bin/env python3
"""Run architecture sync on the issue #830 demo project and print contract_summary."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from pdd.architecture_sync import (
    sync_all_prompts_to_architecture,
    validate_contract_summary,
)


def main() -> int:
    parser = argparse.ArgumentParser(description="Issue #830 contract_summary demo")
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Compute changes without writing architecture.json",
    )
    args = parser.parse_args()

    demo_dir = Path(__file__).resolve().parent
    prompts_dir = demo_dir / "prompts"
    arch_path = demo_dir / "architecture.json"

    result = sync_all_prompts_to_architecture(
        prompts_dir=prompts_dir,
        architecture_path=arch_path,
        dry_run=args.dry_run,
    )

    print(f"success={result['success']} updated_count={result['updated_count']}")
    for row in result.get("results", []):
        name = row.get("filename")
        summary = row.get("contract_summary")
        print(f"\n--- {name} ---")
        if summary is None:
            print("(no contract_summary)")
            continue
        print(json.dumps(summary, indent=2))
        errors = validate_contract_summary(summary)
        if errors:
            print("schema errors:", file=sys.stderr)
            for err in errors:
                print(f"  - {err}", file=sys.stderr)
            return 1
        print("schema: ok")

    if result.get("errors"):
        print("sync errors:", result["errors"], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
