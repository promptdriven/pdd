"""Small direct CLI for standalone checker certification and release evidence."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Sequence

from .released_checker import (
    ReleasedCheckerError,
    _evidence_main,
    _validated_runtime_identity,
)
from .reporting import CanonicalReportOptions, build_canonical_report


class CheckerCliError(ValueError):
    """Raised when standalone checker command inputs are malformed."""


def _certify(arguments: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="pdd-sync-checker certify")
    parser.add_argument("--base-ref", default="HEAD")
    parser.add_argument("--head-ref", default="HEAD")
    parser.add_argument("--module", dest="modules", action="append", default=[])
    parser.add_argument("--replay-ledger", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(arguments)
    try:
        report = build_canonical_report(
            Path.cwd(),
            CanonicalReportOptions(
                base_ref=args.base_ref,
                head_ref=args.head_ref,
                modules=tuple(args.modules),
                replay_ledger_path=(
                    args.replay_ledger
                    or Path(os.environ.get(
                        "PDD_SYNC_TRUST_ROOT", Path.home() / ".pdd/trust/global-sync"
                    )) / "single.json"
                ),
            ),
        )
    except (OSError, RuntimeError, ValueError) as exc:
        report = {"schema_version": 1, "ok": False, "errors": [str(exc)]}
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0 if report.get("ok") is True else 1


def main(arguments: Sequence[str] | None = None) -> int:
    """Run only standalone checker commands after installed-wheel provenance passes."""
    values = tuple(sys.argv[1:] if arguments is None else arguments)
    try:
        _validated_runtime_identity()
        if values in (("--help",), ("-h",)):
            print("usage: pdd-sync-checker {certify,release-pin-evidence} ...")
            return 0
        if not values or values[0] == "certify":
            return _certify(values[1:] if values else ())
        if values[0] == "release-pin-evidence":
            _evidence_main(values[1:])
            return 0
    except ReleasedCheckerError as exc:
        raise CheckerCliError(str(exc)) from exc
    raise CheckerCliError("command must be certify or release-pin-evidence")
