#!/usr/bin/env python3
"""Stamp / verify ``.pdd/meta`` fingerprints for every PDD dev unit.

Thin wrapper over ``pdd.continuous_sync`` (issue #1927: one implementation shared
with ``pdd reconcile``). The committed ``.pdd/meta/<unit>.json`` fingerprints are
the oracle ``pdd sync`` trusts to decide whether a unit changed; this script keeps
that oracle current for the whole tree and verifies it in CI:

* ``stamp`` (default): for every stampable unit, recompute all hashes from the
  files on disk and write the fingerprint JSON byte-identically to how ``pdd``
  writes it. Idempotent — a unit whose content hashes already match is not
  rewritten (its timestamp is preserved and no file is written), so a repo-wide
  restamp touches only genuinely-changed units.

* ``--check``: recompute every stampable unit's hashes and compare to the committed
  fingerprint; exit non-zero listing units that are stale or missing a fingerprint.
  This is the CI gate (``.github/workflows/unit-tests.yml``); its output shape and
  exit codes are unchanged.

Hashing and unit/path resolution live in ``pdd.continuous_sync`` and use pdd's real
hash functions, so a fingerprint this script writes equals what ``pdd sync`` would
compute. Historically this file vendored a stdlib-only copy of pdd's hashing to run
without importing pdd; issue #1927 removed that second implementation, so the
script now imports pdd (CI installs the package before running the gate).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List, Optional

# Ensure the repo root is importable when run as ``scripts/stamp_fingerprints.py``
# (CI also ``pip install -e``s the package, but this keeps a bare checkout working).
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pdd import continuous_sync as _cs  # pylint: disable=wrong-import-position,no-name-in-module

# Re-exported for callers/tests that imported these from the stamper.
PROMPTS_ROOT = REPO_ROOT / "pdd" / "prompts"
META_DIR = REPO_ROOT / ".pdd" / "meta"
WAIVERS_FILE = REPO_ROOT / "scripts" / "fingerprint_waivers.json"
FIELD_ORDER = _cs.FIELD_ORDER
HASH_FIELDS = _cs.HASH_FIELDS
NEW_UNIT_COMMAND = _cs.NEW_UNIT_COMMAND


# --- Resolution / enumeration (delegated to pdd.continuous_sync) --------------


def Unit(basename: str, prompt: Optional[Path] = None):  # pylint: disable=invalid-name
    """Resolve one unit against the repo layout (compat shim for the stamper API).

    ``prompt`` defaults to the conventional ``pdd/prompts/<basename>_python.prompt``.
    """
    return _cs.resolve_unit(basename, REPO_ROOT, prompt)


def enumerate_units():
    """Return every python unit under ``pdd/prompts`` sorted by basename."""
    return _cs.resolve_units(REPO_ROOT)


def load_pddignore() -> List[str]:
    """Load ``.pddignore`` patterns from the repo root."""
    return _cs.load_pddignore(REPO_ROOT)


def load_waivers() -> Dict[str, str]:
    """Return ``{basename: reason}`` from the committed waiver file."""
    return _cs.load_waivers(WAIVERS_FILE)


def classify(units, pddignore, waivers):
    """Split units into ``(stampable, ignored, waived, no_code)`` buckets."""
    return _cs.partition_units(units, pddignore, waivers, REPO_ROOT)


def read_meta(meta_path: Path) -> Optional[Dict]:
    """Read an existing fingerprint JSON, or None if absent/unreadable."""
    meta_path = Path(meta_path)
    if not meta_path.exists():
        return None
    try:
        data = json.loads(meta_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def compute_hashes(unit, stored_deps: Optional[Dict[str, str]] = None) -> Dict:
    """Recompute all fingerprint hash fields for a unit via pdd's real hasher."""
    return _cs.hashes_for(unit, REPO_ROOT, stored_deps)


def write_meta(meta_path: Path, content: Dict) -> None:
    """Write meta JSON byte-identically to pdd (indent=2, no trailing newline)."""
    meta_path = Path(meta_path)
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    with open(meta_path, "w", encoding="utf-8") as handle:
        json.dump(content, handle, indent=2)


# --- Commands ----------------------------------------------------------------


def cmd_stamp(_args: argparse.Namespace) -> int:
    """Recompute and write fingerprints for every stampable unit (idempotent)."""
    units = enumerate_units()
    pddignore = load_pddignore()
    waivers = load_waivers()
    stampable, ignored, waived, no_code = classify(units, pddignore, waivers)

    written = len(_cs.stamp_units(stampable, REPO_ROOT))

    print(
        f"stamped {written} of {len(stampable)} units "
        f"(unchanged {len(stampable) - written}); "
        f"ignored={len(ignored)} waived={len(waived)} no_code={len(no_code)}"
    )
    if no_code:
        print("WARNING: units with no code file (add to waivers):", file=sys.stderr)
        for unit in no_code:
            print(f"  {unit.basename} -> {unit.code}", file=sys.stderr)
        return 1
    return 0


def cmd_check(_args: argparse.Namespace) -> int:
    """Recompute hashes and diff against committed metas. Non-zero on drift."""
    result = _cs.run_check()
    print(
        f"checked {result.stampable} stampable units; "
        f"ignored={result.ignored} waived={result.waived}"
    )
    if result.no_code:
        print(
            f"\n{len(result.no_code)} unit(s) have no code file and no waiver:",
            file=sys.stderr,
        )
        for name in result.no_code:
            print(f"  {name}", file=sys.stderr)
    if result.missing:
        print(
            f"\n{len(result.missing)} unit(s) missing a committed fingerprint:",
            file=sys.stderr,
        )
        for name in result.missing:
            print(f"  {name}", file=sys.stderr)
    if result.stale:
        print(
            f"\n{len(result.stale)} unit(s) have stale fingerprints "
            f"(run: python scripts/stamp_fingerprints.py):",
            file=sys.stderr,
        )
        for name, diffs in result.stale:
            print(f"  {name}: {', '.join(diffs)}", file=sys.stderr)
    if result.ok:
        print("all fingerprints current")
        return 0
    return 1


def main(argv: Optional[List[str]] = None) -> int:
    """Stamp (default) or verify (``--check``) the repo's ``.pdd/meta`` fingerprints."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify committed fingerprints are current; exit non-zero on drift.",
    )
    args = parser.parse_args(argv)
    if args.check:
        return cmd_check(args)
    return cmd_stamp(args)


if __name__ == "__main__":
    sys.exit(main())
