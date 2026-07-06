"""Command-line entry point for distractor-manifest generation.

Example (from ``research/repo-bloat-benchmark/``)::

    python3 -m harness.distractors.cli \
        --scenario-id off-by-one-pagination \
        --core scenarios/off-by-one-pagination/core \
        --pool snapshots/pdd@<commit>/pool \
        --target-file src/pkg/pagination.py \
        --sizes 1 2 5 10 20 50 \
        --seed 1209 \
        --out distractors/

Writes ``distractors/manifests/<scenario>.<size>.json`` for each ladder step,
persists generated (mutate/template) file contents under
``distractors/generated/``, and refreshes ``distractors/manifests.lock``.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .generator import SIZE_LADDER, GenerationConfig, generate_manifest
from .manifest import ManifestWriter, write_lockfile


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario-id", required=True)
    parser.add_argument("--core", required=True, type=Path, help="core tree (1x base repo)")
    parser.add_argument("--pool", type=Path, default=None, help="snapshot ∖ core tree")
    parser.add_argument("--target-file", required=True, help="core-relative target path")
    parser.add_argument("--sizes", type=int, nargs="+", default=list(SIZE_LADDER))
    parser.add_argument("--seed", type=int, default=1209)
    parser.add_argument("--tolerance-pct", type=float, default=2.0)
    parser.add_argument("--leak-denylist-file", type=Path, default=None,
                        help="file of newline-separated hidden-assertion strings")
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)

    denylist: tuple[str, ...] = ()
    if args.leak_denylist_file:
        denylist = tuple(
            line.strip()
            for line in args.leak_denylist_file.read_text(encoding="utf-8").splitlines()
            if line.strip()
        )

    config = GenerationConfig(
        scenario_id=args.scenario_id,
        core_root=args.core,
        pool_root=args.pool,
        target_file=args.target_file,
        selection_seed=args.seed,
        tolerance_pct=args.tolerance_pct,
        leak_denylist=denylist,
    )
    writer = ManifestWriter(args.out)
    written: list[Path] = []
    for size in args.sizes:
        manifest = generate_manifest(config, size)
        path = writer.write(manifest)
        written.append(path)
        status = "ok" if manifest["budget_met"] else "BUDGET NOT MET"
        print(
            f"{path.name}: {manifest['distractor_tokens_on_disk']} distractor tokens "
            f"({manifest['mode_counts']}) [{status}]"
        )
    write_lockfile(list(writer.manifest_dir.glob("*.json")), args.out / "manifests.lock")
    print(f"lockfile: {args.out / 'manifests.lock'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
