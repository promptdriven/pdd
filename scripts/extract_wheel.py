#!/usr/bin/env python3
"""Extract the newest local pdd_cli wheel for inspection."""

from __future__ import annotations

import argparse
import shutil
import zipfile
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dist-dir",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "dist",
        help="Directory containing pdd_cli-*.whl files.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=None,
        help="Directory to extract into. Defaults to <dist-dir>/extracted.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    dist_dir = args.dist_dir.expanduser().resolve()
    extract_path = (
        args.output_dir.expanduser().resolve()
        if args.output_dir
        else dist_dir / "extracted"
    )

    wheel_files = sorted(dist_dir.glob("pdd_cli-*.whl"), key=lambda path: path.stat().st_mtime)
    if not wheel_files:
        print(f"Error: no wheel files found in {dist_dir}")
        return 1

    wheel_path = wheel_files[-1]
    print(f"Using wheel file: {wheel_path}")

    if extract_path.exists():
        print(f"Removing existing directory: {extract_path}")
        shutil.rmtree(extract_path)

    print(f"Creating directory: {extract_path}")
    extract_path.mkdir(parents=True)

    print(f"Extracting {wheel_path} to {extract_path}")
    with zipfile.ZipFile(wheel_path, "r") as zip_ref:
        zip_ref.extractall(extract_path)

    print("Extraction complete!")
    print("\nExtracted contents:")
    for root, _, files in extract_path.walk():
        level = len(root.relative_to(extract_path).parts)
        indent = " " * 2 * level
        print(f"{indent}{root.name}/")
        subindent = " " * 2 * (level + 1)
        for file in files[:10]:
            print(f"{subindent}{file}")
        if len(files) > 10:
            print(f"{subindent}... and {len(files) - 10} more files")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
