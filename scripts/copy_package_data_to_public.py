#!/usr/bin/env python3
"""
Copy package-data files defined in pyproject.toml to a public repo directory.

Reads [tool.setuptools.package-data]["pdd"] and copies matched files from
the local 'pdd/' package into DEST/pdd/, preserving relative paths.
"""
from __future__ import annotations

import argparse
import glob
import os
import shutil
import sys


def load_package_data_patterns(pyproject_path: str) -> list[str]:
    try:
        import tomllib  # Python 3.11+
    except Exception as exc:  # pragma: no cover
        print(f"Error: tomllib not available: {exc}", file=sys.stderr)
        return []

    with open(pyproject_path, "rb") as f:
        cfg = tomllib.load(f)

    return (
        cfg.get("tool", {})
        .get("setuptools", {})
        .get("package-data", {})
        .get("pdd", [])
        or []
    )


def copy_patterns_to_public(patterns: list[str], dest_root: str, base: str = "pdd") -> int:
    copied = 0
    for pattern in patterns:
        for src in glob.glob(os.path.join(base, pattern)):
            rel = os.path.relpath(src, base)
            dest = os.path.join(dest_root, base, rel)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            shutil.copy2(src, dest)
            print(f"  Copied {src} -> {dest}")
            copied += 1
    return copied


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dest", required=True, help="Destination public directory root")
    parser.add_argument(
        "--project-root",
        default=os.getcwd(),
        help="Project root containing pyproject.toml (default: cwd)",
    )
    args = parser.parse_args(argv)

    pyproject_path = os.path.join(args.project_root, "pyproject.toml")
    if not os.path.isfile(pyproject_path):
        print(f"Error: pyproject.toml not found at {pyproject_path}", file=sys.stderr)
        return 1

    patterns = load_package_data_patterns(pyproject_path)
    if not patterns:
        print("No package-data patterns found under [tool.setuptools.package-data]['pdd'].")
        return 0

    os.makedirs(os.path.join(args.dest, "pdd"), exist_ok=True)
    copied = copy_patterns_to_public(patterns, args.dest)
    print(f"Total files copied from pyproject package-data: {copied}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

