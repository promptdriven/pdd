#!/usr/bin/env python3
"""
Copy publishable assets to a public repo directory based on pyproject.toml.

What gets copied:
- Package data: [tool.setuptools.package-data]["pdd"] patterns
- Python modules: packages matched by [tool.setuptools.packages.find].include

Both are copied preserving relative paths under DEST/.
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


def load_package_include_patterns(pyproject_path: str) -> list[str]:
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
        .get("packages", {})
        .get("find", {})
        .get("include", [])
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


def copy_python_packages_to_public(include_patterns: list[str], project_root: str, dest_root: str) -> int:
    """Copy Python modules from packages matched by include patterns.

    This approximates setuptools.find_packages for our simple case by:
    - Matching top-level directories by pattern (e.g., "pdd*")
    - Selecting directories that look like packages (have __init__.py) or the root "pdd" dir
    - Recursively copying only .py files, skipping __pycache__ and .pyc
    """
    copied = 0

    # Resolve candidate top-level package directories
    candidates: set[str] = set()
    for pat in include_patterns:
        # Only support simple top-level patterns like "pdd*"
        for path in glob.glob(os.path.join(project_root, pat)):
            if os.path.isdir(path) and not path.endswith('.egg-info'):
                # Must be a package or the base dir "pdd"
                if os.path.isfile(os.path.join(path, "__init__.py")) or os.path.basename(path) == "pdd":
                    candidates.add(path)

    # For each candidate, walk and copy .py files preserving path under dest_root
    for pkg_dir in sorted(candidates):
        for root, dirs, files in os.walk(pkg_dir):
            # Skip cache and egg-info
            dirs[:] = [d for d in dirs if d != "__pycache__" and not d.endswith('.egg-info')]
            for fname in files:
                if not fname.endswith('.py'):
                    continue
                src = os.path.join(root, fname)
                rel = os.path.relpath(src, project_root)
                dest = os.path.join(dest_root, rel)
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

    # Copy package data
    patterns = load_package_data_patterns(pyproject_path)
    if patterns:
        os.makedirs(os.path.join(args.dest, "pdd"), exist_ok=True)
        copied_data = copy_patterns_to_public(patterns, args.dest)
        print(f"Total files copied from package-data: {copied_data}")
    else:
        print("No package-data patterns found under [tool.setuptools.package-data]['pdd'].")

    # Copy Python modules based on include patterns
    include_patterns = load_package_include_patterns(pyproject_path)
    if include_patterns:
        copied_py = copy_python_packages_to_public(include_patterns, args.project_root, args.dest)
        print(f"Total Python files copied from packages: {copied_py}")
    else:
        print("No package include patterns found under [tool.setuptools.packages.find].include.")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
