#!/usr/bin/env python3
"""
Copy publishable assets to a public repo directory.

Supports two modes:
1. pyproject.toml mode (original): Copy package-data and Python modules
2. YAML config mode (--config): Copy files from .sync-config.yml sections

Both modes preserve relative paths under DEST/.
"""
from __future__ import annotations

import argparse
import glob
import fnmatch
import os
import shutil
import sys


# ============================================================================
# YAML Config Support
# ============================================================================

def parse_yaml_simple(content: str) -> dict:
    """Parse simple YAML without PyYAML dependency.

    Supports only the structure used in .sync-config.yml:
    - Top-level keys ending with ':'
    - List items starting with '- '
    - Comments starting with '#'
    """
    result: dict[str, list[str]] = {}
    current_section: str | None = None

    for line in content.splitlines():
        stripped = line.strip()

        # Skip empty lines and comments
        if not stripped or stripped.startswith('#'):
            continue

        # Check for section header (key:)
        if stripped.endswith(':') and not stripped.startswith('-'):
            current_section = stripped[:-1].strip()
            result[current_section] = []
            continue

        # Check for list item (- value)
        if stripped.startswith('- ') and current_section is not None:
            value = stripped[2:].strip()
            # Remove inline comments
            if '#' in value:
                value = value.split('#')[0].strip()
            if value:
                result[current_section].append(value)

    return result


def load_sync_config(config_path: str) -> dict:
    """Load patterns from .sync-config.yml."""
    try:
        import yaml
        with open(config_path, 'r', encoding='utf-8') as f:
            return yaml.safe_load(f) or {}
    except ImportError:
        with open(config_path, 'r', encoding='utf-8') as f:
            return parse_yaml_simple(f.read())


def copy_from_sync_config(
    config: dict,
    sections: list[str],
    exclude_section: str,
    dest: str,
    project_root: str
) -> int:
    """Copy files from specified YAML sections, applying exclusions.

    Args:
        config: Parsed YAML config dict
        sections: List of section names to copy (e.g., ['shared', 'cap_only'])
        exclude_section: Section name containing exclusion patterns
        dest: Destination directory root
        project_root: Source project root

    Returns:
        Number of files copied
    """
    # Collect all patterns from specified sections
    patterns: list[str] = []
    for section in sections:
        patterns.extend(config.get(section, []))

    # Get exclusion patterns
    exclude_patterns: list[str] = config.get(exclude_section, [])

    def is_excluded(rel_path: str) -> bool:
        """Check if a relative path matches any exclusion pattern."""
        for xpat in exclude_patterns:
            if fnmatch.fnmatch(rel_path, xpat):
                return True
            # Also try matching just the filename
            if fnmatch.fnmatch(os.path.basename(rel_path), xpat):
                return True
        return False

    copied = 0
    copied_paths: set[str] = set()
    processed_dirs: set[str] = set()

    for pattern in patterns:
        # Expand glob pattern relative to project root
        full_pattern = os.path.join(project_root, pattern)
        matches = glob.glob(full_pattern, recursive=True)

        for src in sorted(matches):
            rel_path = os.path.relpath(src, project_root)

            # Skip excluded files
            if is_excluded(rel_path):
                continue

            dest_path = os.path.join(dest, rel_path)

            if os.path.isdir(src):
                # Handle directory: walk and copy all files
                dir_path = os.path.normpath(src)
                if any(dir_path == seen or dir_path.startswith(seen + os.sep)
                       for seen in processed_dirs):
                    continue
                processed_dirs.add(dir_path)

                for root, dirs, files in os.walk(src, followlinks=True):
                    # Skip __pycache__ directories
                    dirs[:] = [d for d in dirs if d != '__pycache__']

                    for fname in files:
                        src_file = os.path.join(root, fname)
                        rel_file = os.path.relpath(src_file, project_root)

                        if is_excluded(rel_file):
                            continue

                        dest_file = os.path.join(dest, rel_file)
                        if dest_file in copied_paths:
                            continue

                        os.makedirs(os.path.dirname(dest_file), exist_ok=True)
                        shutil.copy2(src_file, dest_file)
                        copied_paths.add(dest_file)
                        print(f"  Copied {rel_file}")
                        copied += 1
            else:
                # Handle single file
                if dest_path in copied_paths:
                    continue

                os.makedirs(os.path.dirname(dest_path), exist_ok=True)
                shutil.copy2(src, dest_path)
                copied_paths.add(dest_path)
                print(f"  Copied {rel_path}")
                copied += 1

    return copied


# ============================================================================
# pyproject.toml Support (original functionality)
# ============================================================================

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
    processed_dirs: set[str] = set()
    copied_paths: set[str] = set()
    for pattern in patterns:
        matches = glob.glob(os.path.join(base, pattern), recursive=True)
        for src in sorted(matches):
            if os.path.isdir(src):
                dir_path = os.path.normpath(src)
                if any(dir_path == seen or dir_path.startswith(seen + os.sep) for seen in processed_dirs):
                    continue
                processed_dirs.add(dir_path)

                copied_in_dir = 0
                for root, _, files in os.walk(src):
                    rel_dir = os.path.relpath(root, base)
                    dest_dir = os.path.join(dest_root, base, rel_dir)
                    os.makedirs(dest_dir, exist_ok=True)
                    for fname in files:
                        src_file = os.path.join(root, fname)
                        dest_file = os.path.join(dest_dir, fname)
                        if dest_file in copied_paths:
                            continue
                        shutil.copy2(src_file, dest_file)
                        copied_paths.add(dest_file)
                        print(f"  Copied {src_file} -> {dest_file}")
                        copied += 1
                        copied_in_dir += 1

                if copied_in_dir == 0:
                    rel_dir = os.path.relpath(src, base)
                    dest_dir = os.path.join(dest_root, base, rel_dir)
                    os.makedirs(dest_dir, exist_ok=True)
                    print(f"  Created directory {src} -> {dest_dir}")
                continue

            rel = os.path.relpath(src, base)
            dest = os.path.join(dest_root, base, rel)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            if dest in copied_paths:
                continue
            shutil.copy2(src, dest)
            copied_paths.add(dest)
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

    # YAML config mode (new)
    parser.add_argument(
        "--config",
        help="Path to .sync-config.yml for YAML-driven sync mode",
    )
    parser.add_argument(
        "--sections",
        nargs="+",
        default=[],
        help="Sections to copy from config (e.g., shared cap_only)",
    )

    # Optional: add extra package-data copy patterns (relative to 'pdd/')
    parser.add_argument(
        "--extra-pattern",
        action="append",
        default=[],
        help="Additional glob patterns under 'pdd/' to copy (can be repeated). Example: 'prompts/**/*.prompt'",
    )

    # Optional: copy tests
    parser.add_argument("--copy-tests", action="store_true", help="Copy core tests to public repo")
    parser.add_argument(
        "--tests-include",
        action="append",
        default=[],
        help="Glob pattern of test files to include (can be repeated)",
    )
    parser.add_argument(
        "--tests-exclude",
        action="append",
        default=[],
        help="Glob pattern of test files to exclude (can be repeated)",
    )
    # Optional: copy context examples
    parser.add_argument("--copy-context", action="store_true", help="Copy context example files to public repo")
    parser.add_argument(
        "--context-include",
        action="append",
        default=[],
        help="Glob pattern of context files to include (can be repeated)",
    )
    parser.add_argument(
        "--context-exclude",
        action="append",
        default=[],
        help="Glob pattern of context files to exclude (can be repeated)",
    )
    args = parser.parse_args(argv)

    # YAML config mode: if --config is provided, use YAML-driven sync
    if args.config:
        if not os.path.isfile(args.config):
            print(f"Error: config file not found: {args.config}", file=sys.stderr)
            return 1

        if not args.sections:
            print("Error: --sections required when using --config", file=sys.stderr)
            return 1

        print(f"Loading sync config from {args.config}")
        config = load_sync_config(args.config)

        print(f"Copying files from sections: {', '.join(args.sections)}")
        copied = copy_from_sync_config(
            config,
            sections=args.sections,
            exclude_section="exclude",
            dest=args.dest,
            project_root=args.project_root,
        )
        print(f"Total files copied from config: {copied}")
        return 0

    # Original pyproject.toml mode
    pyproject_path = os.path.join(args.project_root, "pyproject.toml")
    if not os.path.isfile(pyproject_path):
        print(f"Error: pyproject.toml not found at {pyproject_path}", file=sys.stderr)
        return 1

    # Copy package data
    patterns = load_package_data_patterns(pyproject_path)
    # Allow callers to include extra patterns (e.g., all prompts for CAP repo)
    if args.extra_pattern:
        patterns = list(patterns) + list(args.extra_pattern)
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

    # Optionally copy tests
    if args.copy_tests:
        # Build candidate set from include patterns
        candidates: set[str] = set()
        # argparse converts dashes to underscores
        include_patterns = args.tests_include or []
        if not include_patterns:
            # Sensible defaults if none provided
            include_patterns = [
                "tests/test_*.py",
                "tests/__init__.py",
            ]
        for pat in include_patterns:
            # Enable recursive ** patterns
            for path in glob.glob(os.path.join(args.project_root, pat), recursive=True):
                if os.path.isfile(path):
                    candidates.add(path)

        # Filter via exclude patterns
        def is_excluded(path: str) -> bool:
            rel = os.path.relpath(path, args.project_root)
            for xpat in args.tests_exclude or []:
                if fnmatch.fnmatch(rel, xpat) or fnmatch.fnmatch(path, xpat):
                    return True
            return False

        copied_tests = 0
        for src in sorted(candidates):
            if is_excluded(src):
                continue
            rel = os.path.relpath(src, args.project_root)
            dest = os.path.join(args.dest, rel)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            shutil.copy2(src, dest)
            print(f"  Copied {src} -> {dest}")
            copied_tests += 1
        print(f"Total test files copied: {copied_tests}")

    # Optionally copy context example files
    if args.copy_context:
        candidates: set[str] = set()
        include_patterns = args.context_include or []
        if not include_patterns:
            include_patterns = [
                "context/*_example.py",
            ]
        for pat in include_patterns:
            for path in glob.glob(os.path.join(args.project_root, pat), recursive=True):
                if os.path.isfile(path):
                    candidates.add(path)

        def is_ctx_excluded(path: str) -> bool:
            rel = os.path.relpath(path, args.project_root)
            for xpat in args.context_exclude or []:
                if fnmatch.fnmatch(rel, xpat) or fnmatch.fnmatch(path, xpat):
                    return True
            return False

        copied_ctx = 0
        for src in sorted(candidates):
            if is_ctx_excluded(src):
                continue
            rel = os.path.relpath(src, args.project_root)
            dest = os.path.join(args.dest, rel)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            shutil.copy2(src, dest)
            print(f"  Copied {src} -> {dest}")
            copied_ctx += 1
        print(f"Total context files copied: {copied_ctx}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
