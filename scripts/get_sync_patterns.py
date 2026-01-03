#!/usr/bin/env python3
"""
Parse .sync-config.yml and output patterns for use by Makefile or shell scripts.

Usage:
    python scripts/get_sync_patterns.py shared        # Get shared patterns
    python scripts/get_sync_patterns.py cap_only      # Get cap-only patterns
    python scripts/get_sync_patterns.py all           # Get all patterns (shared + cap_only)
    python scripts/get_sync_patterns.py root_files    # Get root files only (no globs)
    python scripts/get_sync_patterns.py test_patterns # Get test patterns only
"""
from __future__ import annotations

import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    # Fallback to simple parsing if PyYAML not available
    yaml = None


def parse_yaml_simple(content: str) -> dict:
    """Simple YAML parser for our specific format (no PyYAML needed)."""
    result = {"shared": [], "cap_only": []}
    current_section = None

    for line in content.splitlines():
        line = line.rstrip()

        # Skip comments and empty lines
        if not line or line.lstrip().startswith("#"):
            continue

        # Detect section headers
        if line.startswith("shared:"):
            current_section = "shared"
            continue
        elif line.startswith("cap_only:"):
            current_section = "cap_only"
            continue
        elif line and not line.startswith(" ") and line.endswith(":"):
            current_section = None
            continue

        # Extract pattern from "  - pattern" lines
        stripped = line.lstrip()
        if stripped.startswith("- ") and current_section:
            pattern = stripped[2:].strip()
            result[current_section].append(pattern)

    return result


def load_config(config_path: Path) -> dict:
    """Load sync config from YAML file."""
    content = config_path.read_text()

    if yaml:
        return yaml.safe_load(content)
    else:
        return parse_yaml_simple(content)


def get_root_files(patterns: list[str]) -> list[str]:
    """Extract root-level files (no directory components, no globs)."""
    root_files = []
    for p in patterns:
        # Skip patterns with directory components or globs
        if "/" in p or "*" in p:
            continue
        root_files.append(p)
    return root_files


def get_test_patterns(patterns: list[str]) -> list[str]:
    """Extract test-related patterns."""
    return [p for p in patterns if p.startswith("tests/")]


def main(argv: list[str] | None = None) -> int:
    if argv is None:
        argv = sys.argv[1:]

    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0

    mode = argv[0]

    # Find config file
    script_dir = Path(__file__).parent
    config_path = script_dir.parent / ".sync-config.yml"

    if not config_path.exists():
        print(f"Error: {config_path} not found", file=sys.stderr)
        return 1

    config = load_config(config_path)
    shared = config.get("shared", [])
    cap_only = config.get("cap_only", [])

    if mode == "shared":
        patterns = shared
    elif mode == "cap_only":
        patterns = cap_only
    elif mode == "all":
        patterns = shared + cap_only
    elif mode == "root_files":
        patterns = get_root_files(shared)
    elif mode == "test_patterns":
        patterns = get_test_patterns(shared)
    else:
        print(f"Unknown mode: {mode}", file=sys.stderr)
        return 1

    # Output space-separated for Makefile, one per line for scripts
    if sys.stdout.isatty():
        for p in patterns:
            print(p)
    else:
        print(" ".join(patterns))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
