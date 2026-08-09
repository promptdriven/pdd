#!/usr/bin/env python3
"""Check that pyproject.toml dependencies match requirements.txt."""

import re
import sys
import tomllib
from pathlib import Path


def normalize_name(name: str) -> str:
    """Normalize package name for comparison."""
    # Handle extras like litellm[caching] -> litellm-caching
    name = name.replace("[", "-").replace("]", "")
    # Extract just the package name (before version specifiers)
    match = re.match(r"^([a-zA-Z0-9_-]+)", name)
    if match:
        # Normalize: lowercase and replace _ with -
        return match.group(1).lower().replace("_", "-")
    return name.lower()


def parse_requirements(requirements_path: Path) -> set:
    """Parse requirements.txt and return normalized package names."""
    deps = set()
    with open(requirements_path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                deps.add(normalize_name(line))
    return deps


def main():
    """Main entry point."""
    script_dir = Path(__file__).parent
    project_root = script_dir.parent

    pyproject_path = project_root / "pyproject.toml"
    requirements_path = project_root / "requirements.txt"

    # Parse pyproject.toml
    with open(pyproject_path, "rb") as f:
        toml_data = tomllib.load(f)

    # Get production dependencies
    toml_prod_deps = set()
    for dep in toml_data.get("project", {}).get("dependencies", []):
        toml_prod_deps.add(normalize_name(dep))

    # Get dev dependencies
    toml_dev_deps = set()
    optional_deps = toml_data.get("project", {}).get("optional-dependencies", {})
    for dep in optional_deps.get("dev", []):
        toml_dev_deps.add(normalize_name(dep))

    # Combined toml deps (prod + dev)
    toml_all_deps = toml_prod_deps | toml_dev_deps

    # Parse requirements.txt
    req_deps = parse_requirements(requirements_path)

    # Compare production + dev dependencies
    in_req_not_toml = req_deps - toml_all_deps
    in_toml_not_req = toml_all_deps - req_deps

    has_errors = False

    if in_req_not_toml or in_toml_not_req:
        has_errors = True
        print("ERROR: Dependency mismatch detected!")
        if in_req_not_toml:
            print(f"  In requirements.txt but not pyproject.toml: {sorted(in_req_not_toml)}")
        if in_toml_not_req:
            print(f"  In pyproject.toml but not requirements.txt: {sorted(in_toml_not_req)}")
        print("\nPlease sync dependencies before releasing.")
        print("  - pyproject.toml is the source of truth for pip installs")
        print("  - requirements.txt should include both prod and dev dependencies")

    if has_errors:
        sys.exit(1)
    else:
        print("Dependencies are in sync.")
        print(f"  Production deps: {len(toml_prod_deps)}")
        print(f"  Dev deps: {len(toml_dev_deps)}")
        print(f"  Total in requirements.txt: {len(req_deps)}")


if __name__ == "__main__":
    main()
