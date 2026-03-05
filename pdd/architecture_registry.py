"""
Architecture registry for tracking multi-issue generation provenance.

Maintains `.pdd/architecture_registry.json` to record which modules came from
which GitHub issue, and provides merge logic for combining new architecture
entries with existing ones.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


def load_registry(project_root: Path) -> dict:
    """Load the architecture registry from .pdd/architecture_registry.json.

    Returns an empty registry structure if the file doesn't exist.
    """
    registry_path = project_root / ".pdd" / "architecture_registry.json"
    if not registry_path.exists():
        return {"version": 1, "generations": []}
    try:
        with open(registry_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return {"version": 1, "generations": []}
        return data
    except (json.JSONDecodeError, OSError):
        return {"version": 1, "generations": []}


def save_registry(project_root: Path, registry: dict) -> None:
    """Save the architecture registry to .pdd/architecture_registry.json."""
    pdd_dir = project_root / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    registry_path = pdd_dir / "architecture_registry.json"
    with open(registry_path, "w", encoding="utf-8") as f:
        json.dump(registry, f, indent=2, ensure_ascii=False)


def record_generation(
    project_root: Path,
    issue_number: int,
    issue_url: str,
    modules_added: List[str],
    modules_updated: List[str],
    target_dir: Optional[str] = None,
) -> None:
    """Record a generation event in the architecture registry."""
    registry = load_registry(project_root)
    registry["generations"].append({
        "issue_number": issue_number,
        "issue_url": issue_url,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "target_dir": target_dir or ".",
        "modules_added": modules_added,
        "modules_updated": modules_updated,
    })
    save_registry(project_root, registry)


def merge_architecture(
    existing_arch: List[dict],
    new_arch: List[dict],
    issue_number: int,
    issue_url: str,
) -> Tuple[List[dict], dict]:
    """Merge new modules into existing architecture.

    - Match by ``filename`` (exact match).
    - New modules: append with origin metadata.
    - Existing modules with same filename: update, track as "updated".
    - Modules only in existing: preserve unchanged.
    - Re-number priorities for valid topological order.

    Returns:
        (merged_arch, merge_report)
        merge_report = {"added": [...], "updated": [...], "unchanged": [...]}
    """
    now = datetime.now(timezone.utc).isoformat()
    origin = {
        "issue_number": issue_number,
        "issue_url": issue_url,
        "generated_at": now,
    }

    # Index existing by filename
    existing_by_name: Dict[str, dict] = {}
    for entry in existing_arch:
        fn = entry.get("filename", "")
        if fn:
            existing_by_name[fn] = entry

    # Index new by filename
    new_by_name: Dict[str, dict] = {}
    for entry in new_arch:
        fn = entry.get("filename", "")
        if fn:
            new_by_name[fn] = entry

    merged: List[dict] = []
    added: List[str] = []
    updated: List[str] = []
    unchanged: List[str] = []

    # Process existing modules
    for fn, entry in existing_by_name.items():
        if fn in new_by_name:
            # Module updated by new generation
            updated_entry = dict(new_by_name[fn])
            updated_entry["origin"] = origin
            merged.append(updated_entry)
            updated.append(fn)
        else:
            # Module preserved from existing
            merged.append(dict(entry))
            unchanged.append(fn)

    # Process new modules not in existing
    for fn, entry in new_by_name.items():
        if fn not in existing_by_name:
            new_entry = dict(entry)
            new_entry["origin"] = origin
            merged.append(new_entry)
            added.append(fn)

    # Re-number priorities based on dependency order
    _renumber_priorities(merged)

    merge_report = {
        "added": added,
        "updated": updated,
        "unchanged": unchanged,
    }
    return merged, merge_report


def _renumber_priorities(arch: List[dict]) -> None:
    """Re-number priorities to form a valid topological order.

    Performs a topological sort based on dependencies, then assigns
    sequential priority numbers starting from 1.
    """
    # Build filename -> entry index map
    name_to_idx: Dict[str, int] = {}
    for i, entry in enumerate(arch):
        name_to_idx[entry.get("filename", "")] = i

    # Build adjacency list (dependency -> dependents)
    in_degree: Dict[int, int] = {i: 0 for i in range(len(arch))}
    adj: Dict[int, List[int]] = {i: [] for i in range(len(arch))}

    for i, entry in enumerate(arch):
        deps = entry.get("dependencies", [])
        for dep in deps:
            if dep in name_to_idx:
                dep_idx = name_to_idx[dep]
                adj[dep_idx].append(i)
                in_degree[i] += 1

    # Kahn's algorithm
    queue = [i for i in range(len(arch)) if in_degree[i] == 0]
    # Sort queue by original priority to maintain stability
    queue.sort(key=lambda i: arch[i].get("priority", 999))
    order: List[int] = []

    while queue:
        # Process lowest-priority-first for stability
        queue.sort(key=lambda i: arch[i].get("priority", 999))
        node = queue.pop(0)
        order.append(node)
        for neighbor in adj[node]:
            in_degree[neighbor] -= 1
            if in_degree[neighbor] == 0:
                queue.append(neighbor)

    # Handle cycles: append any remaining nodes
    if len(order) < len(arch):
        remaining = [i for i in range(len(arch)) if i not in set(order)]
        remaining.sort(key=lambda i: arch[i].get("priority", 999))
        order.extend(remaining)

    # Sort arch in-place by topological order and assign priorities
    sorted_entries = [arch[i] for i in order]
    for priority, entry in enumerate(sorted_entries, start=1):
        entry["priority"] = priority

    # Replace arch contents
    arch[:] = sorted_entries


def find_architecture_for_project(project_root: Path) -> List[Path]:
    """Discover all architecture.json files (root + subdirs).

    Returns paths sorted with root first, then alphabetically by subdir.
    """
    results: List[Path] = []

    # Check root
    root_arch = project_root / "architecture.json"
    if root_arch.exists():
        results.append(root_arch)

    # Scan immediate subdirectories
    try:
        children = sorted(project_root.iterdir())
    except (OSError, IOError):
        return results

    for child in children:
        if not child.is_dir() or child.name.startswith("."):
            continue
        if child.name in ("node_modules", "__pycache__", ".git"):
            continue
        arch_file = child / "architecture.json"
        if arch_file.exists():
            results.append(arch_file)

    return results


def get_modules_for_issue(arch_data: List[dict], issue_number: int) -> List[dict]:
    """Filter architecture entries by origin.issue_number."""
    return [
        entry for entry in arch_data
        if isinstance(entry.get("origin"), dict)
        and entry["origin"].get("issue_number") == issue_number
    ]
