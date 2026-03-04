"""Tests for pdd.architecture_registry module."""

import json
import sys
from pathlib import Path

# Add project root to sys.path
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest

from pdd.architecture_registry import (
    find_architecture_for_project,
    get_modules_for_issue,
    load_registry,
    merge_architecture,
    record_generation,
    save_registry,
)


# --- Merge Tests ---


def test_merge_no_overlap():
    """Disjoint modules merge correctly — all new modules are added."""
    existing = [
        {"filename": "auth_Python.prompt", "priority": 1, "dependencies": []},
    ]
    new = [
        {"filename": "billing_Python.prompt", "priority": 1, "dependencies": []},
    ]

    merged, report = merge_architecture(existing, new, issue_number=42, issue_url="https://github.com/o/r/issues/42")

    assert len(merged) == 2
    filenames = {m["filename"] for m in merged}
    assert filenames == {"auth_Python.prompt", "billing_Python.prompt"}
    assert report["added"] == ["billing_Python.prompt"]
    assert report["updated"] == []
    assert report["unchanged"] == ["auth_Python.prompt"]

    # New module should have origin
    billing = [m for m in merged if m["filename"] == "billing_Python.prompt"][0]
    assert billing["origin"]["issue_number"] == 42

    # Existing module should NOT have origin added
    auth = [m for m in merged if m["filename"] == "auth_Python.prompt"][0]
    assert "origin" not in auth


def test_merge_with_overlap():
    """Overlapping modules update, not duplicate."""
    existing = [
        {"filename": "auth_Python.prompt", "priority": 1, "dependencies": [], "description": "old"},
        {"filename": "db_Python.prompt", "priority": 2, "dependencies": ["auth_Python.prompt"]},
    ]
    new = [
        {"filename": "auth_Python.prompt", "priority": 1, "dependencies": [], "description": "updated"},
        {"filename": "billing_Python.prompt", "priority": 2, "dependencies": ["auth_Python.prompt"]},
    ]

    merged, report = merge_architecture(existing, new, issue_number=43, issue_url="https://github.com/o/r/issues/43")

    assert len(merged) == 3
    assert report["updated"] == ["auth_Python.prompt"]
    assert report["added"] == ["billing_Python.prompt"]
    assert report["unchanged"] == ["db_Python.prompt"]

    # Updated module should have new description and origin
    auth = [m for m in merged if m["filename"] == "auth_Python.prompt"][0]
    assert auth["description"] == "updated"
    assert auth["origin"]["issue_number"] == 43

    # No duplicates
    auth_count = sum(1 for m in merged if m["filename"] == "auth_Python.prompt")
    assert auth_count == 1


def test_merge_preserves_legacy():
    """Modules without origin are preserved unchanged."""
    existing = [
        {"filename": "legacy_Python.prompt", "priority": 1, "dependencies": []},
    ]
    new = [
        {"filename": "new_Python.prompt", "priority": 1, "dependencies": []},
    ]

    merged, report = merge_architecture(existing, new, issue_number=1, issue_url="https://github.com/o/r/issues/1")

    legacy = [m for m in merged if m["filename"] == "legacy_Python.prompt"][0]
    assert "origin" not in legacy
    assert report["unchanged"] == ["legacy_Python.prompt"]


def test_priority_renumbering():
    """Priorities are renumbered after merge to form valid topological order."""
    existing = [
        {"filename": "a_Python.prompt", "priority": 1, "dependencies": []},
        {"filename": "b_Python.prompt", "priority": 2, "dependencies": ["a_Python.prompt"]},
    ]
    new = [
        {"filename": "c_Python.prompt", "priority": 1, "dependencies": ["b_Python.prompt"]},
    ]

    merged, _ = merge_architecture(existing, new, issue_number=10, issue_url="https://github.com/o/r/issues/10")

    # After merge: a(no deps) -> b(deps on a) -> c(deps on b)
    # Priorities should be sequential: 1, 2, 3
    priorities = {m["filename"]: m["priority"] for m in merged}
    assert priorities["a_Python.prompt"] < priorities["b_Python.prompt"]
    assert priorities["b_Python.prompt"] < priorities["c_Python.prompt"]
    assert set(priorities.values()) == {1, 2, 3}


def test_merge_empty_existing():
    """Merging into empty existing produces all new modules."""
    new = [
        {"filename": "a_Python.prompt", "priority": 1, "dependencies": []},
        {"filename": "b_Python.prompt", "priority": 2, "dependencies": ["a_Python.prompt"]},
    ]

    merged, report = merge_architecture([], new, issue_number=1, issue_url="url")

    assert len(merged) == 2
    assert sorted(report["added"]) == ["a_Python.prompt", "b_Python.prompt"]
    assert report["updated"] == []
    assert report["unchanged"] == []


def test_merge_empty_new():
    """Merging empty new preserves all existing modules."""
    existing = [
        {"filename": "a_Python.prompt", "priority": 1, "dependencies": []},
    ]

    merged, report = merge_architecture(existing, [], issue_number=1, issue_url="url")

    assert len(merged) == 1
    assert report["unchanged"] == ["a_Python.prompt"]
    assert report["added"] == []


# --- Registry Tests ---


def test_registry_record_and_load(tmp_path):
    """Registry round-trips correctly."""
    record_generation(
        project_root=tmp_path,
        issue_number=42,
        issue_url="https://github.com/o/r/issues/42",
        modules_added=["auth_Python.prompt"],
        modules_updated=[],
        target_dir=".",
    )

    registry = load_registry(tmp_path)
    assert registry["version"] == 1
    assert len(registry["generations"]) == 1
    gen = registry["generations"][0]
    assert gen["issue_number"] == 42
    assert gen["modules_added"] == ["auth_Python.prompt"]
    assert gen["modules_updated"] == []
    assert gen["target_dir"] == "."
    assert "timestamp" in gen


def test_registry_multiple_generations(tmp_path):
    """Multiple generations are appended."""
    record_generation(tmp_path, 1, "url1", ["a.prompt"], [])
    record_generation(tmp_path, 2, "url2", ["b.prompt"], ["a.prompt"])

    registry = load_registry(tmp_path)
    assert len(registry["generations"]) == 2
    assert registry["generations"][0]["issue_number"] == 1
    assert registry["generations"][1]["issue_number"] == 2


def test_load_registry_missing_file(tmp_path):
    """Loading from non-existent file returns empty registry."""
    registry = load_registry(tmp_path)
    assert registry == {"version": 1, "generations": []}


def test_save_and_load_registry(tmp_path):
    """Save and load registry round-trip."""
    data = {"version": 1, "generations": [{"issue_number": 5}]}
    save_registry(tmp_path, data)

    loaded = load_registry(tmp_path)
    assert loaded == data


# --- Discovery Tests ---


def test_find_architecture_files_root_only(tmp_path):
    """Finds architecture.json at root."""
    (tmp_path / "architecture.json").write_text("[]")

    result = find_architecture_for_project(tmp_path)
    assert len(result) == 1
    assert result[0] == tmp_path / "architecture.json"


def test_find_architecture_files_subdirs(tmp_path):
    """Finds architecture.json in subdirectories."""
    (tmp_path / "architecture.json").write_text("[]")
    sub = tmp_path / "subproject"
    sub.mkdir()
    (sub / "architecture.json").write_text("[]")

    result = find_architecture_for_project(tmp_path)
    assert len(result) == 2
    assert result[0] == tmp_path / "architecture.json"
    assert result[1] == sub / "architecture.json"


def test_find_architecture_files_ignores_hidden(tmp_path):
    """Ignores hidden directories."""
    hidden = tmp_path / ".hidden"
    hidden.mkdir()
    (hidden / "architecture.json").write_text("[]")

    result = find_architecture_for_project(tmp_path)
    assert len(result) == 0


def test_find_architecture_files_none(tmp_path):
    """Returns empty list when no architecture files exist."""
    result = find_architecture_for_project(tmp_path)
    assert result == []


# --- Filter by Issue Tests ---


def test_get_modules_for_issue():
    """Filtering by origin works."""
    arch = [
        {"filename": "a.prompt", "origin": {"issue_number": 42, "issue_url": "url"}},
        {"filename": "b.prompt", "origin": {"issue_number": 43, "issue_url": "url"}},
        {"filename": "c.prompt"},  # No origin (legacy)
        {"filename": "d.prompt", "origin": {"issue_number": 42, "issue_url": "url"}},
    ]

    result = get_modules_for_issue(arch, 42)
    filenames = [m["filename"] for m in result]
    assert filenames == ["a.prompt", "d.prompt"]


def test_get_modules_for_issue_no_match():
    """Returns empty list when no modules match."""
    arch = [
        {"filename": "a.prompt", "origin": {"issue_number": 1}},
    ]
    assert get_modules_for_issue(arch, 999) == []


def test_get_modules_for_issue_no_origin():
    """Legacy modules (no origin) are not matched."""
    arch = [
        {"filename": "a.prompt"},
        {"filename": "b.prompt", "origin": None},
    ]
    assert get_modules_for_issue(arch, 1) == []
