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


# --- Issue #1010: Nested architecture.json discovery tests ---


def test_find_architecture_depth_2(tmp_path):
    """architecture.json at depth 2+ must be discovered (primary bug reproduction).

    The bug: find_architecture_for_project() only scans 1 level deep,
    missing files like backend/functions/architecture.json.
    """
    # Root architecture.json
    (tmp_path / "architecture.json").write_text("[]")
    # Depth 1: frontend/architecture.json
    (tmp_path / "frontend").mkdir()
    (tmp_path / "frontend" / "architecture.json").write_text("[]")
    # Depth 2: backend/functions/architecture.json (MISSED by buggy code)
    (tmp_path / "backend" / "functions").mkdir(parents=True)
    (tmp_path / "backend" / "functions" / "architecture.json").write_text("[]")
    # Depth 2: extensions/github_pdd_app/architecture.json (MISSED by buggy code)
    (tmp_path / "extensions" / "github_pdd_app").mkdir(parents=True)
    (tmp_path / "extensions" / "github_pdd_app" / "architecture.json").write_text("[]")

    result = find_architecture_for_project(tmp_path)

    # Should find all 4 files; buggy code only finds 2 (root + frontend)
    assert len(result) == 4, (
        f"Expected 4 architecture files (root + 3 nested), got {len(result)}: {result}"
    )
    # Root should be first
    assert result[0] == tmp_path / "architecture.json"
    # All nested files should be present
    found_paths = {str(p.relative_to(tmp_path)) for p in result}
    assert "backend/functions/architecture.json" in found_paths
    assert "extensions/github_pdd_app/architecture.json" in found_paths


def test_find_architecture_depth_3(tmp_path):
    """architecture.json at depth 3+ must also be discovered."""
    (tmp_path / "architecture.json").write_text("[]")
    # Depth 3: a/b/c/architecture.json
    (tmp_path / "a" / "b" / "c").mkdir(parents=True)
    (tmp_path / "a" / "b" / "c" / "architecture.json").write_text("[]")

    result = find_architecture_for_project(tmp_path)

    assert len(result) == 2, (
        f"Expected 2 architecture files (root + depth-3), got {len(result)}: {result}"
    )
    found_paths = {str(p.relative_to(tmp_path)) for p in result}
    assert "a/b/c/architecture.json" in found_paths


def test_find_architecture_skips_excluded_but_finds_valid_nested(tmp_path):
    """Recursive discovery must skip excluded dirs but still find valid nested files.

    This tests that exclusion rules (hidden, node_modules, __pycache__) work
    at all depths while still discovering valid architecture files at depth 2+.
    """
    # Valid nested architecture at depth 2 (should be found)
    (tmp_path / "backend" / "functions").mkdir(parents=True)
    (tmp_path / "backend" / "functions" / "architecture.json").write_text("[]")
    # Excluded: nested hidden dir
    (tmp_path / "backend" / ".hidden").mkdir(parents=True)
    (tmp_path / "backend" / ".hidden" / "architecture.json").write_text("[]")
    # Excluded: nested node_modules
    (tmp_path / "backend" / "node_modules").mkdir(parents=True)
    (tmp_path / "backend" / "node_modules" / "architecture.json").write_text("[]")
    # Excluded: nested __pycache__
    (tmp_path / "backend" / "__pycache__").mkdir(parents=True)
    (tmp_path / "backend" / "__pycache__" / "architecture.json").write_text("[]")

    result = find_architecture_for_project(tmp_path)

    # Buggy code: finds 0 (can't reach depth 2 at all)
    # Fixed code: finds 1 (backend/functions only, excludes the rest)
    assert len(result) == 1, (
        f"Expected 1 architecture file (backend/functions only), got {len(result)}: {result}"
    )
    assert result[0] == tmp_path / "backend" / "functions" / "architecture.json"


def test_load_architecture_includes_depth_2_modules(tmp_path):
    """_load_architecture_json must include modules from depth-2 architecture files.

    This tests the caller integration: even if find_architecture_for_project
    returns depth-2 files, the combined architecture must contain their entries.
    """
    import json as _json
    from pdd.agentic_sync import _load_architecture_json

    # Root architecture with one module
    (tmp_path / "architecture.json").write_text(
        _json.dumps([{"filename": "auth_Python.prompt", "priority": 1, "dependencies": []}])
    )
    # Depth-2 architecture with a different module
    (tmp_path / "backend" / "functions").mkdir(parents=True)
    (tmp_path / "backend" / "functions" / "architecture.json").write_text(
        _json.dumps([{"filename": "admin_approve_user_Python.prompt", "priority": 1, "dependencies": []}])
    )

    combined, _ = _load_architecture_json(tmp_path)

    # Buggy code: combined has only 1 entry (root only, depth-2 missed)
    # Fixed code: combined has 2 entries
    assert combined is not None
    filenames = [e["filename"] for e in combined]
    assert "admin_approve_user_Python.prompt" in filenames, (
        f"Depth-2 module 'admin_approve_user_Python.prompt' missing from combined architecture. "
        f"Got: {filenames}"
    )
    assert len(combined) == 2


def test_filter_invalid_basenames_with_complete_architecture(tmp_path):
    """_filter_invalid_basenames must accept modules from depth-2 architecture files.

    End-to-end: discover nested architecture → build combined list →
    validate basenames. This is the exact failure path from issue #1010.
    """
    import json as _json
    from pdd.agentic_sync import _filter_invalid_basenames, _load_architecture_json

    # Root architecture
    (tmp_path / "architecture.json").write_text(
        _json.dumps([{"filename": "auth_Python.prompt", "priority": 1, "dependencies": []}])
    )
    # Depth-1 architecture
    (tmp_path / "frontend").mkdir()
    (tmp_path / "frontend" / "architecture.json").write_text(
        _json.dumps([{"filename": "dashboard_Python.prompt", "priority": 1, "dependencies": []}])
    )
    # Depth-2 architecture (contains the module that was being rejected)
    (tmp_path / "backend" / "functions").mkdir(parents=True)
    (tmp_path / "backend" / "functions" / "architecture.json").write_text(
        _json.dumps([{"filename": "admin_approve_user_Python.prompt", "priority": 1, "dependencies": []}])
    )

    combined, _ = _load_architecture_json(tmp_path)

    # This is the exact input that was failing in issue #1010
    valid, invalid = _filter_invalid_basenames(
        ["backend/admin_approve_user"], combined
    )

    # Buggy code: admin_approve_user is in invalid (depth-2 file not discovered)
    # Fixed code: admin_approve_user is in valid (tail matches unique basename)
    assert "backend/admin_approve_user" in valid, (
        f"'backend/admin_approve_user' should be valid but was rejected. "
        f"Valid: {valid}, Invalid: {invalid}"
    )
    assert len(invalid) == 0


def test_find_architecture_caller_update_main(tmp_path):
    """update_main.py caller gets depth-2 architecture files from find_architecture_for_project.

    Verifies the other caller also benefits from recursive discovery.
    """
    # Create nested architecture at depth 2
    (tmp_path / "backend" / "functions").mkdir(parents=True)
    (tmp_path / "backend" / "functions" / "architecture.json").write_text(
        json.dumps([{"filename": "nested_module_Python.prompt", "priority": 1}])
    )

    result = find_architecture_for_project(tmp_path)

    # Buggy code: returns [] because depth-2 file is missed
    # Fixed code: returns the depth-2 file
    assert len(result) >= 1, (
        f"Expected at least 1 architecture file (depth-2), got {len(result)}"
    )
    # Verify we can actually load the file (simulating what update_main does)
    arch_data = json.loads(result[0].read_text())
    assert len(arch_data) == 1
    assert arch_data[0]["filename"] == "nested_module_Python.prompt"
