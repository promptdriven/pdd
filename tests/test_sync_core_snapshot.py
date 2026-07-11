"""Tests for complete multi-artifact snapshots and include closure binding."""

import json
import os
import subprocess
from pathlib import Path

from pdd.sync_core import (
    build_unit_manifest,
    build_unit_snapshot,
    load_verification_profiles,
)
from pdd.sync_core.identity import initialize_repository_identity


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _repository(
    tmp_path: Path, *, query: bool = False, approved_alias: bool = False
) -> tuple[Path, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "snapshot@example.com")
    _git(root, "config", "user.name", "Snapshot Test")
    initialize_repository_identity(root, REPOSITORY_ID)
    for directory in ("prompts", "src", "docs", "tests"):
        (root / directory).mkdir()
    include = (
        '<include query="summarize">docs/widget.md</include>'
        if query
        else "<include>docs/widget.md</include>"
    )
    (root / "prompts/widget_python.prompt").write_text(f"REQ-1: widget\n{include}\n")
    (root / "docs/widget.md").write_text("Widget contract\n")
    (root / "src/widget.py").write_text("value = 1\n")
    (root / "tests/test_widget.py").write_text("def test_widget(): pass\n")
    (root / "tests/test_widget_e2e.py").write_text("def test_e2e(): pass\n")
    (root / "notes.md").write_text("Human-owned release notes\n")
    (root / "release.md").write_text("Unrelated human-owned file\n")
    (root / ".pdd/sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "*.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "documentation",
                        "owner": "docs@example.com",
                    }
                ]
            }
        )
    )
    os.chmod(root / "tests/test_widget_e2e.py", 0o755)
    (root / "architecture.json").write_text(
        json.dumps(
            [{"filename": "widget_python.prompt", "filepath": "src/widget.py"}]
        )
    )
    (root / ".pdd/verification-profiles.json").write_text(
        json.dumps(
            {
                "profiles": [
                    {
                        "prompt_path": "prompts/widget_python.prompt",
                        "language_id": "python",
                        "required_requirement_ids": ["REQ-1"],
                        "obligations": [
                            {
                                "obligation_id": "tests",
                                "kind": "test",
                                "validator_id": "pytest",
                                "validator_config_digest": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
                                "requirement_ids": ["REQ-1"],
                                "artifact_paths": [
                                    "tests/test_widget.py",
                                    "tests/test_widget_e2e.py",
                                ],
                                "code_under_test_paths": ["notes.md"],
                            }
                        ],
                    }
                ]
            }
        )
    )
    if approved_alias:
        (root / "canonical").mkdir()
        (root / "src/widget.py").rename(root / "canonical/widget.py")
        (root / "src").rmdir()
        (root / "src").symlink_to("canonical", target_is_directory=True)
        (root / ".pdd/sync-aliases.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "aliases": [
                        {"alias_path": "src", "canonical_path": "canonical"}
                    ],
                }
            )
        )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "snapshot fixture")
    return root, _git(root, "rev-parse", "HEAD")


def test_snapshot_contains_prompt_include_code_and_all_tests(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profile = load_verification_profiles(root, manifest).profiles[0]
    snapshot = build_unit_snapshot(root, manifest, manifest.managed_units[0], profile)
    identities = {(item.role, item.relpath.as_posix()) for item in snapshot.artifacts}
    assert identities == {
        ("prompt", "prompts/widget_python.prompt"),
        ("include", "docs/widget.md"),
        ("code", "src/widget.py"),
        ("test", "tests/test_widget.py"),
        ("test", "tests/test_widget_e2e.py"),
        ("code", "notes.md"),
    }
    executable = next(
        item for item in snapshot.artifacts if item.relpath.name == "test_widget_e2e.py"
    )
    assert executable.git_mode == "100755"


def test_code_under_test_bytes_invalidate_snapshot(tmp_path) -> None:
    root, base = _repository(tmp_path)
    manifest = build_unit_manifest(root, base_ref=base, head_ref=base)
    profile = load_verification_profiles(root, manifest).profiles[0]
    before = build_unit_snapshot(root, manifest, manifest.managed_units[0], profile)
    (root / "notes.md").write_text("Changed product bytes\n")
    _git(root, "add", "notes.md")
    _git(root, "commit", "-q", "-m", "change declared product")
    head = _git(root, "rev-parse", "HEAD")
    changed_manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    changed_profile = load_verification_profiles(root, changed_manifest).profiles[0]
    after = build_unit_snapshot(
        root, changed_manifest, changed_manifest.managed_units[0], changed_profile
    )
    assert before.digest() != after.digest()


def test_snapshot_accepts_base_protected_approved_alias(tmp_path) -> None:
    root, commit = _repository(tmp_path, approved_alias=True)
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profile = load_verification_profiles(root, manifest).profiles[0]

    snapshot = build_unit_snapshot(root, manifest, manifest.managed_units[0], profile)

    assert any(item.relpath.as_posix() == "src/widget.py" for item in snapshot.artifacts)


def test_snapshot_allows_regular_code_edit_between_protected_trees(tmp_path) -> None:
    root, base = _repository(tmp_path)
    (root / "src/widget.py").write_text("value = 2\n")
    _git(root, "add", "src/widget.py")
    _git(root, "commit", "-q", "-m", "edit managed code")
    head = _git(root, "rev-parse", "HEAD")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    profile = load_verification_profiles(root, manifest).profiles[0]

    snapshot = build_unit_snapshot(root, manifest, manifest.managed_units[0], profile)

    code = next(item for item in snapshot.artifacts if item.role == "code")
    assert code.relpath.as_posix() == "src/widget.py"


def test_query_expansion_cannot_receive_trusted_verified_status(tmp_path) -> None:
    root, commit = _repository(tmp_path, query=True)
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profile = load_verification_profiles(root, manifest).profiles[0]
    snapshot = build_unit_snapshot(root, manifest, manifest.managed_units[0], profile)
    assert snapshot.nondeterministic_inputs is True


def test_unrelated_human_owned_change_does_not_invalidate_unit_snapshot(tmp_path) -> None:
    root, base = _repository(tmp_path)
    first_manifest = build_unit_manifest(root, base_ref=base, head_ref=base)
    first_profile = load_verification_profiles(root, first_manifest).profiles[0]
    first = build_unit_snapshot(
        root, first_manifest, first_manifest.managed_units[0], first_profile
    )

    (root / "release.md").write_text("Unrelated human-owned update\n")
    _git(root, "add", "release.md")
    _git(root, "commit", "-q", "-m", "update release notes")
    head = _git(root, "rev-parse", "HEAD")
    second_manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    second_profile = load_verification_profiles(root, second_manifest).profiles[0]
    second = build_unit_snapshot(
        root, second_manifest, second_manifest.managed_units[0], second_profile
    )

    assert first_manifest.digest() != second_manifest.digest()
    assert first.manifest_digest == second.manifest_digest
    assert first.digest() == second.digest()
