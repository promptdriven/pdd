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


def _repository(tmp_path: Path, *, query: bool = False) -> tuple[Path, str]:
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
                                "validator_config_digest": "pytest-v1",
                                "requirement_ids": ["REQ-1"],
                                "artifact_paths": [
                                    "tests/test_widget.py",
                                    "tests/test_widget_e2e.py",
                                ],
                            }
                        ],
                    }
                ]
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
    }
    executable = next(
        item for item in snapshot.artifacts if item.relpath.name == "test_widget_e2e.py"
    )
    assert executable.git_mode == "100755"


def test_query_expansion_cannot_receive_trusted_verified_status(tmp_path) -> None:
    root, commit = _repository(tmp_path, query=True)
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profile = load_verification_profiles(root, manifest).profiles[0]
    snapshot = build_unit_snapshot(root, manifest, manifest.managed_units[0], profile)
    assert snapshot.nondeterministic_inputs is True
