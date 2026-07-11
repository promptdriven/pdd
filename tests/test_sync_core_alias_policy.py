"""Protected approved-alias policy tests."""

import json
import subprocess
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import build_unit_manifest
from pdd.sync_core.alias_policy import load_committed_aliases, load_protected_aliases
from pdd.sync_core.identity import initialize_repository_identity


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def test_candidate_alias_policy_cannot_authorize_itself(tmp_path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "aliases@example.com")
    _git(root, "config", "user.name", "Alias Test")
    initialize_repository_identity(root, REPOSITORY_ID)
    (root / "tracked.txt").write_text("base\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "base")
    base = _git(root, "rev-parse", "HEAD")

    (root / ".pdd").mkdir(exist_ok=True)
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [{"alias_path": "alias", "canonical_path": "canonical"}],
            }
        ),
        encoding="utf-8",
    )
    _git(root, "add", ".pdd/sync-aliases.json")
    _git(root, "commit", "-qm", "candidate adds aliases")
    head = _git(root, "rev-parse", "HEAD")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)

    with pytest.raises(ValueError, match="candidate added protected alias policy"):
        load_protected_aliases(root, manifest)


def test_protected_alias_policy_requires_unchanged_candidate_copy(tmp_path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "aliases@example.com")
    _git(root, "config", "user.name", "Alias Test")
    initialize_repository_identity(root, REPOSITORY_ID)
    (root / ".pdd").mkdir(exist_ok=True)
    policy = {
        "schema_version": 1,
        "aliases": [{"alias_path": "alias", "canonical_path": "canonical"}],
    }
    (root / ".pdd/sync-aliases.json").write_text(json.dumps(policy), encoding="utf-8")
    (root / "tracked.txt").write_text("base\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "protected aliases")
    base = _git(root, "rev-parse", "HEAD")
    policy["aliases"][0]["canonical_path"] = "other"
    (root / ".pdd/sync-aliases.json").write_text(json.dumps(policy), encoding="utf-8")
    _git(root, "add", ".pdd/sync-aliases.json")
    _git(root, "commit", "-qm", "candidate retargets aliases")
    manifest = build_unit_manifest(root, base_ref=base, head_ref="HEAD")

    with pytest.raises(ValueError, match="candidate changed protected alias policy"):
        load_protected_aliases(root, manifest)


def test_protected_alias_policy_rejects_overlapping_authorities(tmp_path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "aliases@example.com")
    _git(root, "config", "user.name", "Alias Test")
    (root / ".pdd").mkdir()
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {"alias_path": "src", "canonical_path": "canonical"},
                    {"alias_path": "src/nested", "canonical_path": "other"},
                ],
            }
        ),
        encoding="utf-8",
    )
    _git(root, "add", ".pdd/sync-aliases.json")
    _git(root, "commit", "-qm", "overlapping aliases")

    with pytest.raises(ValueError, match="overlap"):
        load_committed_aliases(root)
