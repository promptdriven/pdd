"""Protected PDD inventory rollout policy tests."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from pdd.sync_core.manifest import build_unit_manifest


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PATH = ROOT / ".pdd" / "expected-managed.json"
OWNERSHIP_PATH = ROOT / ".pdd" / "sync-ownership.json"
REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
EXPECTED_MANAGED_UNITS = 466


def _git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "-c", "user.name=PDD test", "-c", "user.email=pdd@example.test", "commit", "-m", message)
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()


def test_pdd_protected_inventory_is_complete_and_exact() -> None:
    """The committed PDD tree has a non-waived protected inventory partition."""
    assert EXPECTED_PATH.is_file(), "missing protected expected-managed registry"
    assert OWNERSHIP_PATH.is_file(), "missing protected sync ownership policy"

    expected = json.loads(EXPECTED_PATH.read_text(encoding="utf-8"))
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    assert expected.keys() == {"schema_version", "units"}
    assert expected["schema_version"] == 1
    assert isinstance(expected["units"], list) and expected["units"]
    assert all(set(row) == {"prompt_path", "language_id"} for row in expected["units"])
    identities = {(row["prompt_path"], row["language_id"]) for row in expected["units"]}
    assert len(identities) == len(expected["units"]) == EXPECTED_MANAGED_UNITS

    assert ownership.keys() == {"rules"}
    assert isinstance(ownership["rules"], list) and ownership["rules"]
    assert all(
        row.keys() == {"pattern", "inventory", "role", "owner"}
        and row["inventory"] == "HUMAN_OWNED"
        and row["role"] == "human-maintained"
        and row["owner"] == "pdd-maintainers"
        and not any(token in row["pattern"] for token in ("*", "?", "["))
        for row in ownership["rules"]
    )

    assert not (ROOT / ".pdd" / "sync-waivers.json").exists()
    assert not (ROOT / ".pdd" / "verification-profiles.json").exists()
    assert not (ROOT / ".pdd" / "attestation-trust.json").exists()

    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    assert manifest.repository_id == REPOSITORY_ID
    assert not manifest.invalid_reasons
    assert not manifest.unaccounted_tracked_paths
    assert {(unit.prompt_relpath.as_posix(), unit.language_id) for unit in manifest.expected_managed} == identities
    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS

    managed_prompt_paths = {
        unit.unit_id.prompt_relpath.as_posix() for unit in manifest.managed_units
    }
    assert managed_prompt_paths == {path for path, _language in identities}
    tracked = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", "HEAD"], cwd=ROOT, text=True
    ).splitlines()
    assert {item.candidate_id.artifact_relpath.as_posix() for item in manifest.candidates} == set(tracked)


def test_pdd_registry_prevents_candidate_denominator_reduction(tmp_path: Path) -> None:
    """Candidate additions grow the union; removals remain protected debt."""
    root = tmp_path / "inventory"
    (root / ".pdd").mkdir(parents=True)
    (root / "prompts").mkdir()
    (root / ".pdd" / "repository-id").write_text(f"{REPOSITORY_ID}\n", encoding="ascii")
    (root / ".pdd" / "expected-managed.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "units": [{"prompt_path": "prompts/owned_python.prompt", "language_id": "python"}],
            }
        ),
        encoding="utf-8",
    )
    (root / ".pdd" / "sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "README.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "human-maintained",
                        "owner": "pdd-maintainers",
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    (root / "prompts" / "owned_python.prompt").write_text("owned", encoding="utf-8")
    (root / "README.md").write_text("human", encoding="utf-8")
    _git(root, "init", "-q")
    base = _commit(root, "protected baseline")

    (root / "prompts" / "added_python.prompt").write_text("added", encoding="utf-8")
    added = _commit(root, "candidate addition")
    addition_manifest = build_unit_manifest(root, base_ref=base, head_ref=added)
    assert len(addition_manifest.expected_managed) == 2

    _git(root, "rm", "prompts/owned_python.prompt")
    removed = _commit(root, "candidate removal")
    removal_manifest = build_unit_manifest(root, base_ref=base, head_ref=removed)
    assert len(removal_manifest.expected_managed) == 2
    assert any("removed managed unit lacks" in reason for reason in removal_manifest.invalid_reasons)
