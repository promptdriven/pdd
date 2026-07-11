"""Lifecycle tests for complete base/head candidate inventory."""

import json
import subprocess
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import InventoryStatus, build_unit_manifest
from pdd.sync_core.identity import initialize_repository_identity
from pdd.sync_core.language import LanguageRegistry, LanguageSpec
from pdd.sync_core.manifest import ManifestError


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", message)
    return _git(root, "rev-parse", "HEAD")


def _repository(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "sync@example.com")
    _git(root, "config", "user.name", "Sync Test")
    initialize_repository_identity(
        root, "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
    )
    (root / "prompts").mkdir()
    (root / "src").mkdir()
    (root / "prompts/widget_python.prompt").write_text("Build widget\n")
    (root / "src/widget.py").write_text("value = 1\n")
    (root / "README.md").write_text("Human documentation\n")
    (root / ".pdd/sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "README.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "documentation",
                        "owner": "docs@example.com",
                    }
                ]
            }
        )
    )
    (root / "architecture.json").write_text(
        json.dumps(
            [{"filename": "widget_python.prompt", "filepath": "src/widget.py"}]
        )
    )
    return root


def test_manifest_partitions_every_base_and_head_path(tmp_path) -> None:
    root = _repository(tmp_path)
    base = _commit(root, "base")
    (root / "prompts/helper_python.prompt").write_text("Build helper\n")
    head = _commit(root, "head")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    tracked = set(_git(root, "ls-tree", "-r", "--name-only", head).splitlines())
    assert {item.candidate_id.artifact_relpath.as_posix() for item in manifest.candidates} == tracked
    assert manifest.unaccounted_tracked_paths == ()
    assert len(manifest.expected_managed) == 2
    assert len(manifest.managed_units) == 2
    readme = next(
        item for item in manifest.candidates if item.candidate_id.artifact_relpath.as_posix() == "README.md"
    )
    assert readme.inventory is InventoryStatus.HUMAN_OWNED


def test_removed_prompt_remains_expected_and_requires_tombstone(tmp_path) -> None:
    root = _repository(tmp_path)
    base = _commit(root, "base")
    (root / "prompts/widget_python.prompt").unlink()
    head = _commit(root, "remove prompt")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert len(manifest.expected_managed) == 1
    assert manifest.managed_units == ()
    assert any("lacks a complete" in reason for reason in manifest.invalid_reasons)


def test_protected_tombstone_accounts_for_removed_unit(tmp_path) -> None:
    root = _repository(tmp_path)
    _commit(root, "base")
    tombstone = root / ".pdd/sync-tombstones.json"
    tombstone.write_text(
        json.dumps(
            [
                {
                    "prompt_path": "prompts/widget_python.prompt",
                    "artifact_paths": [
                        "prompts/widget_python.prompt",
                        "src/widget.py",
                    ],
                    "rationale": "Widget was deliberately retired",
                    "owner": "sync-owner@example.com",
                    "baseline_status": "IN_SYNC",
                }
            ]
        )
    )
    base = _commit(root, "authorize decommission")
    (root / "prompts/widget_python.prompt").unlink()
    head = _commit(root, "decommission widget")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert not any("lacks a complete" in reason for reason in manifest.invalid_reasons)
    assert manifest.units[0].tombstoned is True
    assert len(manifest.expected_managed) == 1


def test_retired_unit_stale_alias_cannot_account_canonical_candidate(tmp_path) -> None:
    root = _repository(tmp_path)
    (root / "prompts/helper_python.prompt").write_text("Build helper\n")
    (root / "src/helper.py").write_text("helper = True\n")
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {"filename": "widget_python.prompt", "filepath": "src/widget.py"},
                {"filename": "helper_python.prompt", "filepath": "src/helper.py"},
            ]
        )
    )
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
    (root / ".pdd/sync-tombstones.json").write_text(
        json.dumps(
            [
                {
                    "prompt_path": "prompts/widget_python.prompt",
                    "artifact_paths": [
                        "prompts/widget_python.prompt",
                        "src/widget.py",
                    ],
                    "rationale": "Widget was deliberately retired",
                    "owner": "sync-owner@example.com",
                    "baseline_status": "IN_SYNC",
                }
            ]
        )
    )
    base = _commit(root, "authorize retirement with stale alias")
    (root / "canonical").mkdir()
    (root / "canonical/widget.py").write_text("candidate = True\n")
    (root / "prompts/widget_python.prompt").unlink()
    (root / "src/widget.py").unlink()
    (root / "architecture.json").write_text(
        json.dumps(
            [{"filename": "helper_python.prompt", "filepath": "src/helper.py"}]
        )
    )
    head = _commit(root, "retire widget and add canonical candidate")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)

    assert any("unchanged symlink" in reason for reason in manifest.invalid_reasons)
    assert PurePosixPath("canonical/widget.py") in manifest.unaccounted_tracked_paths
    candidate = next(
        item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath == PurePosixPath("canonical/widget.py")
    )
    assert candidate.inventory is InventoryStatus.INVALID


def test_incomplete_tombstone_cannot_reduce_expected_managed(tmp_path) -> None:
    root = _repository(tmp_path)
    _commit(root, "base")
    (root / ".pdd/sync-tombstones.json").write_text(
        json.dumps(
            [
                {
                    "prompt_path": "prompts/widget_python.prompt",
                    "artifact_paths": ["prompts/widget_python.prompt"],
                    "rationale": "Attempted debt removal",
                    "owner": "candidate",
                    "baseline_status": "DRIFTED",
                }
            ]
        )
    )
    base = _commit(root, "attempt decommission authorization")
    (root / "prompts/widget_python.prompt").unlink()
    head = _commit(root, "incomplete tombstone")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert len(manifest.expected_managed) == 1
    assert any("complete IN_SYNC tombstone" in item for item in manifest.invalid_reasons)


def test_protected_registry_preserves_and_authorizes_denominator_transition(
    tmp_path,
) -> None:
    root = _repository(tmp_path)
    _commit(root, "base")
    (root / ".pdd/expected-managed.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "units": [
                    {
                        "prompt_path": "prompts/widget_python.prompt",
                        "language_id": "python",
                    }
                ],
            }
        )
    )
    (root / ".pdd/sync-tombstones.json").write_text(
        json.dumps(
            [
                {
                    "prompt_path": "prompts/widget_python.prompt",
                    "artifact_paths": [
                        "prompts/widget_python.prompt",
                        "src/widget.py",
                    ],
                    "rationale": "Widget was deliberately retired",
                    "owner": "sync-owner@example.com",
                    "baseline_status": "IN_SYNC",
                }
            ]
        )
    )
    authorized = _commit(root, "protect decommission authorization")
    (root / "prompts/widget_python.prompt").unlink()
    (root / "src/widget.py").unlink()
    (root / "architecture.json").write_text("[]\n")
    removed = _commit(root, "remove authorized widget")

    transition = build_unit_manifest(root, base_ref=authorized, head_ref=removed)
    stable = build_unit_manifest(root, base_ref=removed, head_ref=removed)
    assert transition.expected_managed == ()
    assert stable.expected_managed == ()
    assert transition.invalid_reasons == ()
    assert stable.invalid_reasons == ()


def test_architecture_mapping_prefers_project_prompt_root_over_duplicate_leaf(
    tmp_path,
) -> None:
    root = _repository(tmp_path)
    nested = root / "prompts/nested"
    nested.mkdir()
    (nested / "widget_python.prompt").write_text("Build another widget\n")
    commit = _commit(root, "ambiguous prompt")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    assert not any("has 2 matches" in reason for reason in manifest.invalid_reasons)
    widget = next(
        unit
        for unit in manifest.managed_units
        if unit.unit_id.prompt_relpath.as_posix() == "prompts/widget_python.prompt"
    )
    assert widget.artifact_paths == (Path("src/widget.py"),)


def test_unmatched_tracked_path_is_unaccounted_not_default_human(tmp_path) -> None:
    root = _repository(tmp_path)
    (root / "src/orphan.py").write_text("orphan = True\n")
    commit = _commit(root, "orphan")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    assert [path.as_posix() for path in manifest.unaccounted_tracked_paths] == [
        "src/orphan.py"
    ]
    orphan = next(
        item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix() == "src/orphan.py"
    )
    assert orphan.inventory is InventoryStatus.INVALID


def test_duplicate_protected_ownership_pattern_is_rejected(tmp_path) -> None:
    """Exact ownership policy patterns remain a deterministic partition."""
    root = _repository(tmp_path)
    policy_path = root / ".pdd/sync-ownership.json"
    policy = json.loads(policy_path.read_text())
    policy["rules"].append(dict(policy["rules"][0]))
    policy_path.write_text(json.dumps(policy))
    commit = _commit(root, "duplicate ownership pattern")

    with pytest.raises(ManifestError, match="duplicate pattern: README.md"):
        build_unit_manifest(root, base_ref=commit, head_ref=commit)


def test_protected_human_rule_precedes_prompt_filename_inference(tmp_path) -> None:
    root = _repository(tmp_path)
    policy = json.loads((root / ".pdd/sync-ownership.json").read_text())
    policy["rules"].append(
        {
            "pattern": "tests/fixtures/**",
            "inventory": "HUMAN_OWNED",
            "role": "test-fixture",
            "owner": "quality@example.com",
        }
    )
    (root / ".pdd/sync-ownership.json").write_text(json.dumps(policy))
    fixture = root / "tests/fixtures/sample_python.prompt"
    fixture.parent.mkdir(parents=True)
    fixture.write_text("This resembles a prompt but is test data\n")
    commit = _commit(root, "human prompt fixture")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    assert len(manifest.managed_units) == 1
    candidate = next(
        item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        == "tests/fixtures/sample_python.prompt"
    )
    assert candidate.inventory is InventoryStatus.HUMAN_OWNED


def test_manifest_digest_ignores_refs_and_dynamic_canonical_state(tmp_path) -> None:
    root = _repository(tmp_path)
    base = _commit(root, "base")
    first = build_unit_manifest(root, base_ref=base, head_ref=base)
    state = root / ".pdd/meta/v2/fingerprint.json"
    state.parent.mkdir(parents=True)
    state.write_text("{}\n")
    head = _commit(root, "canonical state")
    second = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert first.digest() == second.digest()


def test_worktree_repository_id_cannot_change_immutable_manifest_identity(
    tmp_path,
) -> None:
    root = _repository(tmp_path)
    commit = _commit(root, "base")
    (root / ".pdd/repository-id").write_text(
        "11111111-1111-4111-8111-111111111111\n"
    )
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    assert manifest.repository_id == "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"


def test_duplicate_architecture_output_is_invalid(tmp_path) -> None:
    root = _repository(tmp_path)
    architecture = json.loads((root / "architecture.json").read_text())
    architecture.append(dict(architecture[0]))
    (root / "architecture.json").write_text(json.dumps(architecture))
    commit = _commit(root, "duplicate output")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    assert any("duplicate output" in reason for reason in manifest.invalid_reasons)


def test_alias_counterpart_collision_with_concrete_owner_is_invalid(tmp_path) -> None:
    root = _repository(tmp_path)
    (root / "prompts/helper_python.prompt").write_text("Build helper\n")
    (root / "canonical").mkdir()
    (root / "src/widget.py").rename(root / "canonical/widget.py")
    (root / "src").rmdir()
    (root / "src").symlink_to("canonical", target_is_directory=True)
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [{"alias_path": "src", "canonical_path": "canonical"}],
            }
        )
    )
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {"filename": "widget_python.prompt", "filepath": "src/widget.py"},
                {
                    "filename": "helper_python.prompt",
                    "filepath": "canonical/widget.py",
                },
            ]
        )
    )
    commit = _commit(root, "alias and canonical owners")

    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)

    assert any(
        "canonical counterpart" in reason and "canonical/widget.py" in reason
        for reason in manifest.invalid_reasons
    )


def test_two_alias_counterparts_with_different_owners_are_invalid(tmp_path) -> None:
    root = _repository(tmp_path)
    (root / "prompts/helper_python.prompt").write_text("Build helper\n")
    (root / "canonical").mkdir()
    (root / "src/widget.py").rename(root / "canonical/widget.py")
    (root / "src").rmdir()
    (root / "src").symlink_to("canonical", target_is_directory=True)
    (root / "alternate").symlink_to("canonical", target_is_directory=True)
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {"alias_path": "src", "canonical_path": "canonical"},
                    {"alias_path": "alternate", "canonical_path": "canonical"},
                ],
            }
        )
    )
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {"filename": "widget_python.prompt", "filepath": "src/widget.py"},
                {
                    "filename": "helper_python.prompt",
                    "filepath": "alternate/widget.py",
                },
            ]
        )
    )
    commit = _commit(root, "two alias owners")

    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)

    assert any(
        "canonical counterpart" in reason and "canonical/widget.py" in reason
        for reason in manifest.invalid_reasons
    )


def test_architecture_resolves_prompt_from_repository_prompt_root(tmp_path) -> None:
    root = _repository(tmp_path)
    nested_prompt = root / "prompts/backend/widget_python.prompt"
    nested_prompt.parent.mkdir()
    nested_prompt.write_text("Build backend widget\n")
    architecture = json.loads((root / "architecture.json").read_text())
    architecture.append(
        {
            "filename": "backend/widget_python.prompt",
            "filepath": "src/backend_widget.py",
        }
    )
    (root / "architecture.json").write_text(json.dumps(architecture))
    commit = _commit(root, "repository prompt root")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    backend = next(
        unit
        for unit in manifest.managed_units
        if unit.unit_id.prompt_relpath == PurePosixPath(
            "prompts/backend/widget_python.prompt"
        )
    )
    assert backend.artifact_paths == (PurePosixPath("src/backend_widget.py"),)


def test_excluded_project_architecture_is_not_a_canonical_declaration(tmp_path) -> None:
    root = _repository(tmp_path)
    policy = json.loads((root / ".pdd/sync-ownership.json").read_text())
    policy["rules"].append(
        {
            "pattern": "vendor/**",
            "inventory": "HUMAN_OWNED",
            "role": "excluded-project",
            "owner": "vendor@example.com",
        }
    )
    (root / ".pdd/sync-ownership.json").write_text(json.dumps(policy))
    vendor = root / "vendor"
    vendor.mkdir()
    (vendor / "architecture.json").write_text(
        json.dumps(
            [{"filename": "missing_python.prompt", "filepath": "missing.py"}]
        )
    )
    commit = _commit(root, "excluded nested project")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    assert not any("vendor/architecture.json" in item for item in manifest.invalid_reasons)
    architecture = next(
        item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath
        == PurePosixPath("vendor/architecture.json")
    )
    assert architecture.inventory is InventoryStatus.HUMAN_OWNED


def test_nested_architecture_output_is_relative_to_project_root(tmp_path) -> None:
    root = _repository(tmp_path)
    project = root / "project"
    (project / "prompts").mkdir(parents=True)
    (project / "src").mkdir()
    (project / "prompts/nested_python.prompt").write_text("Build nested\n")
    (project / "src/nested.py").write_text("nested = True\n")
    (project / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "nested_python.prompt",
                    "filepath": "src/nested.py",
                }
            ]
        )
    )
    commit = _commit(root, "nested architecture")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    nested = next(
        unit
        for unit in manifest.managed_units
        if unit.unit_id.prompt_relpath
        == PurePosixPath("project/prompts/nested_python.prompt")
    )
    assert nested.artifact_paths == (PurePosixPath("project/src/nested.py"),)


def test_architecture_owned_prompt_output_is_not_a_second_source_unit(tmp_path) -> None:
    root = _repository(tmp_path)
    project = root / "project"
    (project / "prompts").mkdir(parents=True)
    (project / "src").mkdir()
    source = project / "prompts/generated_python.prompt"
    output = project / "src/generated_python.prompt"
    source.write_text("Generate the runtime prompt\n")
    output.write_text("Runtime instructions\n")
    (project / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "generated_python.prompt",
                    "filepath": "src/generated_python.prompt",
                }
            ]
        )
    )
    commit = _commit(root, "generated prompt artifact")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    prompt_paths = {unit.unit_id.prompt_relpath for unit in manifest.managed_units}
    assert PurePosixPath("project/prompts/generated_python.prompt") in prompt_paths
    assert PurePosixPath("project/src/generated_python.prompt") not in prompt_paths
    generated = next(
        unit
        for unit in manifest.managed_units
        if unit.unit_id.prompt_relpath
        == PurePosixPath("project/prompts/generated_python.prompt")
    )
    assert generated.artifact_paths == (
        PurePosixPath("project/src/generated_python.prompt"),
    )


def test_unmapped_prompt_uses_protected_config_output_template(tmp_path) -> None:
    root = _repository(tmp_path)
    (root / ".pddrc").write_text(
        "version: '1.0'\n"
        "contexts:\n"
        "  python:\n"
        "    defaults:\n"
        "      prompts_dir: prompts\n"
        "      generate_output_path: src\n"
        "      outputs:\n"
        "        code:\n"
        "          path: src/{name}.py\n"
    )
    (root / "prompts/helper_python.prompt").write_text("Build helper\n")
    (root / "src/helper.py").write_text("helper = True\n")
    commit = _commit(root, "configured helper")
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    helper = next(
        unit
        for unit in manifest.managed_units
        if unit.unit_id.prompt_relpath == PurePosixPath("prompts/helper_python.prompt")
    )
    assert helper.artifact_paths == (PurePosixPath("src/helper.py"),)


def test_manifest_digest_binds_protected_config_blob_bytes(tmp_path) -> None:
    root = _repository(tmp_path)
    config = root / ".pddrc"
    config.write_text(
        "version: '1.0'\ncontexts:\n  default:\n    defaults:\n"
        "      prompts_dir: prompts\n      generate_output_path: src\n"
    )
    first_commit = _commit(root, "first config")
    first = build_unit_manifest(root, base_ref=first_commit, head_ref=first_commit)
    config.write_text(config.read_text() + "      strength: 0.5\n")
    second_commit = _commit(root, "change config bytes")
    second = build_unit_manifest(root, base_ref=second_commit, head_ref=second_commit)
    assert first.digest() != second.digest()


def test_manifest_digest_binds_language_registry_policy(tmp_path) -> None:
    root = _repository(tmp_path)
    commit = _commit(root, "base")
    first_registry = LanguageRegistry(
        (LanguageSpec("python", "Python", ("python",), (".py",), ("code",)),)
    )
    second_registry = LanguageRegistry(
        (
            LanguageSpec(
                "python", "Python", ("python",), (".py",), ("code", "test")
            ),
        )
    )
    first = build_unit_manifest(
        root, base_ref=commit, head_ref=commit, registry=first_registry
    )
    second = build_unit_manifest(
        root, base_ref=commit, head_ref=commit, registry=second_registry
    )
    assert first.digest() != second.digest()


def test_protected_human_pattern_does_not_auto_classify_new_head_path(tmp_path) -> None:
    root = _repository(tmp_path)
    policy = json.loads((root / ".pdd/sync-ownership.json").read_text())
    policy["rules"].append(
        {
            "pattern": "docs/**",
            "inventory": "HUMAN_OWNED",
            "role": "documentation",
            "owner": "docs@example.com",
        }
    )
    (root / ".pdd/sync-ownership.json").write_text(json.dumps(policy))
    (root / "docs").mkdir()
    (root / "docs/existing.md").write_text("protected human file\n")
    base = _commit(root, "human base")
    (root / "docs/new.md").write_text("candidate addition\n")
    head = _commit(root, "new file")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert PurePosixPath("docs/new.md") in manifest.unaccounted_tracked_paths


def test_absent_preauthorization_rejects_wildcard_pattern(tmp_path) -> None:
    """Future-path authorization is restricted to one exact protected path."""
    root = _repository(tmp_path)
    policy_path = root / ".pdd/sync-ownership.json"
    policy = json.loads(policy_path.read_text())
    policy["rules"].append(
        {
            "pattern": "docs/**",
            "inventory": "HUMAN_OWNED",
            "role": "documentation",
            "owner": "docs@example.com",
            "preauthorize_absent": True,
        }
    )
    policy_path.write_text(json.dumps(policy))
    commit = _commit(root, "wildcard absent preauthorization")

    with pytest.raises(ManifestError, match="overly broad or invalid"):
        build_unit_manifest(root, base_ref=commit, head_ref=commit)


def test_unmarked_absent_exact_rule_does_not_classify_new_head_path(tmp_path) -> None:
    """Dormant historical rules remain inert without explicit authorization."""
    root = _repository(tmp_path)
    policy_path = root / ".pdd/sync-ownership.json"
    policy = json.loads(policy_path.read_text())
    policy["rules"].append(
        {
            "pattern": "docs/unmarked-future.md",
            "inventory": "HUMAN_OWNED",
            "role": "documentation",
            "owner": "docs@example.com",
        }
    )
    policy_path.write_text(json.dumps(policy))
    base = _commit(root, "unmarked absent ownership rule")

    docs_path = root / "docs/unmarked-future.md"
    docs_path.parent.mkdir()
    docs_path.write_text("candidate addition\n")
    head = _commit(root, "introduce unmarked path")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    candidate = next(
        item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath
        == PurePosixPath("docs/unmarked-future.md")
    )
    assert candidate.inventory is InventoryStatus.INVALID
    assert candidate.candidate_id.role == "unaccounted"
    assert not candidate.in_base and candidate.in_head
    assert candidate.ownership_provenance == "none"
    assert PurePosixPath("docs/unmarked-future.md") in (
        manifest.unaccounted_tracked_paths
    )
