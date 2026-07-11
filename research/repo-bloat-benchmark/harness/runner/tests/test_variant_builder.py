"""Tests for sha-verified variant materialization."""

import pytest

from harness.distractors.generator import GenerationConfig, generate_manifest
from harness.distractors.manifest import ManifestWriter, load_manifest
from harness.runner.variant_builder import (
    VariantIntegrityError,
    materialize_variant,
    tree_sha256,
)

CORE = 'def slice_ledger_page(items, page, size):\n    """Slice one ledger export page."""\n    return items[page * size:(page + 1) * size]\n'
POOL = 'def summarize_ledger_page(page):\n    """Summarize one ledger export page."""\n    return {"entries": len(page)}\n'


@pytest.fixture()
def fixtures(tmp_path):
    core = tmp_path / "core"
    (core / "src" / "pkg").mkdir(parents=True)
    (core / "src" / "pkg" / "pagination.py").write_text(CORE)
    pool = tmp_path / "pool"
    (pool / "src" / "pkg").mkdir(parents=True)
    (pool / "src" / "pkg" / "summary.py").write_text(POOL)
    config = GenerationConfig(
        scenario_id="vb-demo",
        core_root=core,
        pool_root=pool,
        target_file="src/pkg/pagination.py",
        template_file_tokens=100,
    )
    manifest = generate_manifest(config, 5)
    writer = ManifestWriter(tmp_path / "distractors")
    manifest_path = writer.write(manifest)
    return tmp_path, core, pool, load_manifest(manifest_path)


def test_materialize_is_deterministic_and_verified(fixtures, tmp_path):
    root, core, pool, manifest = fixtures
    hash_a = materialize_variant(
        core, manifest, tmp_path / "v1", pool_root=pool,
        distractors_dir=root / "distractors",
    )
    hash_b = materialize_variant(
        core, manifest, tmp_path / "v2", pool_root=pool,
        distractors_dir=root / "distractors",
    )
    assert hash_a == hash_b
    assert (tmp_path / "v1" / "src" / "pkg" / "pagination.py").read_text() == CORE
    # Every manifest file landed at its recorded path.
    for entry in manifest["files"]:
        assert (tmp_path / "v1" / entry["upstream_path"]).is_file()


def test_sha_mismatch_aborts(fixtures, tmp_path):
    root, core, pool, manifest = fixtures
    regrow = [e for e in manifest["files"] if e["mode"] == "regrow"]
    assert regrow, "fixture should include a regrow file"
    (pool / regrow[0]["source_path"]).write_text("tampered = True\n")
    with pytest.raises(VariantIntegrityError, match="sha256 mismatch"):
        materialize_variant(
            core, manifest, tmp_path / "v3", pool_root=pool,
            distractors_dir=root / "distractors",
        )


def test_core_collision_aborts(fixtures, tmp_path):
    root, core, pool, manifest = fixtures
    manifest["files"][0]["upstream_path"] = "src/pkg/pagination.py"
    with pytest.raises(VariantIntegrityError, match="collides with core"):
        materialize_variant(
            core, manifest, tmp_path / "v4", pool_root=pool,
            distractors_dir=root / "distractors",
        )


def test_tree_hash_changes_with_content(tmp_path):
    (tmp_path / "a").mkdir()
    (tmp_path / "a" / "f.py").write_text("x = 1\n")
    (tmp_path / "b").mkdir()
    (tmp_path / "b" / "f.py").write_text("x = 2\n")
    assert tree_sha256(tmp_path / "a") != tree_sha256(tmp_path / "b")


def test_upstream_path_must_stay_under_materialized_root(fixtures, tmp_path):
    root, core, pool, manifest = fixtures
    manifest["files"][0]["upstream_path"] = "../escape.py"
    with pytest.raises(VariantIntegrityError, match="relative|contain '\\.\\.'|escapes"):
        materialize_variant(
            core, manifest, tmp_path / "v-escape", pool_root=pool,
            distractors_dir=root / "distractors",
        )


def test_regrow_source_path_must_stay_under_pool_root(fixtures, tmp_path):
    root, core, pool, manifest = fixtures
    regrow = next(entry for entry in manifest["files"] if entry["mode"] == "regrow")
    regrow["source_path"] = "../pool.py"
    with pytest.raises(VariantIntegrityError, match="relative|contain '\\.\\.'|escapes"):
        materialize_variant(
            core, manifest, tmp_path / "v-regrow-escape", pool_root=pool,
            distractors_dir=root / "distractors",
        )


def test_generated_content_path_must_stay_under_store(fixtures, tmp_path):
    root, core, pool, manifest = fixtures
    generated = next(entry for entry in manifest["files"] if entry["mode"] != "regrow")
    generated["content_path"] = "../generated.py"
    with pytest.raises(VariantIntegrityError, match="relative|contain '\\.\\.'|escapes"):
        materialize_variant(
            core, manifest, tmp_path / "v-content-escape", pool_root=pool,
            distractors_dir=root / "distractors",
        )
