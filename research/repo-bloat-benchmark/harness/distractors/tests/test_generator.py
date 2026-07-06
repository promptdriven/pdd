"""Tests for deterministic generation, the mode cascade, and the size ladder."""

import ast
import json

import pytest

from harness.distractors.generator import (
    GenerationConfig,
    generate_ladder,
    generate_manifest,
    tier_for,
)
from harness.distractors.manifest import (
    ManifestWriter,
    load_manifest,
    verify_lockfile,
    write_lockfile,
)

CORE_MODULE = '''\
"""Pagination core for the ledger export service."""


def slice_page(items, page, page_size):
    """Return one page of ledger items."""
    start = page * page_size
    return items[start:start + page_size]


def count_pages(items, page_size):
    """Number of pages needed to export all ledger items."""
    return (len(items) + page_size - 1) // page_size
'''

CORE_TEST = '''\
from pagination import count_pages, slice_page


def test_slice_page_returns_requested_window():
    assert slice_page([1, 2, 3, 4], 1, 2) == [3, 4]


def test_count_pages_rounds_up_for_partial_pages():
    assert count_pages([1, 2, 3], 2) == 2
'''


def _pool_module(index: int) -> str:
    return (
        f'"""Ledger reporting helpers, batch {index}."""\n\n\n'
        f"def summarize_ledger_batch_{index}(entries, export_config):\n"
        f'    """Summarize one ledger export batch for reporting."""\n'
        f"    total_export_amount = sum(entry.amount for entry in entries)\n"
        f"    return {{'batch': {index}, 'total': total_export_amount}}\n"
    )


@pytest.fixture()
def scenario(tmp_path):
    core = tmp_path / "core"
    (core / "src" / "pkg").mkdir(parents=True)
    (core / "src" / "pkg" / "pagination.py").write_text(CORE_MODULE)
    (core / "src" / "pkg" / "test_pagination.py").write_text(CORE_TEST)
    pool = tmp_path / "pool"
    (pool / "src" / "pkg").mkdir(parents=True)
    (pool / "src" / "reporting").mkdir(parents=True)
    for i in range(3):
        (pool / "src" / "pkg" / f"ledger_helpers_{i}.py").write_text(_pool_module(i))
        (pool / "src" / "reporting" / f"report_builder_{i}.py").write_text(
            _pool_module(i + 100)
        )
    return tmp_path


def _config(scenario, **overrides):
    defaults = dict(
        scenario_id="pagination-demo",
        core_root=scenario / "core",
        pool_root=scenario / "pool",
        target_file="src/pkg/pagination.py",
        selection_seed=1209,
        template_file_tokens=120,
    )
    defaults.update(overrides)
    return GenerationConfig(**defaults)


def test_deterministic_same_seed_same_manifest(scenario):
    first = generate_manifest(_config(scenario), 5)
    second = generate_manifest(_config(scenario), 5)
    assert json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)


def test_different_seed_changes_selection_order(scenario):
    first = generate_manifest(_config(scenario), 5)
    second = generate_manifest(_config(scenario, selection_seed=99), 5)
    assert json.dumps(first, sort_keys=True) != json.dumps(second, sort_keys=True)


def test_budget_met_within_tolerance(scenario):
    manifest = generate_manifest(_config(scenario), 5)
    assert manifest["budget_met"]
    target = manifest["size_token_target"]
    realized = manifest["distractor_tokens_on_disk"]
    assert realized >= target * 0.98
    assert realized <= target * 1.02


def test_1x_control_has_no_distractors(scenario):
    manifest = generate_manifest(_config(scenario), 1)
    assert manifest["files"] == []
    assert manifest["distractor_tokens_on_disk"] == 0
    assert manifest["budget_met"]


def test_mode_cascade_regrow_first_then_generated(scenario):
    # Small budget: regrow alone should cover it.
    small = generate_manifest(_config(scenario), 2)
    assert small["mode_counts"]["regrow"] > 0
    # Huge budget: the tiny pool must cascade into mutate and template.
    large = generate_manifest(_config(scenario), 50)
    assert large["budget_met"]
    assert large["mode_counts"]["regrow"] > 0
    assert large["mode_counts"]["mutate"] > 0
    assert large["mode_counts"]["template"] > 0


def test_50x_scales_to_budget(scenario):
    manifest = generate_manifest(_config(scenario), 50)
    assert manifest["distractor_tokens_on_disk"] >= 49 * manifest["core_tokens"] * 0.98


def test_generated_files_parse_and_carry_no_tell(scenario):
    manifest = generate_manifest(_config(scenario), 50)
    for destination, content in manifest["generated_contents"].items():
        ast.parse(content)  # plausibility: everything materialized must parse
        assert "distractor" not in destination.lower()
        assert "distractor" not in content.lower()


def test_tiers_assigned_from_layout(scenario):
    manifest = generate_manifest(_config(scenario), 2)
    tiers = {f["upstream_path"]: f["tier"] for f in manifest["files"]}
    for path, tier in tiers.items():
        assert tier == tier_for(path, "src/pkg/pagination.py")
    assert tier_for("src/pkg/other.py", "src/pkg/pagination.py") == "same-package"
    assert tier_for("src/reporting/r.py", "src/pkg/pagination.py") == "same-layer"
    assert tier_for("docs/guide.py", "src/pkg/pagination.py") == "cross-cutting"


def test_no_destination_collides_with_core(scenario):
    manifest = generate_manifest(_config(scenario), 50)
    core_paths = {"src/pkg/pagination.py", "src/pkg/test_pagination.py"}
    destinations = {f["upstream_path"] for f in manifest["files"]}
    assert not destinations & core_paths
    assert len(destinations) == len(manifest["files"])  # unique paths


def test_ladder_generation(scenario):
    ladder = generate_ladder(_config(scenario), sizes=(1, 2, 5))
    assert set(ladder) == {1, 2, 5}
    assert ladder[1]["files"] == []
    assert ladder[5]["distractor_tokens_on_disk"] > ladder[2]["distractor_tokens_on_disk"]


def test_manifest_writer_and_lockfile(scenario, tmp_path):
    manifest = generate_manifest(_config(scenario), 5)
    writer = ManifestWriter(tmp_path / "out")
    path = writer.write(manifest)

    loaded = load_manifest(path)
    assert loaded["scenario_id"] == "pagination-demo"
    assert "generated_contents" not in loaded  # split out to content files
    for entry in loaded["files"]:
        if entry["mode"] != "regrow":
            content_file = tmp_path / "out" / entry["content_path"]
            assert content_file.is_file()

    lock = tmp_path / "out" / "manifests.lock"
    write_lockfile([path], lock)
    assert verify_lockfile(path, lock)
    # Tampering breaks the freeze.
    path.write_text(path.read_text().replace("pagination-demo", "tampered"))
    assert not verify_lockfile(path, lock)


def test_leak_denylist_blocks_content(scenario):
    # Poison every pool file with the hidden assertion; regrow must reject all.
    for pool_file in (scenario / "pool").rglob("*.py"):
        pool_file.write_text(
            pool_file.read_text()
            + "\n# expected: slice_page([1,2,3,4,5], 2, 2) == [5]\n"
        )
    config = _config(
        scenario, leak_denylist=("slice_page([1,2,3,4,5], 2, 2) == [5]",)
    )
    manifest = generate_manifest(config, 2)
    assert manifest["mode_counts"]["regrow"] == 0
    assert all(f["mode"] != "regrow" for f in manifest["files"])
    assert any(
        "condition 4" in violation
        for rejection in manifest["rejected"]
        for violation in rejection["violations"]
    )
