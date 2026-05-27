# test_balance_chunks.py
#
# Unit tests for ci/cloud-batch/balance-chunks.py. The script lives outside
# pdd/ so we load it via importlib to avoid a dash-in-module-name import.

import importlib.util
import json
from pathlib import Path

import pytest


@pytest.fixture(scope="module")
def bc():
    repo_root = Path(__file__).resolve().parents[1]
    spec = importlib.util.spec_from_file_location(
        "balance_chunks", repo_root / "ci" / "cloud-batch" / "balance-chunks.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ── _split_unit_id ────────────────────────────────────────────────────────


def test_split_unit_id_module_level_function(bc):
    uid = bc._split_unit_id(
        "tests/test_foo.py", "tests.test_foo", "test_baz"
    )
    assert uid == "tests/test_foo.py::test_baz"


def test_split_unit_id_class_method(bc):
    uid = bc._split_unit_id(
        "tests/test_foo.py", "tests.test_foo.TestBar", "test_baz"
    )
    # Class methods collapse to the class — every method of the class
    # ends up in the same balance unit.
    assert uid == "tests/test_foo.py::TestBar"


def test_split_unit_id_nested_class(bc):
    uid = bc._split_unit_id(
        "tests/test_foo.py", "tests.test_foo.Outer.Inner", "test_baz"
    )
    assert uid == "tests/test_foo.py::Outer::Inner"


def test_split_unit_id_parametrize_brackets_stripped(bc):
    uid = bc._split_unit_id(
        "tests/test_foo.py", "tests.test_foo", "test_baz[case1]"
    )
    assert uid == "tests/test_foo.py::test_baz"


def test_split_unit_id_returns_none_on_mismatch(bc):
    # classname doesn't match expected module path -> unmappable
    assert bc._split_unit_id(
        "tests/test_foo.py", "completely.unrelated.path", "test_x"
    ) is None


# ── _build_units (splitter behaviour) ─────────────────────────────────────


def test_build_units_light_file_emits_whole(bc):
    durations = {"tests/test_light.py": 50.0}
    units = bc._build_units(
        files=["tests/test_light.py"],
        durations=durations,
        heavy_threshold=300.0,
        default_duration=10.0,
    )
    assert units == [("tests/test_light.py", 50.0)]


def test_build_units_heavy_file_with_subunits_splits(bc):
    durations = {
        "tests/test_heavy.py": 600.0,
        "tests/test_heavy.py::TestA": 250.0,
        "tests/test_heavy.py::TestB": 350.0,
    }
    units = bc._build_units(
        files=["tests/test_heavy.py"],
        durations=durations,
        heavy_threshold=300.0,
        default_duration=10.0,
    )
    unit_ids = {u[0] for u in units}
    # Whole file replaced by its per-unit entries.
    assert "tests/test_heavy.py" not in unit_ids
    assert unit_ids == {
        "tests/test_heavy.py::TestA",
        "tests/test_heavy.py::TestB",
    }


def test_build_units_heavy_file_without_subunits_emits_whole(bc):
    # File exceeds threshold but has no per-unit entries yet (e.g. first
    # run after introducing splitter, before record/seed populated them).
    durations = {"tests/test_heavy.py": 600.0}
    units = bc._build_units(
        files=["tests/test_heavy.py"],
        durations=durations,
        heavy_threshold=300.0,
        default_duration=10.0,
    )
    assert units == [("tests/test_heavy.py", 600.0)]


def test_build_units_uses_default_for_unknown_file(bc):
    units = bc._build_units(
        files=["tests/test_unknown.py"],
        durations={},
        heavy_threshold=300.0,
        default_duration=12.5,
    )
    assert units == [("tests/test_unknown.py", 12.5)]


# ── packing invariants ────────────────────────────────────────────────────


def test_greedy_pack_no_overlap_in_split_scenario(bc):
    """A heavy file's sub-units never coexist with the whole-file entry
    in the packing — pytest would otherwise re-run those tests."""
    durations = {
        "tests/test_light.py": 50.0,
        "tests/test_heavy.py": 600.0,
        "tests/test_heavy.py::TestA": 250.0,
        "tests/test_heavy.py::TestB": 350.0,
    }
    files = ["tests/test_light.py", "tests/test_heavy.py"]
    units = bc._build_units(files, durations, 300.0, 10.0)
    chunks = bc._greedy_pack_units(units, num_chunks=2)
    flat = [u for chunk in chunks for u in chunk]
    assert len(flat) == len(set(flat)), "duplicate units in packing"
    assert "tests/test_heavy.py" not in flat


# ── seed (AST-based per-class weighting) ─────────────────────────────────


def test_seed_emits_per_class_for_heavy_file(bc, tmp_path):
    test_file = tmp_path / "tests" / "test_heavy_seed.py"
    test_file.parent.mkdir(parents=True)
    test_file.write_text(
        "class TestAlpha:\n"
        "    def test_one(self): pass\n"
        "    def test_two(self): pass\n"
        "class TestBeta:\n"
        "    def test_three(self): pass\n"
        "def test_module_level(): pass\n"
    )
    durations_path = tmp_path / "test-durations.json"
    durations_path.write_text(json.dumps({"tests/test_heavy_seed.py": 400.0}))

    args = type("A", (), {
        "test_dir": "tests/",
        "durations": str(durations_path),
        "heavy_threshold": 100.0,
    })()
    # discover_test_files emits paths relative to CWD; chdir so they match
    # the keys we put in durations.
    import os
    cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        bc.cmd_seed(args)
    finally:
        os.chdir(cwd)

    out = json.loads(durations_path.read_text())
    sub_keys = {k for k in out if k.startswith("tests/test_heavy_seed.py::")}
    # 2 classes + 1 module-level test = 3 sub-units
    assert sub_keys == {
        "tests/test_heavy_seed.py::TestAlpha",
        "tests/test_heavy_seed.py::TestBeta",
        "tests/test_heavy_seed.py::test_module_level",
    }
    # Proportional: 2 methods + 1 method + 1 fn = 4 units total. Alpha gets 2/4.
    assert out["tests/test_heavy_seed.py::TestAlpha"] == pytest.approx(200.0, abs=0.5)
    assert out["tests/test_heavy_seed.py::TestBeta"] == pytest.approx(100.0, abs=0.5)
    assert out["tests/test_heavy_seed.py::test_module_level"] == pytest.approx(100.0, abs=0.5)


def test_seed_skips_files_below_threshold(bc, tmp_path):
    test_file = tmp_path / "tests" / "test_light.py"
    test_file.parent.mkdir(parents=True)
    test_file.write_text(
        "class TestX:\n    def test_a(self): pass\n"
    )
    durations_path = tmp_path / "test-durations.json"
    durations_path.write_text(json.dumps({"tests/test_light.py": 50.0}))

    args = type("A", (), {
        "test_dir": "tests/",
        "durations": str(durations_path),
        "heavy_threshold": 300.0,
    })()
    import os
    cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        bc.cmd_seed(args)
    finally:
        os.chdir(cwd)

    out = json.loads(durations_path.read_text())
    assert not any("::" in k for k in out)
