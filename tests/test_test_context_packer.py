from __future__ import annotations

import os
from pathlib import Path

import pytest

from pdd.test_context_packer import (
    OmittedTestEntry,
    SelectedTestEntry,
    TestContextPacker,
    TestPackingManifest,
    TestPackingResult,
)

"""
Test Plan for TestContextPacker:
- Ranking: relevant tests (import distance + symbol overlap) outrank unrelated ones.
- Token cap: enforce a configurable budget; over-budget candidates are omitted.
- Failing-test priority: failing tests are always packed first, before budget accounting.
- No-test fallback: empty test root returns an empty manifest without error.
- Deduplication: near-duplicate test files (high Jaccard on imported symbols) are dropped.
- Manifest content: selected/omitted entries, budget, used tokens, priority count.
- Config & edge cases: env overrides, zero/negative budget, lastfailed cache, unparseable module.
"""


def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    for key in (
        "PDD_FAILING_TESTS",
        "PDD_TEST_TOKEN_BUDGET",
        "PDD_TEST_RANKING_WEIGHTS",
        "PDD_TEST_DEDUP_THRESHOLD",
    ):
        monkeypatch.delenv(key, raising=False)
    yield


@pytest.fixture
def project(tmp_path: Path):
    """A minimal project: a module under change and a tests/ dir."""
    module = _write(
        tmp_path / "calculator.py",
        "def add(a, b):\n    return a + b\n\n\ndef subtract(a, b):\n    return a - b\n",
    )
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    return tmp_path, module, tests_dir


# --------------------------------------------------------------------- ranking
def test_ranks_relevant_tests_above_unrelated(project):
    tmp_path, module, tests_dir = project
    _write(
        tests_dir / "test_add.py",
        "from calculator import add\n\n\ndef test_add():\n    assert add(1, 2) == 3\n",
    )
    _write(
        tests_dir / "test_unrelated.py",
        "def test_unrelated():\n    assert 'x'.upper() == 'X'\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=5000)

    selected = [Path(e.file).name for e in result.manifest.selected]
    assert "test_add.py" in selected and "test_unrelated.py" in selected
    # The relevant test (import + symbol overlap) must outrank the unrelated one.
    assert selected.index("test_add.py") < selected.index("test_unrelated.py")
    by_name = {Path(e.file).name: e.score for e in result.manifest.selected}
    assert by_name["test_add.py"] > by_name["test_unrelated.py"]


def test_import_distance_signal_scores_importers_higher(project):
    tmp_path, module, tests_dir = project
    importer = _write(
        tests_dir / "test_direct.py",
        "from calculator import add, subtract\n\n\ndef test_direct():\n    assert add(2, subtract(3, 1)) == 4\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    distances = packer._build_import_graph(str(module))
    assert distances[str(importer.resolve())] == 1


# -------------------------------------------------------------------- token cap
def test_token_cap_enforced(project):
    tmp_path, module, tests_dir = project
    big_body = "\n".join(f"    assert add({i}, 1) == {i + 1}" for i in range(400))
    _write(
        tests_dir / "test_big.py",
        f"from calculator import add\n\n\ndef test_big():\n{big_body}\n",
    )
    _write(
        tests_dir / "test_small.py",
        "from calculator import subtract\n\n\ndef test_small():\n    assert subtract(2, 1) == 1\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=50)

    assert result.token_count <= 50
    assert result.manifest.used_tokens <= 50
    # At least one candidate must be omitted for budget reasons.
    assert any(e.reason == "budget exhausted" for e in result.manifest.omitted)


def test_zero_budget_returns_empty(project):
    tmp_path, module, tests_dir = project
    _write(tests_dir / "test_a.py", "def test_a():\n    assert True\n")
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=0)
    assert result.context_text == ""
    assert result.manifest.selected == []
    assert result.token_count == 0


def test_negative_budget_returns_empty(project):
    tmp_path, module, tests_dir = project
    _write(tests_dir / "test_a.py", "def test_a():\n    assert True\n")
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=-10)
    assert result.context_text == ""
    assert result.manifest.selected == []


# ---------------------------------------------------------- failing-test lane
def test_failing_tests_always_included_first(project):
    tmp_path, module, tests_dir = project
    failing_file = _write(
        tests_dir / "test_failing.py",
        "from calculator import add\n\n\ndef test_broken():\n    assert add(1, 1) == 3\n",
    )
    _write(
        tests_dir / "test_passing.py",
        "from calculator import subtract\n\n\ndef test_ok():\n    assert subtract(2, 1) == 1\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(
        module_path=str(module),
        failing_tests=[f"{failing_file}::test_broken"],
        budget_tokens=5000,
    )

    assert result.manifest.failing_test_priority_count == 1
    first = result.manifest.selected[0]
    assert Path(first.file).name == "test_failing.py"
    assert first.reason == "failing test (priority lane)"
    assert "test_broken" in first.tests


def test_failing_tests_from_env_var(project, monkeypatch):
    tmp_path, module, tests_dir = project
    failing_file = _write(
        tests_dir / "test_env.py",
        "def test_env_broken():\n    assert False\n",
    )
    monkeypatch.setenv("PDD_FAILING_TESTS", f"{failing_file}::test_env_broken")
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=5000)
    assert result.manifest.failing_test_priority_count == 1
    assert result.manifest.selected[0].reason == "failing test (priority lane)"


def test_failing_tests_from_lastfailed_cache(project):
    import json

    tmp_path, module, tests_dir = project
    failing_file = _write(
        tests_dir / "test_cached.py",
        "def test_cached_broken():\n    assert False\n",
    )
    cache_dir = tmp_path / ".pytest_cache" / "v" / "cache"
    cache_dir.mkdir(parents=True)
    (cache_dir / "lastfailed").write_text(
        json.dumps({f"{failing_file}::test_cached_broken": True}), encoding="utf-8"
    )
    cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        packer = TestContextPacker(test_root=str(tests_dir))
        result = packer.pack(module_path=str(module), budget_tokens=5000)
    finally:
        os.chdir(cwd)
    assert result.manifest.failing_test_priority_count == 1


def test_oversized_failing_file_is_sliced(project):
    tmp_path, module, tests_dir = project
    big_helper = "\n".join(f"# filler line {i}" for i in range(500))
    failing_file = _write(
        tests_dir / "test_huge.py",
        f"from calculator import add\n\n{big_helper}\n\n\ndef test_target():\n    assert add(1, 1) == 2\n\n\ndef test_other():\n    assert add(2, 2) == 4\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(
        module_path=str(module),
        failing_tests=[f"{failing_file}::test_target"],
        budget_tokens=40,
    )
    # The failing test is still present even though the full file exceeded budget.
    assert "test_target" in result.context_text
    # Slicing dropped the unrelated filler / sibling test.
    assert "test_other" not in result.context_text


# -------------------------------------------------------------- no-test fallback
def test_no_test_files_returns_empty_manifest(tmp_path):
    module = _write(tmp_path / "calculator.py", "def add(a, b):\n    return a + b\n")
    empty_tests = tmp_path / "tests"
    empty_tests.mkdir()
    packer = TestContextPacker(test_root=str(empty_tests))
    result = packer.pack(module_path=str(module), budget_tokens=2000)
    assert result.context_text == ""
    assert result.manifest.selected == []
    assert result.manifest.unavailability_reason == "no test files found"


def test_missing_test_root_returns_empty(tmp_path):
    module = _write(tmp_path / "calculator.py", "def add(a, b):\n    return a + b\n")
    packer = TestContextPacker(test_root=str(tmp_path / "does_not_exist"))
    result = packer.pack(module_path=str(module), budget_tokens=2000)
    assert result.manifest.selected == []
    assert result.manifest.unavailability_reason == "no test files found"


# ------------------------------------------------------------- deduplication
def test_near_duplicate_files_are_deduplicated(project):
    tmp_path, module, tests_dir = project
    body = "from calculator import add, subtract\n\n\ndef {name}():\n    assert add(1, 1) == 2\n    assert subtract(2, 1) == 1\n"
    _write(tests_dir / "test_unit.py", body.format(name="test_unit"))
    _write(tests_dir / "test_integration.py", body.format(name="test_integration"))
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=5000)

    selected = [Path(e.file).name for e in result.manifest.selected]
    omitted = [e for e in result.manifest.omitted]
    # The two files import the identical symbol set -> Jaccard 1.0 -> one omitted.
    assert len(selected) == 1
    assert len(omitted) == 1
    assert omitted[0].reason.startswith("near-duplicate of ")


def test_dedup_threshold_env_override_keeps_both(project, monkeypatch):
    tmp_path, module, tests_dir = project
    _write(
        tests_dir / "test_a.py",
        "from calculator import add, subtract\n\n\ndef test_a():\n    assert add(1, 1) == 2\n",
    )
    _write(
        tests_dir / "test_b.py",
        "from calculator import add, subtract\n\n\ndef test_b():\n    assert subtract(2, 1) == 1\n",
    )
    # Threshold above 1.0 disables deduplication.
    monkeypatch.setenv("PDD_TEST_DEDUP_THRESHOLD", "1.5")
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=5000)
    assert len([e for e in result.manifest.selected]) == 2


# ---------------------------------------------------------------- manifest
def test_manifest_records_budget_and_usage(project):
    tmp_path, module, tests_dir = project
    _write(
        tests_dir / "test_x.py",
        "from calculator import add\n\n\ndef test_x():\n    assert add(1, 1) == 2\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=1234)
    assert isinstance(result, TestPackingResult)
    assert isinstance(result.manifest, TestPackingManifest)
    assert result.manifest.budget_tokens == 1234
    assert result.manifest.used_tokens == result.token_count
    assert result.manifest.unavailability_reason is None
    assert all(isinstance(e, SelectedTestEntry) for e in result.manifest.selected)
    assert result.manifest.selected[0].token_count > 0


def test_context_text_contains_selected_content(project):
    tmp_path, module, tests_dir = project
    _write(
        tests_dir / "test_marker.py",
        "from calculator import add\n\n\ndef test_unique_marker():\n    assert add(1, 1) == 2\n",
    )
    packer = TestContextPacker(test_root=str(tests_dir))
    result = packer.pack(module_path=str(module), budget_tokens=5000)
    assert "test_unique_marker" in result.context_text
    assert "test_marker.py" in result.context_text  # file header


# ------------------------------------------------------------- configuration
def test_env_token_budget_used_when_not_overridden(project, monkeypatch):
    tmp_path, module, tests_dir = project
    _write(tests_dir / "test_a.py", "def test_a():\n    assert True\n")
    monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "777")
    packer = TestContextPacker(test_root=str(tests_dir))
    assert packer.budget_tokens == 777
    result = packer.pack(module_path=str(module))
    assert result.manifest.budget_tokens == 777


def test_ranking_weights_env_override(monkeypatch):
    monkeypatch.setenv(
        "PDD_TEST_RANKING_WEIGHTS",
        '{"import_distance":0.7,"symbol_overlap":0.1,"failure_recency":0.1,"file_recency":0.1}',
    )
    packer = TestContextPacker(test_root="tests")
    assert packer.weights["import_distance"] == 0.7


def test_unparseable_module_falls_back_to_recency(project):
    tmp_path, _module, tests_dir = project
    broken = _write(tmp_path / "broken.py", "def add(a, b)\n    return a + b\n")  # syntax error
    _write(tests_dir / "test_a.py", "def test_a():\n    assert True\n")
    _write(tests_dir / "test_b.py", "def test_b():\n    assert True\n")
    packer = TestContextPacker(test_root=str(tests_dir))
    # Must not raise; recency-only ranking still selects tests.
    result = packer.pack(module_path=str(broken), budget_tokens=5000)
    assert len(result.manifest.selected) == 2
