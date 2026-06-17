"""Tests for TestContextPacker (PR #1524 / closes #793).

Independently generated acceptance suite for issue #793 ("Context optimization:
select relevant tests under a token budget"). These tests exercise the module's
*intended behaviors* through its real, spec'd public API:

    TestContextPacker(test_root: str | None = None)
        .pack(module_path: str,
              failing_tests: list[str] | None = None,
              budget_tokens: int | None = None) -> TestPackingResult

(prompt spec requirement #2 + <pdd-interface>; the same contract used by the
two production call sites in fix_error_loop.py and compressed_sync_context.py).

The packer *discovers* candidate test files under ``test_root`` and sources
failing-test history from the ``failing_tests`` argument, the
``PDD_FAILING_TESTS`` env var, or ``.pytest_cache/v/cache/lastfailed`` — so the
tests below write candidate files into a ``tests/`` dir rather than injecting a
candidate list. Result shape (spec req #1): ``TestPackingResult`` exposes
``context_text``, ``token_count`` and ``manifest``; the ``TestPackingManifest``
exposes ``selected`` / ``omitted`` lists of ``SelectedTestEntry`` /
``OmittedTestEntry`` (``file``, ``score``, ``reason``, ...), plus
``budget_tokens``, ``used_tokens`` and ``failing_test_priority_count``.

Run the full suite with:
    pytest -vv tests/test_test_context_packer.py tests/test_compressed_sync_context.py
"""
from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.test_context_packer import TestContextPacker

_needs_packer = pytest.mark.skipif(False, reason="TestContextPacker is included in this PR")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_test_file(
    path: Path,
    symbols: list[str] | None = None,
    extra_chars: int = 0,
    header: str = "",
) -> Path:
    """Write a minimal pytest-compatible test file at *path*.

    Args:
        path: Destination path (parent directory is created if missing).
        symbols: Test-function names to define. Defaults to one function
            named after the file stem.
        extra_chars: Pad the file with roughly this many trailing comment
            characters of *varied* deterministic text, so the token estimate
            scales ~linearly with size under any tokenizer (a run of identical
            characters would BPE-merge and undercount).
        header: Optional leading lines (e.g. an ``import`` statement) used to
            give the file an import-graph / symbol-overlap relationship with
            the module under change.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    syms = symbols or [f"test_{path.stem}"]
    body = "\n\n".join(f"def {s}():\n    assert True" for s in syms)
    content = (header + "\n" if header else "") + body + "\n"
    if extra_chars:
        # Deterministic, low-compressibility filler (distinct words) so that
        # token_count tracks character count instead of collapsing to a few
        # merged tokens. ~7 chars per word → enough words to reach extra_chars.
        words = [f"pad{i % 131:03d}" for i in range((extra_chars // 7) + 1)]
        content += "# " + " ".join(words) + "\n"
    path.write_text(content, encoding="utf-8")
    return path


def _selected_files(result) -> list[str]:
    """Ordered list of selected file paths (manifest.selected preserves rank)."""
    return [entry.file for entry in result.manifest.selected]


def _omitted_files(result) -> list[str]:
    return [entry.file for entry in result.manifest.omitted]


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    """Isolate every test from ambient packer configuration."""
    for key in (
        "PDD_FAILING_TESTS",
        "PDD_TEST_TOKEN_BUDGET",
        "PDD_TEST_RANKING_WEIGHTS",
        "PDD_TEST_DEDUP_THRESHOLD",
    ):
        monkeypatch.delenv(key, raising=False)
    yield


# ===========================================================================
# Scenario 1: Determinism
# ===========================================================================


@_needs_packer
class TestDeterminism:
    """pack() must produce the same ranked selection for identical inputs."""

    def test_same_inputs_produce_identical_selection_order(self, tmp_path: Path) -> None:
        """Two separate packer instances with identical inputs return the same ranked list."""
        tests_dir = tmp_path / "tests"
        for i in range(5):
            _write_test_file(tests_dir / f"test_module_{i}.py")
        failing = [str(tests_dir / "test_module_0.py"), str(tests_dir / "test_module_1.py")]

        r1 = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=failing, budget_tokens=50_000
        )
        r2 = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=failing, budget_tokens=50_000
        )

        assert _selected_files(r1) == _selected_files(r2), (
            "pack() must be deterministic: identical inputs must always produce the "
            "same ranked selection"
        )

    def test_repeated_pack_calls_on_same_instance_are_identical(self, tmp_path: Path) -> None:
        """Calling .pack() twice on the same packer instance returns identical rankings."""
        tests_dir = tmp_path / "tests"
        for c in ("a", "b", "c"):
            _write_test_file(tests_dir / f"test_{c}.py")
        packer = TestContextPacker(test_root=str(tests_dir))

        r1 = packer.pack(module_path="", failing_tests=[str(tests_dir / "test_a.py")], budget_tokens=50_000)
        r2 = packer.pack(module_path="", failing_tests=[str(tests_dir / "test_a.py")], budget_tokens=50_000)

        assert _selected_files(r1) == _selected_files(r2), (
            "Repeated .pack() calls on the same instance must return identical results"
        )


# ===========================================================================
# Scenario 2: Priority-0 lane — failing tests always included
# ===========================================================================


@_needs_packer
class TestPriorityZeroLane:
    """Failing tests are packed first (priority-0), before budget accounting.

    Note: spec req #10 makes ``budget_tokens <= 0`` an explicit "no test
    context at all" sentinel that returns an empty manifest — so the
    priority-0 guarantee is asserted with a small *positive* budget, the
    regime in which it actually applies (fix flows always use the configured
    positive cap, default 2000).
    """

    def test_failing_test_included_when_budget_too_small_for_it(self, tmp_path: Path) -> None:
        """A failing test is packed unconditionally even when it alone exceeds the budget."""
        tests_dir = tmp_path / "tests"
        # Failing file is large enough to exceed the tiny budget on its own.
        failing_file = _write_test_file(tests_dir / "test_fails.py", extra_chars=4_000)
        _write_test_file(tests_dir / "test_passes.py")

        # Use a full "<file>::<test>" id — the realistic fix-flow input. (A bare
        # path still packs the file in the priority lane, but the manifest's
        # failing_test_priority_count counts named failing *functions*, so it
        # would report 0 for a path-only entry.)
        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="",
            failing_tests=[f"{failing_file}::test_test_fails"],
            budget_tokens=10,  # far smaller than the failing file
        )

        assert str(failing_file) in _selected_files(result), (
            "Failing test must be packed in the priority-0 lane even when it exceeds the budget"
        )
        assert result.manifest.failing_test_priority_count >= 1

    def test_failing_tests_appear_before_non_failing_in_selection(
        self, tmp_path: Path
    ) -> None:
        """Failing tests occupy earlier positions in the selection than non-failing tests."""
        tests_dir = tmp_path / "tests"
        passing_file = _write_test_file(tests_dir / "test_passes.py")
        failing_file = _write_test_file(tests_dir / "test_fails.py")

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="",
            failing_tests=[str(failing_file)],
            budget_tokens=50_000,
        )

        selected = _selected_files(result)
        assert str(failing_file) in selected, "Failing file must be selected"
        assert str(passing_file) in selected, "Passing file must be selected when budget allows"
        assert selected.index(str(failing_file)) < selected.index(str(passing_file)), (
            "Failing test (priority-0) must appear before the non-failing test in the selection"
        )

    def test_all_failing_tests_included_even_when_budget_too_small_for_passers(
        self, tmp_path: Path
    ) -> None:
        """Every failing test is packed even when budget is insufficient for non-failing files."""
        tests_dir = tmp_path / "tests"
        f1 = _write_test_file(tests_dir / "test_fail_a.py")
        f2 = _write_test_file(tests_dir / "test_fail_b.py")
        # Non-failing file is intentionally huge to exceed the budget.
        huge_passer = _write_test_file(tests_dir / "test_pass_huge.py", extra_chars=12_000)

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="",
            failing_tests=[str(f1), str(f2)],
            budget_tokens=500,  # fits the small failing files but not the huge passer
        )

        selected = _selected_files(result)
        assert str(f1) in selected, "First failing file must be packed (priority-0)"
        assert str(f2) in selected, "Second failing file must be packed (priority-0)"
        assert str(huge_passer) not in selected, (
            "Huge non-failing file must be omitted when budget is exhausted"
        )


# ===========================================================================
# Scenario 3: Budget enforcement for non-failing tests
# ===========================================================================


@_needs_packer
class TestBudgetEnforcement:
    """Non-failing tests are packed greedily until the token budget is reached."""

    def test_selected_tokens_do_not_exceed_budget(self, tmp_path: Path) -> None:
        """Total token count across all (non-failing) selected files must not exceed budget."""
        tests_dir = tmp_path / "tests"
        for i in range(10):
            _write_test_file(tests_dir / f"test_item_{i}.py", extra_chars=396)
        budget = 500

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=budget
        )

        assert result.token_count <= budget, (
            f"token_count={result.token_count} must not exceed budget={budget}"
        )
        assert result.manifest.used_tokens <= budget

    def test_candidate_exceeding_remaining_budget_is_omitted(self, tmp_path: Path) -> None:
        """A non-failing candidate whose tokens would exceed remaining budget is skipped."""
        tests_dir = tmp_path / "tests"
        small = _write_test_file(tests_dir / "test_small.py")
        huge = _write_test_file(tests_dir / "test_huge.py", extra_chars=6_000)

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=500
        )

        selected = _selected_files(result)
        assert str(small) in selected, "Small file must be selected (fits in budget)"
        assert str(huge) not in selected, (
            "Huge file must be omitted because it exceeds the remaining budget"
        )

    def test_empty_candidates_returns_empty_selection_without_error(
        self, tmp_path: Path
    ) -> None:
        """An empty test root returns an empty selection without raising."""
        empty_tests = tmp_path / "tests"
        empty_tests.mkdir()
        result = TestContextPacker(test_root=str(empty_tests)).pack(
            module_path="", failing_tests=[], budget_tokens=50_000
        )

        assert result.manifest.selected == [], "Empty test root must produce an empty selection"

    def test_zero_budget_returns_empty_manifest(self, tmp_path: Path) -> None:
        """budget_tokens <= 0 is the 'no test context' sentinel (spec req #10)."""
        tests_dir = tmp_path / "tests"
        _write_test_file(tests_dir / "test_a.py")
        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[str(tests_dir / "test_a.py")], budget_tokens=0
        )
        assert result.manifest.selected == []
        assert result.token_count == 0


# ===========================================================================
# Scenario 4: TestPackingManifest — selection entries
# ===========================================================================


@_needs_packer
class TestPackingManifestSelectionEntries:
    """Every selected file must have an explanatory manifest entry (spec req #1)."""

    def test_every_selected_file_has_a_manifest_entry(self, tmp_path: Path) -> None:
        """The selection list and the manifest.selected entries describe the same files."""
        tests_dir = tmp_path / "tests"
        _write_test_file(tests_dir / "test_alpha.py")
        _write_test_file(tests_dir / "test_beta.py")

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=50_000
        )

        files = {e.file for e in result.manifest.selected}
        assert files, "Expected at least one selected manifest entry"
        # Each selected entry is distinct and corresponds to a real packed file.
        assert len(files) == len(result.manifest.selected), (
            "Each selected file must have exactly one manifest entry"
        )

    def test_manifest_selection_entries_explain_the_decision(self, tmp_path: Path) -> None:
        """Each selection entry exposes a numeric score and a non-empty reason.

        (Spec req #1 defines SelectedTestEntry as file/tests/token_count/score/reason.
        The four scoring signals themselves are validated by their *ranking effects*
        in Scenario 9, which is the observable contract — the manifest's job is to
        explain selection, which it does via score + reason.)
        """
        tests_dir = tmp_path / "tests"
        _write_test_file(tests_dir / "test_signal_check.py")
        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=50_000
        )

        selected_entries = result.manifest.selected
        assert selected_entries, "Expected at least one selected manifest entry"
        for entry in selected_entries:
            assert isinstance(entry.score, (int, float)), "entry.score must be numeric"
            assert entry.reason, f"Selection reason must be non-empty for {entry.file!r}"
            assert entry.token_count > 0, "Selected entry must record its token cost"


# ===========================================================================
# Scenario 5: TestPackingManifest — omission entries
# ===========================================================================


@_needs_packer
class TestPackingManifestOmissionEntries:
    """Every omitted file must have a manifest entry with a reason (spec req #1)."""

    def test_omitted_file_appears_in_manifest(self, tmp_path: Path) -> None:
        """A file excluded because it exceeds the budget has a manifest omission entry."""
        tests_dir = tmp_path / "tests"
        _write_test_file(tests_dir / "test_small.py")
        huge = _write_test_file(tests_dir / "test_huge.py", extra_chars=6_000)

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=500
        )

        assert any(str(huge) == f for f in _omitted_files(result)), (
            "Omitted file must appear in the manifest.omitted list"
        )

    def test_omission_manifest_entries_include_non_empty_reason(
        self, tmp_path: Path
    ) -> None:
        """Each omission entry carries a human-readable reason string."""
        tests_dir = tmp_path / "tests"
        _write_test_file(tests_dir / "test_small.py")
        _write_test_file(tests_dir / "test_huge.py", extra_chars=6_000)

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=500
        )

        omitted_entries = result.manifest.omitted
        assert omitted_entries, "Expected at least one omission manifest entry"
        for entry in omitted_entries:
            assert entry.reason, f"Omission reason must be non-empty; got: {entry.reason!r}"


# ===========================================================================
# Scenario 6: AdaGReS-style marginal redundancy penalty
# ===========================================================================


@_needs_packer
class TestAdaGrESRedundancyPenalty:
    """A candidate that highly overlaps an already-selected file yields its slot
    (AdaGReS-style marginal-gain penalty / cross-file dedup on imported symbols)."""

    def test_novel_file_selected_over_highly_redundant_file(self, tmp_path: Path) -> None:
        """A file duplicating an anchor's imported symbols is dropped as a near-duplicate,
        while a file importing novel symbols is selected."""
        module = tmp_path / "calculator.py"
        module.write_text(
            "def add(a, b):\n    return a + b\n\n\n"
            "def subtract(a, b):\n    return a - b\n\n\n"
            "def multiply(a, b):\n    return a * b\n\n\n"
            "def divide(a, b):\n    return a / b\n",
            encoding="utf-8",
        )
        tests_dir = tmp_path / "tests"
        # anchor: failing → priority-0; imports add+subtract.
        anchor = _write_test_file(
            tests_dir / "test_anchor.py",
            header="from calculator import add, subtract",
        )
        # redundant: imports the *same* symbols as the anchor → Jaccard 1.0 → near-duplicate.
        redundant = _write_test_file(
            tests_dir / "test_redundant.py",
            header="from calculator import add, subtract",
        )
        # novel: imports entirely different symbols → no overlap with anchor.
        novel = _write_test_file(
            tests_dir / "test_novel.py",
            header="from calculator import multiply, divide",
        )

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path=str(module),
            failing_tests=[str(anchor)],  # anchor in priority-0; novel vs redundant compete
            budget_tokens=50_000,
        )

        selected = _selected_files(result)
        assert str(novel) in selected, (
            "Novel file (unique imported symbols) must be selected over the redundant one"
        )
        assert str(redundant) not in selected, (
            "Redundant file (duplicate of the anchor's symbols) must be dropped"
        )
        # And it must be recorded as a near-duplicate omission, not silently lost.
        assert any(
            e.file == str(redundant) and "near-duplicate" in e.reason
            for e in result.manifest.omitted
        ), "Redundant file must be omitted with a 'near-duplicate' reason"


# ===========================================================================
# Scenario 7: Cross-file deduplication
# ===========================================================================


@_needs_packer
class TestCrossFileDeduplication:
    """Near-duplicate test files (high Jaccard on imported symbols) are charged once."""

    def test_each_path_appears_at_most_once(self, tmp_path: Path) -> None:
        """No selected path appears more than once (discovery + dedup guarantee)."""
        tests_dir = tmp_path / "tests"
        f = _write_test_file(tests_dir / "test_dup.py")

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=50_000
        )

        selected = _selected_files(result)
        assert selected.count(str(f)) <= 1, (
            f"A path must appear at most once in the selection; got {selected.count(str(f))}"
        )

    def test_near_duplicate_content_counted_only_once(self, tmp_path: Path) -> None:
        """Two files importing the same module symbols dedup to a single selection."""
        module = tmp_path / "widget.py"
        module.write_text(
            "def create():\n    ...\n\n\ndef destroy():\n    ...\n", encoding="utf-8"
        )
        tests_dir = tmp_path / "tests"
        a = _write_test_file(tests_dir / "test_a.py", header="from widget import create, destroy")
        b = _write_test_file(tests_dir / "test_b.py", header="from widget import create, destroy")

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path=str(module), failing_tests=[], budget_tokens=50_000
        )

        selected = _selected_files(result)
        # Exactly one of the two identical-symbol files survives; the other is a near-duplicate.
        assert len({str(a), str(b)} & set(selected)) == 1, (
            "Near-duplicate files (identical imported symbols) must dedup to one selection"
        )


# ===========================================================================
# Scenario 8: PDD_TEST_TOKEN_BUDGET env var
# ===========================================================================


@_needs_packer
class TestPddTestTokenBudgetEnvVar:
    """PDD_TEST_TOKEN_BUDGET sets the default budget (read at instantiation)."""

    def test_small_env_budget_selects_fewer_files(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """A small PDD_TEST_TOKEN_BUDGET restricts the number of selected files."""
        tests_dir = tmp_path / "tests"
        for i in range(10):
            _write_test_file(tests_dir / f"test_env_{i}.py", extra_chars=400)

        # Env var is read in __init__, so construct the packer *after* setting it.
        monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "200")
        result_small = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[]
        )

        monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "10000000")
        result_large = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[]
        )

        assert len(result_small.manifest.selected) < len(result_large.manifest.selected), (
            "Smaller PDD_TEST_TOKEN_BUDGET must select strictly fewer files here"
        )

    def test_explicit_budget_kwarg_overrides_env_var(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """An explicit budget_tokens= argument takes precedence over the env var."""
        tests_dir = tmp_path / "tests"
        for i in range(5):
            _write_test_file(tests_dir / f"test_kwarg_{i}.py")

        monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "1")  # near-zero env budget
        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=10_000_000
        )

        assert len(result.manifest.selected) > 0, (
            "Explicit budget_tokens= must override the near-zero PDD_TEST_TOKEN_BUDGET env var"
        )


# ===========================================================================
# Scenario 9: Four scoring signals affect ranking
# ===========================================================================


@_needs_packer
class TestFourScoringSignals:
    """Each of the four scoring signals must influence ranking in the expected direction."""

    def test_import_graph_distance_closer_file_ranks_higher(
        self, tmp_path: Path
    ) -> None:
        """A test file that imports the target module (distance=1) ranks above an
        unrelated file (distance=inf)."""
        target = tmp_path / "my_module.py"
        target.write_text("def compute():\n    return 42\n", encoding="utf-8")

        tests_dir = tmp_path / "tests"
        close = _write_test_file(
            tests_dir / "test_close.py", header="from my_module import compute"
        )
        distant = _write_test_file(tests_dir / "test_distant.py")

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path=str(target), failing_tests=[], budget_tokens=50_000
        )

        selected = _selected_files(result)
        assert str(close) in selected, "Closer importing file must be selected"
        assert str(distant) in selected, "Distant file must be selected when budget allows"
        assert selected.index(str(close)) < selected.index(str(distant)), (
            "File with smaller import-graph distance must rank higher in selection"
        )

    def test_symbol_reference_overlap_higher_overlap_ranks_higher(
        self, tmp_path: Path
    ) -> None:
        """Among files at equal import distance, the one referencing more of the
        module's exported symbols ranks higher."""
        target = tmp_path / "widget.py"
        target.write_text(
            "def create_widget():\n    ...\n\n\n"
            "def destroy_widget():\n    ...\n\n\n"
            "def resize_widget():\n    ...\n",
            encoding="utf-8",
        )
        tests_dir = tmp_path / "tests"
        # Both import widget (equal import distance); high references all 3 symbols.
        tests_dir.mkdir(parents=True, exist_ok=True)
        high_overlap = tests_dir / "test_widget_full.py"
        high_overlap.write_text(
            "from widget import create_widget, destroy_widget, resize_widget\n\n"
            "def test_all():\n"
            "    create_widget()\n"
            "    destroy_widget()\n"
            "    resize_widget()\n",
            encoding="utf-8",
        )
        low_overlap = tests_dir / "test_widget_one.py"
        low_overlap.write_text(
            "from widget import create_widget\n\n"
            "def test_one():\n"
            "    create_widget()\n",
            encoding="utf-8",
        )

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path=str(target), failing_tests=[], budget_tokens=50_000
        )

        selected = _selected_files(result)
        assert str(high_overlap) in selected, "Higher-overlap file must be selected"
        assert str(low_overlap) in selected, "Lower-overlap file must be selected when budget allows"
        assert selected.index(str(high_overlap)) < selected.index(str(low_overlap)), (
            "Higher symbol-reference overlap with the target must produce a higher rank"
        )

    def test_failure_history_signal_prioritizes_failing_test_from_env(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """The failure signal is sourced from PDD_FAILING_TESTS (spec req #4): a test
        named there is treated as failing and always packed first.

        (The spec sources failure history from PDD_FAILING_TESTS / .pytest_cache —
        neither stores per-failure timestamps, so the signal is failed-vs-not, not a
        time gradient; its observable effect is priority placement, asserted here.)
        """
        tests_dir = tmp_path / "tests"
        failed = _write_test_file(tests_dir / "test_flaky.py")
        _write_test_file(tests_dir / "test_stable.py")

        monkeypatch.setenv("PDD_FAILING_TESTS", f"{failed}::test_test_flaky")
        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=None, budget_tokens=50_000
        )

        selected = _selected_files(result)
        assert str(failed) in selected, "A PDD_FAILING_TESTS entry must be selected"
        assert selected[0] == str(failed), (
            "A failing test sourced from PDD_FAILING_TESTS must be packed first (priority-0)"
        )
        assert result.manifest.failing_test_priority_count >= 1

    def test_modification_recency_newer_file_ranks_higher(self, tmp_path: Path) -> None:
        """With no module to rank against (recency-only fallback), a newer file
        ranks above one whose mtime is the Unix epoch."""
        tests_dir = tmp_path / "tests"
        newer = _write_test_file(tests_dir / "test_newer.py")
        older = _write_test_file(tests_dir / "test_older.py")
        os.utime(older, (0, 0))  # force older's mtime to epoch 0

        result = TestContextPacker(test_root=str(tests_dir)).pack(
            module_path="", failing_tests=[], budget_tokens=50_000
        )

        selected = _selected_files(result)
        assert str(newer) in selected, "Newer file must be selected"
        assert str(older) in selected, "Older file must be selected when budget allows"
        assert selected.index(str(newer)) < selected.index(str(older)), (
            "More recently modified file must rank higher than one last touched at epoch 0"
        )


# ===========================================================================
# Scenario 10: _test_context_compression_active() env var wiring
# (Always runs — targets existing code in pdd/pytest_output.py)
# ===========================================================================


class TestContextCompressionEnvVarWiring:
    """_test_context_compression_active() reads compression env vars correctly."""

    def test_pdd_compress_test_context_one_activates_compression(
        self, monkeypatch
    ) -> None:
        """PDD_COMPRESS_TEST_CONTEXT=1 → _test_context_compression_active() is True."""
        from pdd.pytest_output import _test_context_compression_active

        monkeypatch.setenv("PDD_COMPRESS_TEST_CONTEXT", "1")
        monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)

        assert _test_context_compression_active() is True

    def test_pdd_context_compression_test_mode_activates(self, monkeypatch) -> None:
        """PDD_CONTEXT_COMPRESSION=test → _test_context_compression_active() is True."""
        from pdd.pytest_output import _test_context_compression_active

        monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)
        monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "test")

        assert _test_context_compression_active() is True

    def test_pdd_context_compression_all_mode_activates(self, monkeypatch) -> None:
        """PDD_CONTEXT_COMPRESSION=all → _test_context_compression_active() is True."""
        from pdd.pytest_output import _test_context_compression_active

        monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)
        monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "all")

        assert _test_context_compression_active() is True

    def test_pdd_context_compression_off_does_not_activate(self, monkeypatch) -> None:
        """PDD_CONTEXT_COMPRESSION=off → _test_context_compression_active() is False."""
        from pdd.pytest_output import _test_context_compression_active

        monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)
        monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "off")

        assert _test_context_compression_active() is False

    def test_no_env_vars_returns_false(self, monkeypatch) -> None:
        """Without any compression env vars, _test_context_compression_active() is False."""
        from pdd.pytest_output import _test_context_compression_active

        monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)
        monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)

        assert _test_context_compression_active() is False


# ===========================================================================
# Scenario 11: fix_error_loop context_compression parameter wiring
# (Always runs — targets existing code in pdd/fix_error_loop.py)
# ===========================================================================


class TestFixErrorLoopContextCompressionWiring:
    """fix_error_loop() forwards context_compression to apply_compression_env correctly."""

    def test_context_compression_test_calls_apply_compression_env(
        self, tmp_path: Path
    ) -> None:
        """fix_error_loop(context_compression='test') calls
        apply_compression_env({'context_compression': 'test'})."""
        from pdd.fix_error_loop import fix_error_loop

        with patch("pdd.fix_error_loop.apply_compression_env") as mock_apply:
            fix_error_loop(
                unit_test_file=str(tmp_path / "nonexistent_test.py"),
                code_file=str(tmp_path / "nonexistent_code.py"),
                prompt_file=str(tmp_path / "prompt.txt"),
                prompt="test prompt",
                verification_program="pytest",
                strength=0.5,
                temperature=0.0,
                max_attempts=1,
                budget=1.0,
                context_compression="test",
            )

        mock_apply.assert_called_once_with({"context_compression": "test"})

    def test_context_compression_all_calls_apply_compression_env(
        self, tmp_path: Path
    ) -> None:
        """fix_error_loop(context_compression='all') calls
        apply_compression_env({'context_compression': 'all'})."""
        from pdd.fix_error_loop import fix_error_loop

        with patch("pdd.fix_error_loop.apply_compression_env") as mock_apply:
            fix_error_loop(
                unit_test_file=str(tmp_path / "nonexistent_test.py"),
                code_file=str(tmp_path / "nonexistent_code.py"),
                prompt_file=str(tmp_path / "prompt.txt"),
                prompt="test prompt",
                verification_program="pytest",
                strength=0.5,
                temperature=0.0,
                max_attempts=1,
                budget=1.0,
                context_compression="all",
            )

        mock_apply.assert_called_once_with({"context_compression": "all"})
