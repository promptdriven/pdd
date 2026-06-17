"""Tests for TestContextPacker (PR #1524 / closes #793).

Written TDD-style — packer tests are skipped gracefully until
pdd/test_context_packer.py is merged from PR #1524.  Tests for
_test_context_compression_active() and the fix_error_loop
context_compression parameter are always runnable because they target
existing code in pdd/pytest_output.py and pdd/fix_error_loop.py.

Run the full suite with:
    pytest -vv tests/test_test_context_packer.py tests/test_compressed_sync_context.py
"""
from __future__ import annotations

import os
import time as time_module
from pathlib import Path
from unittest.mock import patch

import pytest

# ---------------------------------------------------------------------------
# Conditional import — packer tests skip until PR #1524 lands
# ---------------------------------------------------------------------------
try:
    from pdd.test_context_packer import TestContextPacker, TestPackingManifest

    _PACKER_AVAILABLE = True
except ImportError:
    _PACKER_AVAILABLE = False
    TestContextPacker = None  # type: ignore[assignment,misc]
    TestPackingManifest = None  # type: ignore[assignment,misc]

_needs_packer = pytest.mark.skipif(
    not _PACKER_AVAILABLE,
    reason=(
        "pdd.test_context_packer not yet on main — waiting for PR #1524. "
        "These tests will run automatically once the module is merged."
    ),
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_test_file(
    path: Path,
    symbols: list[str] | None = None,
    extra_chars: int = 0,
) -> Path:
    """Write a minimal pytest-compatible test file at *path*.

    Args:
        path: Destination path (parent directory is created if missing).
        symbols: Function names to define. Defaults to one function named
            after the file stem.
        extra_chars: Pad the file by appending this many 'x' characters so
            that its character count (and thus token estimate) is predictable.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    syms = symbols or [f"test_{path.stem}"]
    body = "\n\n".join(f"def {s}():\n    assert True" for s in syms)
    content = body + "\n" + ("x" * extra_chars)
    path.write_text(content, encoding="utf-8")
    return path


# ===========================================================================
# Scenario 1: Determinism
# ===========================================================================


@_needs_packer
class TestDeterminism:
    """pack() must produce the same ranked selection for identical inputs."""

    def test_same_inputs_produce_identical_selection_order(self, tmp_path: Path) -> None:
        """Two separate packer instances with identical inputs return the same ranked list."""
        candidates = [
            _write_test_file(tmp_path / f"test_module_{i}.py")
            for i in range(5)
        ]
        failing = candidates[:2]

        r1 = TestContextPacker(candidates=candidates, failing=failing, budget=50_000).pack()
        r2 = TestContextPacker(candidates=candidates, failing=failing, budget=50_000).pack()

        assert [str(p) for p in r1.selected] == [str(p) for p in r2.selected], (
            "pack() must be deterministic: identical inputs must always produce the "
            "same ranked selection"
        )

    def test_repeated_pack_calls_on_same_instance_are_identical(self, tmp_path: Path) -> None:
        """Calling .pack() twice on the same packer instance returns identical rankings."""
        candidates = [_write_test_file(tmp_path / f"test_{c}.py") for c in ("a", "b", "c")]
        packer = TestContextPacker(
            candidates=candidates, failing=[candidates[0]], budget=50_000
        )

        r1 = packer.pack()
        r2 = packer.pack()

        assert [str(p) for p in r1.selected] == [str(p) for p in r2.selected], (
            "Repeated .pack() calls on the same instance must return identical results"
        )


# ===========================================================================
# Scenario 2: Priority-0 lane — failing tests always included
# ===========================================================================


@_needs_packer
class TestPriorityZeroLane:
    """Failing tests are packed first (priority-0) regardless of token budget."""

    def test_failing_test_included_when_budget_is_zero(self, tmp_path: Path) -> None:
        """A failing test is packed even when budget=0 (priority-0 overrides budget)."""
        failing_file = _write_test_file(tmp_path / "test_fails.py")
        passing_file = _write_test_file(tmp_path / "test_passes.py")

        result = TestContextPacker(
            candidates=[failing_file, passing_file],
            failing=[failing_file],
            budget=0,
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        assert str(failing_file) in selected_strs, (
            "Failing test must appear in the priority-0 lane even when budget=0"
        )

    def test_failing_tests_appear_before_non_failing_in_selection(
        self, tmp_path: Path
    ) -> None:
        """Failing tests occupy earlier positions in .selected than non-failing tests."""
        passing_file = _write_test_file(tmp_path / "test_passes.py")
        failing_file = _write_test_file(tmp_path / "test_fails.py")

        result = TestContextPacker(
            candidates=[passing_file, failing_file],
            failing=[failing_file],
            budget=50_000,
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        assert str(failing_file) in selected_strs, "Failing file must be selected"
        assert str(passing_file) in selected_strs, (
            "Passing file must be selected when budget allows"
        )
        assert selected_strs.index(str(failing_file)) < selected_strs.index(
            str(passing_file)
        ), "Failing test (priority-0) must appear before the non-failing test in .selected"

    def test_all_failing_tests_included_even_when_budget_too_small_for_passers(
        self, tmp_path: Path
    ) -> None:
        """Every failing test is packed even when budget is insufficient for non-failing files."""
        f1 = _write_test_file(tmp_path / "test_fail_a.py")
        f2 = _write_test_file(tmp_path / "test_fail_b.py")
        # Non-failing file is intentionally huge to exceed any reasonable budget
        huge_passer = _write_test_file(tmp_path / "test_pass_huge.py", extra_chars=500_000)

        result = TestContextPacker(
            candidates=[f1, f2, huge_passer],
            failing=[f1, f2],
            budget=500,  # tiny: fits the small failing files but not the 500 k-char passer
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        assert str(f1) in selected_strs, "First failing file must be packed (priority-0)"
        assert str(f2) in selected_strs, "Second failing file must be packed (priority-0)"
        assert str(huge_passer) not in selected_strs, (
            "Huge non-failing file must be omitted when budget is exhausted"
        )


# ===========================================================================
# Scenario 3: Budget enforcement for non-failing tests
# ===========================================================================


@_needs_packer
class TestBudgetEnforcement:
    """Non-failing tests are packed greedily until the token budget is reached."""

    def test_selected_tokens_do_not_exceed_budget(self, tmp_path: Path) -> None:
        """Total token count across all selected files must not exceed the configured budget."""
        # Each file: ~400 chars of padding → rough ~100-token estimate at 4 chars/token
        candidates = [
            _write_test_file(tmp_path / f"test_item_{i}.py", extra_chars=396)
            for i in range(10)
        ]
        budget = 500  # fits roughly 1–5 files depending on the estimator

        result = TestContextPacker(candidates=candidates, failing=[], budget=budget).pack()

        assert result.total_tokens <= budget, (
            f"total_tokens={result.total_tokens} must not exceed budget={budget}"
        )

    def test_candidate_exceeding_remaining_budget_is_omitted(self, tmp_path: Path) -> None:
        """A non-failing candidate whose tokens would exceed remaining budget is skipped."""
        small = _write_test_file(tmp_path / "test_small.py")  # ~50 chars
        huge = _write_test_file(tmp_path / "test_huge.py", extra_chars=100_000)

        result = TestContextPacker(
            candidates=[small, huge],
            failing=[],
            budget=500,  # fits small, not huge
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        assert str(small) in selected_strs, "Small file must be selected (fits in budget)"
        assert str(huge) not in selected_strs, (
            "Huge file must be omitted because it exceeds the remaining budget"
        )

    def test_empty_candidates_returns_empty_selection_without_error(
        self, tmp_path: Path
    ) -> None:
        """Packing an empty candidate list returns an empty selection without raising."""
        result = TestContextPacker(candidates=[], failing=[], budget=50_000).pack()

        assert result.selected == [], "Empty candidate list must produce an empty selection"


# ===========================================================================
# Scenario 4: TestPackingManifest — selection entries
# ===========================================================================


@_needs_packer
class TestPackingManifestSelectionEntries:
    """Every selected file must have a manifest entry with decision='selected'."""

    def test_every_selected_file_has_a_manifest_entry(self, tmp_path: Path) -> None:
        """The set of paths in manifest['selected'] exactly matches .selected."""
        f1 = _write_test_file(tmp_path / "test_alpha.py")
        f2 = _write_test_file(tmp_path / "test_beta.py")

        result = TestContextPacker(candidates=[f1, f2], failing=[], budget=50_000).pack()

        selected_paths = {str(p) for p in result.selected}
        manifest_selected_paths = {
            m.path for m in result.manifest if m.decision == "selected"
        }
        assert selected_paths == manifest_selected_paths, (
            "Every selected file must have exactly one manifest entry with decision='selected'"
        )

    def test_manifest_selection_entries_expose_all_four_signals(
        self, tmp_path: Path
    ) -> None:
        """Each manifest selection entry includes all four scoring signal values."""
        f = _write_test_file(tmp_path / "test_signal_check.py")
        result = TestContextPacker(candidates=[f], failing=[], budget=50_000).pack()

        selected_entries = [m for m in result.manifest if m.decision == "selected"]
        assert selected_entries, "Expected at least one selected manifest entry"

        required_signal_keys = {
            "import_graph_distance",
            "symbol_overlap",
            "failure_recency",
            "modification_recency",
        }
        for entry in selected_entries:
            assert hasattr(entry, "signals"), (
                "TestPackingManifest must expose a 'signals' attribute"
            )
            missing = required_signal_keys - set(entry.signals)
            assert not missing, (
                f"Manifest entry for {entry.path!r} is missing signal keys: {missing}"
            )


# ===========================================================================
# Scenario 5: TestPackingManifest — omission entries
# ===========================================================================


@_needs_packer
class TestPackingManifestOmissionEntries:
    """Every omitted file must have a manifest entry with decision='omitted'."""

    def test_omitted_file_appears_in_manifest(self, tmp_path: Path) -> None:
        """A file excluded because it exceeds the budget has a manifest 'omitted' entry."""
        small = _write_test_file(tmp_path / "test_small.py")
        huge = _write_test_file(tmp_path / "test_huge.py", extra_chars=100_000)

        result = TestContextPacker(
            candidates=[small, huge],
            failing=[],
            budget=500,
        ).pack()

        omitted_paths = {m.path for m in result.manifest if m.decision == "omitted"}
        assert any(str(huge) in p for p in omitted_paths), (
            "Omitted file must appear in the manifest with decision='omitted'"
        )

    def test_omission_manifest_entries_include_non_empty_reason(
        self, tmp_path: Path
    ) -> None:
        """Each omission manifest entry carries a human-readable reason string."""
        small = _write_test_file(tmp_path / "test_small.py")
        huge = _write_test_file(tmp_path / "test_huge.py", extra_chars=100_000)

        result = TestContextPacker(
            candidates=[small, huge],
            failing=[],
            budget=500,
        ).pack()

        omitted_entries = [m for m in result.manifest if m.decision == "omitted"]
        assert omitted_entries, "Expected at least one omission manifest entry"
        for entry in omitted_entries:
            assert entry.reason, (
                f"Omission reason must be a non-empty string; got: {entry.reason!r}"
            )


# ===========================================================================
# Scenario 6: AdaGReS-style marginal redundancy penalty
# ===========================================================================


@_needs_packer
class TestAdaGrESRedundancyPenalty:
    """Files with high symbol overlap against already-selected files rank lower
    than novel files (AdaGReS-style marginal gain penalty)."""

    def test_novel_file_ranked_above_highly_redundant_file(
        self, tmp_path: Path
    ) -> None:
        """A file sharing many symbols with a priority-0 anchor file is outranked by
        a novel file that introduces unique symbols."""
        shared_syms = [f"test_common_{i}" for i in range(20)]

        # anchor: priority-0, its symbols are already "in context"
        anchor = _write_test_file(tmp_path / "test_anchor.py", symbols=shared_syms)
        # redundant: duplicates all anchor symbols → high overlap penalty
        redundant = _write_test_file(
            tmp_path / "test_redundant.py", symbols=shared_syms
        )
        # novel: introduces entirely new symbols → low redundancy
        novel = _write_test_file(
            tmp_path / "test_novel.py",
            symbols=[f"test_unique_{i}" for i in range(20)],
        )

        result = TestContextPacker(
            candidates=[anchor, redundant, novel],
            failing=[anchor],  # anchor in priority-0; novel vs redundant compete in ranked lane
            budget=50_000,
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        assert str(novel) in selected_strs, (
            "Novel file (unique symbols) must be selected over the redundant one"
        )
        if str(redundant) in selected_strs:
            assert selected_strs.index(str(novel)) < selected_strs.index(
                str(redundant)
            ), "Novel file must rank higher (earlier) than the high-overlap redundant file"


# ===========================================================================
# Scenario 7: Cross-file deduplication
# ===========================================================================


@_needs_packer
class TestCrossFileDeduplication:
    """The same test path may appear at most once in the selection."""

    def test_duplicate_candidate_path_appears_at_most_once(
        self, tmp_path: Path
    ) -> None:
        """A path passed twice in candidates is deduplicated in .selected."""
        f = _write_test_file(tmp_path / "test_dup.py")

        result = TestContextPacker(
            candidates=[f, f],  # deliberate duplicate
            failing=[],
            budget=50_000,
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        count = selected_strs.count(str(f))
        assert count <= 1, (
            f"Duplicate path must appear at most once in .selected; got {count} occurrences"
        )

    def test_deduped_path_token_budget_counted_only_once(self, tmp_path: Path) -> None:
        """Token budget for a deduplicated path is charged only once, not twice."""
        # File size: just under the budget → one copy fits, two copies would overflow
        budget = 300
        f = _write_test_file(tmp_path / "test_half_budget.py", extra_chars=budget * 4 // 2)

        result = TestContextPacker(
            candidates=[f, f],  # duplicate: only one copy's tokens should be charged
            failing=[],
            budget=budget,
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        assert selected_strs.count(str(f)) <= 1, (
            "After deduplication the file must appear at most once, "
            "confirming its tokens were counted only once"
        )


# ===========================================================================
# Scenario 8: PDD_TEST_TOKEN_BUDGET env var
# ===========================================================================


@_needs_packer
class TestPddTestTokenBudgetEnvVar:
    """PDD_TEST_TOKEN_BUDGET controls the default budget when no explicit budget is given."""

    def test_small_env_budget_selects_fewer_files(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """A small PDD_TEST_TOKEN_BUDGET value restricts the number of selected files."""
        candidates = [
            _write_test_file(tmp_path / f"test_env_{i}.py", extra_chars=200)
            for i in range(10)
        ]

        monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "200")
        result_small = TestContextPacker(candidates=candidates, failing=[]).pack()

        monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "10000000")
        result_large = TestContextPacker(candidates=candidates, failing=[]).pack()

        assert len(result_small.selected) <= len(result_large.selected), (
            "Smaller PDD_TEST_TOKEN_BUDGET must result in fewer or equal selected files"
        )

    def test_explicit_budget_kwarg_overrides_env_var(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """An explicit budget= constructor argument takes precedence over PDD_TEST_TOKEN_BUDGET."""
        candidates = [_write_test_file(tmp_path / f"test_kwarg_{i}.py") for i in range(5)]

        monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "1")  # near-zero env budget
        result = TestContextPacker(
            candidates=candidates,
            failing=[],
            budget=10_000_000,  # explicit unlimited budget
        ).pack()

        assert len(result.selected) > 0, (
            "Explicit budget= kwarg must override the near-zero PDD_TEST_TOKEN_BUDGET env var"
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
        """A test file that imports the target module (distance=1) ranks above a file
        that has no import relationship with it (distance=∞)."""
        target = tmp_path / "my_module.py"
        target.write_text("def compute(): return 42\n", encoding="utf-8")

        # close: directly imports the target
        close = tmp_path / "test_close.py"
        close.write_text(
            "from my_module import compute\n\ndef test_close(): assert compute() == 42\n",
            encoding="utf-8",
        )
        # distant: unrelated, no import of target
        distant = _write_test_file(tmp_path / "test_distant.py")

        result = TestContextPacker(
            candidates=[distant, close],
            failing=[],
            budget=50_000,
            target_module=str(target),
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        if str(close) in selected_strs and str(distant) in selected_strs:
            assert selected_strs.index(str(close)) < selected_strs.index(
                str(distant)
            ), "File with smaller import-graph distance must rank higher in selection"

    def test_symbol_reference_overlap_higher_overlap_ranks_higher(
        self, tmp_path: Path
    ) -> None:
        """A test file that references more of the target module's symbols ranks higher."""
        target = tmp_path / "widget.py"
        target.write_text(
            "def create_widget(): ...\n"
            "def destroy_widget(): ...\n"
            "def resize_widget(): ...\n",
            encoding="utf-8",
        )

        # high_overlap: uses all three target symbols
        high_overlap = tmp_path / "test_widget_full.py"
        high_overlap.write_text(
            "from widget import create_widget, destroy_widget, resize_widget\n"
            "def test_all():\n"
            "    create_widget()\n"
            "    destroy_widget()\n"
            "    resize_widget()\n",
            encoding="utf-8",
        )
        # low_overlap: no reference to target symbols
        low_overlap = _write_test_file(tmp_path / "test_unrelated.py")

        result = TestContextPacker(
            candidates=[low_overlap, high_overlap],
            failing=[],
            budget=50_000,
            target_module=str(target),
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        if str(high_overlap) in selected_strs and str(low_overlap) in selected_strs:
            assert selected_strs.index(str(high_overlap)) < selected_strs.index(
                str(low_overlap)
            ), "Higher symbol-reference overlap with the target must produce higher rank"

    def test_failure_recency_more_recent_failure_ranks_higher(
        self, tmp_path: Path
    ) -> None:
        """A test file that failed more recently ranks above one that failed long ago."""
        now = time_module.time()
        recent = _write_test_file(tmp_path / "test_recent_fail.py")
        old = _write_test_file(tmp_path / "test_old_fail.py")

        result = TestContextPacker(
            candidates=[old, recent],
            failing=[],
            budget=50_000,
            # Pass explicit failure timestamps: recent failed 10 s ago, old failed 1 day ago
            failure_timestamps={str(recent): now - 10, str(old): now - 86_400},
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        if str(recent) in selected_strs and str(old) in selected_strs:
            assert selected_strs.index(str(recent)) < selected_strs.index(str(old)), (
                "More recently failing file must rank higher than one that failed long ago"
            )

    def test_modification_recency_newer_file_ranks_higher(self, tmp_path: Path) -> None:
        """A test file with a newer mtime ranks above one with a very old mtime,
        all else being equal."""
        newer = _write_test_file(tmp_path / "test_newer.py")
        older = _write_test_file(tmp_path / "test_older.py")
        # Force older's mtime to Unix epoch 0 so the difference is unambiguous
        os.utime(older, (0, 0))

        result = TestContextPacker(
            candidates=[older, newer],
            failing=[],
            budget=50_000,
        ).pack()

        selected_strs = [str(p) for p in result.selected]
        if str(newer) in selected_strs and str(older) in selected_strs:
            assert selected_strs.index(str(newer)) < selected_strs.index(str(older)), (
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
    """fix_error_loop() forwards context_compression to apply_compression_env correctly.

    The function calls apply_compression_env() before any file I/O, so we
    can patch that function and allow fix_error_loop to bail out early
    (non-existent files trigger an immediate early-return) while still
    capturing the apply_compression_env() arguments.
    """

    def test_context_compression_test_calls_apply_compression_env(
        self, tmp_path: Path
    ) -> None:
        """fix_error_loop(context_compression='test') calls
        apply_compression_env({'context_compression': 'test'})."""
        from pdd.fix_error_loop import fix_error_loop

        # Non-existent files → early return after apply_compression_env is called
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
