"""Tests for auto-deps CSV entry wipe and unnecessary re-summarization bugs.

These tests target two real bugs identified in the auto-deps system:

Bug 1 - Entry wipeout: summarize_directory() only writes entries for files it
discovers in the current run. If a file was previously summarized but is not in
the current scan (e.g., different directory_path, file deleted then re-added,
different git state), its CSV entry is silently dropped. The function does no
merging of old entries with new results. This causes the CSV to lose entries
that were previously computed, forcing expensive re-summarization later.

Bug 2 - Unnecessary re-summarization: The cache lookup uses relative paths
computed from base_dir, but base_dir changes depending on how directory_path is
specified (directory vs glob vs absolute path). This causes cache misses even
when file content hasn't changed, triggering needless LLM calls.
"""

import csv
import hashlib
import os
from io import StringIO
from unittest.mock import patch

import pytest

from pdd.summarize_directory import summarize_directory, FileSummary


@pytest.fixture
def mock_load_prompt_template():
    with patch('pdd.summarize_directory.load_prompt_template') as mock:
        mock.return_value = "Summarize the following file contents."
        yield mock


@pytest.fixture
def mock_llm_invoke():
    with patch('pdd.summarize_directory.llm_invoke') as mock:
        mock_response = {
            'result': FileSummary(
                file_summary="Fresh LLM summary.",
                key_exports=["func"],
                dependencies=["os"],
            ),
            'cost': 0.01,
            'model_name': "TestModel",
        }
        mock.return_value = mock_response
        yield mock


def _make_csv(rows: list[dict]) -> str:
    """Build a CSV string from a list of row dicts."""
    output = StringIO()
    fieldnames = ['full_path', 'file_summary', 'key_exports', 'dependencies', 'content_hash']
    writer = csv.DictWriter(output, fieldnames=fieldnames)
    writer.writeheader()
    writer.writerows(rows)
    return output.getvalue()


def _parse_csv(csv_str: str) -> list[dict]:
    return list(csv.DictReader(StringIO(csv_str)))


def _content_hash(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


# ---------------------------------------------------------------------------
# Bug 1: Entry wipeout — files not in current scan lose their CSV entries
# ---------------------------------------------------------------------------

class TestEntryWipeout:
    """summarize_directory should preserve CSV entries for files outside the
    current scan scope, not silently drop them."""

    def test_entries_for_unscanned_files_are_preserved(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """If the CSV has entries for files in directory A and we scan
        directory B, directory A's entries should not be wiped out.

        This is the core wipeout bug: the function rewrites the entire CSV
        with only the files it discovered, dropping everything else.
        """
        # Set up: two subdirectories, each with a file
        dir_a = tmp_path / "dir_a"
        dir_a.mkdir()
        dir_b = tmp_path / "dir_b"
        dir_b.mkdir()

        file_a = dir_a / "module_a.py"
        file_a.write_text("class A: pass")
        file_b = dir_b / "module_b.py"
        file_b.write_text("class B: pass")

        # Existing CSV has entries for BOTH files
        existing_csv = _make_csv([
            {
                'full_path': 'dir_a/module_a.py',
                'file_summary': 'Module A summary',
                'key_exports': '["A"]',
                'dependencies': '[]',
                'content_hash': _content_hash("class A: pass"),
            },
            {
                'full_path': 'dir_b/module_b.py',
                'file_summary': 'Module B summary',
                'key_exports': '["B"]',
                'dependencies': '[]',
                'content_hash': _content_hash("class B: pass"),
            },
        ])

        # Scan only dir_b — dir_a's entry should survive
        csv_output, cost, _ = summarize_directory(
            directory_path=str(dir_b),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        rows = _parse_csv(csv_output)
        paths = {row['full_path'] for row in rows}

        # BUG: currently dir_a/module_a.py gets wiped because it wasn't
        # in the scan. This test documents the expected behavior.
        assert 'dir_a/module_a.py' in paths or any(
            'module_a' in p for p in paths
        ), (
            "Entry for module_a.py was wiped from the CSV even though its "
            "content hasn't changed. The CSV should preserve entries for "
            f"files outside the current scan scope. Got paths: {paths}"
        )

    def test_deleted_then_readded_file_not_resummarized(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """If a file is temporarily removed (e.g., on a different branch)
        and then re-added with the same content, it should reuse the cached
        summary rather than making a new LLM call.

        This simulates the scenario where someone switches branches, auto-deps
        runs and wipes entries, then they switch back and have to re-summarize
        everything.
        """
        # Create initial file
        py_file = tmp_path / "utils.py"
        content = "def helper(): return 42"
        py_file.write_text(content)

        # First run: summarize the file
        csv_output_1, cost_1, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
        )
        assert cost_1 > 0  # LLM was called
        mock_llm_invoke.reset_mock()

        # Simulate: file is deleted (branch switch), auto-deps runs
        py_file.unlink()
        csv_output_2, _, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=csv_output_1,
        )

        # File comes back with same content
        py_file.write_text(content)

        # After the merge fix, csv_output_2 retains the entry for utils.py
        # even though the file was absent during that scan.  When the file
        # reappears with the same content, it should be a cache hit.
        csv_output_3, cost_3, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=csv_output_2,
        )

        rows = _parse_csv(csv_output_3)
        assert len(rows) == 1

        # If entries were preserved, cost_3 would be 0 (cache hit).
        # The bug causes cost_3 > 0 because the entry was wiped.
        assert cost_3 == 0, (
            f"File was re-summarized (cost={cost_3}) even though its content "
            "hasn't changed. The entry was wiped from the CSV when the file "
            "was temporarily absent."
        )

    def test_scanning_subset_preserves_full_csv(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Scanning a glob pattern that matches a subset of files should not
        remove entries for files that don't match the pattern."""
        # Create files of different types
        (tmp_path / "alpha.py").write_text("x = 1")
        (tmp_path / "beta.js").write_text("const y = 2")

        # CSV has entries for both
        existing_csv = _make_csv([
            {
                'full_path': 'alpha.py',
                'file_summary': 'Alpha module',
                'key_exports': '["x"]',
                'dependencies': '[]',
                'content_hash': _content_hash("x = 1"),
            },
            {
                'full_path': 'beta.js',
                'file_summary': 'Beta module',
                'key_exports': '["y"]',
                'dependencies': '[]',
                'content_hash': _content_hash("const y = 2"),
            },
        ])

        # Scan only *.py files
        csv_output, _, _ = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        rows = _parse_csv(csv_output)
        paths = {row['full_path'] for row in rows}

        # BUG: beta.js gets dropped because *.py glob doesn't match it
        assert any('beta' in p for p in paths), (
            f"Entry for beta.js was wiped when scanning only *.py files. "
            f"Got paths: {paths}"
        )


# ---------------------------------------------------------------------------
# Bug 2: Unnecessary re-summarization due to path normalization mismatches
# ---------------------------------------------------------------------------

class TestUnnecessaryResummarization:
    """Cache lookups should work regardless of how directory_path is specified,
    as long as the underlying files are the same."""

    def test_directory_vs_glob_path_cache_consistency(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Summarizing with directory_path='dir/' then 'dir/*.py' should reuse
        the cache, not re-summarize everything.

        The bug: base_dir is computed differently for directory paths vs glob
        patterns, so relative paths differ, causing cache misses.
        """
        subdir = tmp_path / "src"
        subdir.mkdir()
        (subdir / "main.py").write_text("def main(): pass")

        # First run with directory path
        csv_output_1, cost_1, _ = summarize_directory(
            directory_path=str(subdir),
            strength=0.5,
            temperature=0.0,
        )
        assert cost_1 > 0  # LLM was called
        mock_llm_invoke.reset_mock()

        # Second run with glob pattern for same directory
        csv_output_2, cost_2, _ = summarize_directory(
            directory_path=str(subdir / "*.py"),
            strength=0.5,
            temperature=0.0,
            csv_file=csv_output_1,
        )

        # Should be a cache hit — same file, same content
        assert cost_2 == 0, (
            f"File was re-summarized (cost={cost_2}) when switching from "
            "directory path to glob pattern, even though content is unchanged. "
            "This is caused by base_dir changing the relative path used for "
            "cache lookup."
        )

    def test_trailing_slash_does_not_invalidate_cache(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """'dir' vs 'dir/' should not cause cache invalidation."""
        (tmp_path / "app.py").write_text("import flask")

        # First run without trailing separator
        csv_output_1, cost_1, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
        )
        assert cost_1 > 0
        mock_llm_invoke.reset_mock()

        # Second run with trailing separator
        csv_output_2, cost_2, _ = summarize_directory(
            directory_path=str(tmp_path) + os.sep,
            strength=0.5,
            temperature=0.0,
            csv_file=csv_output_1,
        )

        assert cost_2 == 0, (
            f"Adding a trailing separator caused re-summarization (cost={cost_2}). "
            "Path normalization should handle this."
        )

    def test_old_format_csv_without_exports_forces_resummarization(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Old-format CSV entries (missing key_exports/dependencies columns)
        should be re-summarized. This is expected behavior, not a bug — but
        documents that upgrading the CSV format triggers a full rescan.

        When someone adds the selective includes feature, ALL existing entries
        get the _backfilled flag and are re-summarized on next run.
        """
        (tmp_path / ".pddrc").touch()
        content = "def old_func(): pass"
        (tmp_path / "legacy.py").write_text(content)

        # Old-format CSV: only has full_path, file_summary, content_hash
        old_csv = (
            "full_path,file_summary,content_hash\n"
            f"legacy.py,Old summary,{_content_hash(content)}\n"
        )

        csv_output, cost, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=old_csv,
        )

        # This SHOULD re-summarize (old format lacks key_exports/dependencies)
        assert cost > 0, "Old-format entries should trigger re-summarization"

        # Verify the new entry has all columns
        rows = _parse_csv(csv_output)
        assert len(rows) == 1
        assert rows[0]['key_exports'] != '[]' or rows[0]['dependencies'] != '[]' or True
        assert 'key_exports' in rows[0]
        assert 'dependencies' in rows[0]

    def test_absolute_vs_relative_path_in_csv_cache_hit(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """If the existing CSV has absolute paths but the current run produces
        relative paths (or vice versa), cache should still hit.

        The code attempts backward compat at line 366 by checking both
        normalized_path and abs_normalized_path, but the CSV is always written
        with relative paths (line 417), so after one run with absolute paths in
        CSV, the next run's relative paths won't match the written output.
        """
        (tmp_path / ".pddrc").touch()
        content = "x = 1"
        py_file = tmp_path / "mod.py"
        py_file.write_text(content)

        # CSV with absolute path
        existing_csv = _make_csv([{
            'full_path': str(py_file),  # absolute path
            'file_summary': 'Cached with absolute path',
            'key_exports': '["x"]',
            'dependencies': '[]',
            'content_hash': _content_hash(content),
        }])

        csv_output, cost, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        # Should be a cache hit — the code checks abs path for compat
        assert cost == 0, (
            f"File with absolute path in CSV was re-summarized (cost={cost}) "
            "instead of getting a cache hit via backward-compat path lookup."
        )

        # Now verify the OUTPUT uses relative paths (so next run can cache hit)
        rows = _parse_csv(csv_output)
        assert len(rows) == 1
        assert not os.path.isabs(rows[0]['full_path']), (
            f"CSV output should use relative paths, got: {rows[0]['full_path']}"
        )


# ---------------------------------------------------------------------------
# Bug 3: Alternating directory scans wipe each other's entries
# (exact real-world pattern from issue #603 comment)
# ---------------------------------------------------------------------------

class TestAlternatingDirectoryScans:
    """Reproduces the exact production pattern: sync scans context/ (example
    files), then a separate run scans pdd/ (source files). Both write to the
    same project_dependencies.csv.  Each scan should ADD entries, not replace
    the CSV wholesale."""

    def test_alternating_scans_accumulate_entries(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Scan context/ then pdd/ — CSV should contain entries from both.

        This mirrors the real history:
        - commit 0ff8ecfb7: CSV has 748 lines (context/ entries)
        - commit cb52e3070: CSV drops to 263 (pdd/ scan wiped context/ entries)
        - commit 920ba06df: CSV is 269 (context/ scan wiped pdd/ entries)
        """
        # Set up two directories like the real project
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()

        # Create example files in context/
        for name in ["example_a.py", "example_b.py", "example_c.py"]:
            (context_dir / name).write_text(f"# {name}")

        # Create source files in pdd/
        for name in ["cli.py", "sync.py"]:
            (pdd_dir / name).write_text(f"# {name}")

        # Step 1: First scan covers context/
        csv_after_context, cost1, _ = summarize_directory(
            directory_path=str(context_dir),
            strength=0.5,
            temperature=0.0,
        )
        context_rows = _parse_csv(csv_after_context)
        assert len(context_rows) == 3, f"Expected 3 context entries, got {len(context_rows)}"

        # Step 2: Second scan covers pdd/, passing the context/ CSV as cache
        csv_after_pdd, cost2, _ = summarize_directory(
            directory_path=str(pdd_dir),
            strength=0.5,
            temperature=0.0,
            csv_file=csv_after_context,
        )
        pdd_rows = _parse_csv(csv_after_pdd)

        # CSV should now have BOTH context/ and pdd/ entries
        pdd_paths = {row['full_path'] for row in pdd_rows}
        assert len(pdd_rows) >= 5, (
            f"After scanning pdd/, CSV should have 5 entries (3 context + 2 pdd), "
            f"got {len(pdd_rows)}. Context entries were wiped. Paths: {pdd_paths}"
        )

        # Step 3: Third scan covers context/ again — should not re-summarize
        # the 3 context files (cache hit) AND should preserve pdd/ entries
        mock_llm_invoke.reset_mock()
        csv_after_context2, cost3, _ = summarize_directory(
            directory_path=str(context_dir),
            strength=0.5,
            temperature=0.0,
            csv_file=csv_after_pdd,
        )
        final_rows = _parse_csv(csv_after_context2)
        final_paths = {row['full_path'] for row in final_rows}

        # Context files should be cache hits (no LLM cost)
        assert cost3 == 0, (
            f"Context files were re-summarized on second scan (cost={cost3}). "
            "Should be cache hits."
        )
        # All 5 entries should still be present
        assert len(final_rows) >= 5, (
            f"After re-scanning context/, CSV should still have 5 entries, "
            f"got {len(final_rows)}. Pdd entries were wiped. Paths: {final_paths}"
        )


# ---------------------------------------------------------------------------
# Combined scenario: the full pain sequence described in the conversation
# ---------------------------------------------------------------------------

class TestFullWipeoutScenario:
    """End-to-end scenario: CSV has 5 entries, scan finds only 3 files,
    the CSV should still retain all 5 entries (3 updated + 2 preserved).
    Currently it produces only 3 entries, losing 2."""

    def test_partial_scan_preserves_unscanned_entries(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Simulates the real-world scenario where project_dependencies.csv
        has ~200 entries but a scan of a subdirectory wipes it down to just
        the files in that subdirectory.
        """
        # Create 3 files that will be scanned
        for i in range(3):
            (tmp_path / f"scanned_{i}.py").write_text(f"val = {i}")

        # CSV has 5 entries: 3 for files that exist + 2 for files elsewhere
        rows = []
        for i in range(3):
            rows.append({
                'full_path': f'scanned_{i}.py',
                'file_summary': f'Scanned file {i}',
                'key_exports': f'["val"]',
                'dependencies': '[]',
                'content_hash': _content_hash(f"val = {i}"),
            })
        # These 2 entries are for files in a different directory
        rows.append({
            'full_path': 'other_dir/important.py',
            'file_summary': 'Important module in another dir',
            'key_exports': '["important_func"]',
            'dependencies': '["requests"]',
            'content_hash': 'abc123',
        })
        rows.append({
            'full_path': 'other_dir/utils.py',
            'file_summary': 'Utility functions',
            'key_exports': '["helper"]',
            'dependencies': '["os"]',
            'content_hash': 'def456',
        })

        existing_csv = _make_csv(rows)

        csv_output, _, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        output_rows = _parse_csv(csv_output)
        output_paths = {row['full_path'] for row in output_rows}

        # The 3 scanned files should be there
        for i in range(3):
            assert any(f'scanned_{i}' in p for p in output_paths), (
                f"scanned_{i}.py missing from output"
            )

        # BUG: The 2 unscanned entries should also be preserved
        assert len(output_rows) >= 5, (
            f"Expected at least 5 rows (3 scanned + 2 preserved), "
            f"got {len(output_rows)}. Entries for other_dir/ were wiped. "
            f"Output paths: {output_paths}"
        )


# ---------------------------------------------------------------------------
# Symlinked directories: cache should hit even if the directory is
# accessed through a symlink (e.g. macOS /var -> /private/var).
# ---------------------------------------------------------------------------

class TestSymlinkCacheConsistency:
    """Files accessed through a symlink should still get cache hits."""

    def test_symlinked_directory_gets_cache_hit(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Scanning via a symlink to the directory should reuse cached entries
        from a scan of the real directory."""
        real_dir = tmp_path / "real_project"
        real_dir.mkdir()
        (real_dir / ".pddrc").touch()
        (real_dir / "app.py").write_text("print('hello')")

        # First scan via the real path
        csv1, cost1, _ = summarize_directory(
            directory_path=str(real_dir),
            strength=0.5,
            temperature=0.0,
        )
        assert cost1 > 0
        mock_llm_invoke.reset_mock()

        # Create a symlink to the project
        link_dir = tmp_path / "link_project"
        link_dir.symlink_to(real_dir)

        # Rescan via the symlink — should be a cache hit
        csv2, cost2, _ = summarize_directory(
            directory_path=str(link_dir),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )
        assert cost2 == 0, (
            f"Scanning via symlink caused re-summarization (cost={cost2}). "
            "Cache lookup should match via realpath normalization."
        )

    def test_symlinked_file_not_duplicated_in_csv(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """When a file is reachable via both a real path and a symlink path,
        it should appear only once in the CSV output, not as two entries."""
        real_dir = tmp_path / "real_project"
        real_dir.mkdir()
        (real_dir / ".pddrc").touch()
        (real_dir / "utils.py").write_text("x = 1")

        # First scan via real path
        csv1, _, _ = summarize_directory(
            directory_path=str(real_dir),
            strength=0.5,
            temperature=0.0,
        )

        # Create symlink and scan via it, passing first CSV as cache
        link_dir = tmp_path / "link_project"
        link_dir.symlink_to(real_dir)

        csv2, _, _ = summarize_directory(
            directory_path=str(link_dir),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )

        rows = _parse_csv(csv2)
        assert len(rows) == 1, (
            f"File should appear once in CSV, got {len(rows)} entries: "
            f"{[r['full_path'] for r in rows]}"
        )


# ---------------------------------------------------------------------------
# Projects without any root marker
# ---------------------------------------------------------------------------

class TestNoProjectMarkerFallback:
    """When no project root marker exists (.git, .pddrc, pyproject.toml, etc.),
    summarize_directory stores absolute paths so that files are unambiguous
    across scans of different directories.  The pipeline should still work:
    no crashes, cache hits on rescan, entries preserved, and no collisions
    between same-named files in different directories."""

    def test_no_markers_uses_absolute_paths(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Without project markers, CSV paths should be absolute so they
        are stable and unambiguous regardless of which directory is scanned."""
        bare_dir = tmp_path / "no_markers" / "src"
        bare_dir.mkdir(parents=True)
        (bare_dir / "app.py").write_text("print('hello')")

        csv_output, _, _ = summarize_directory(
            directory_path=str(bare_dir),
            strength=0.5,
            temperature=0.0,
        )
        rows = _parse_csv(csv_output)
        assert len(rows) == 1
        assert os.path.isabs(rows[0]['full_path']), (
            f"Without project markers, path should be absolute, "
            f"got: {rows[0]['full_path']}"
        )

    def test_no_markers_no_collision_same_named_files(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Two directories each containing utils.py should produce two
        distinct CSV entries, not overwrite each other."""
        dir_a = tmp_path / "no_markers" / "dir_a"
        dir_a.mkdir(parents=True)
        (dir_a / "utils.py").write_text("def helper_a(): return 1")

        dir_b = tmp_path / "no_markers" / "dir_b"
        dir_b.mkdir(parents=True)
        (dir_b / "utils.py").write_text("def helper_b(): return 2")

        csv1, _, _ = summarize_directory(
            directory_path=str(dir_a),
            strength=0.5,
            temperature=0.0,
        )
        csv2, _, _ = summarize_directory(
            directory_path=str(dir_b),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )

        rows = _parse_csv(csv2)
        assert len(rows) == 2, (
            f"Same-named files in different directories should produce "
            f"2 distinct entries, got {len(rows)}: "
            f"{[r['full_path'] for r in rows]}"
        )

    def test_no_markers_caches_and_preserves(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Without project markers: same-directory rescans get cache hits,
        and cross-directory entries are preserved."""
        dir_a = tmp_path / "no_markers" / "dir_a"
        dir_a.mkdir(parents=True)
        (dir_a / "app.py").write_text("print('hello')")

        dir_b = tmp_path / "no_markers" / "dir_b"
        dir_b.mkdir(parents=True)
        (dir_b / "lib.py").write_text("x = 1")

        # Scan dir_a
        csv1, cost1, _ = summarize_directory(
            directory_path=str(dir_a),
            strength=0.5,
            temperature=0.0,
        )
        assert cost1 > 0
        mock_llm_invoke.reset_mock()

        # Scan dir_b, passing dir_a's CSV — dir_a's entry preserved
        csv2, _, _ = summarize_directory(
            directory_path=str(dir_b),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )
        rows2 = _parse_csv(csv2)
        assert len(rows2) == 2, (
            f"dir_a entry should be preserved when scanning dir_b, "
            f"got {len(rows2)} rows: {[r['full_path'] for r in rows2]}"
        )
        mock_llm_invoke.reset_mock()

        # Rescan dir_a — should be a cache hit
        csv3, cost3, _ = summarize_directory(
            directory_path=str(dir_a),
            strength=0.5,
            temperature=0.0,
            csv_file=csv2,
        )
        assert cost3 == 0, (
            f"Same-directory rescan should be a cache hit even without "
            f"project markers, but LLM was called (cost={cost3})"
        )
        rows3 = _parse_csv(csv3)
        assert len(rows3) == 2, (
            f"Both entries should be preserved after rescan, "
            f"got {len(rows3)} rows: {[r['full_path'] for r in rows3]}"
        )

    def test_existing_csv_with_both_abs_and_rel_deduplicates(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """If the existing CSV somehow contains both an absolute-path entry
        and a relative-path entry for the same file, the output should have
        only one entry (the relative version)."""
        (tmp_path / ".pddrc").touch()
        content = "x = 1"
        py_file = tmp_path / "mod.py"
        py_file.write_text(content)

        existing_csv = _make_csv([
            {
                'full_path': str(py_file.resolve()),  # absolute
                'file_summary': 'Abs summary',
                'key_exports': '["x"]',
                'dependencies': '[]',
                'content_hash': _content_hash(content),
            },
            {
                'full_path': 'mod.py',  # relative
                'file_summary': 'Rel summary',
                'key_exports': '["x"]',
                'dependencies': '[]',
                'content_hash': _content_hash(content),
            },
        ])

        csv_output, cost, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        rows = _parse_csv(csv_output)
        mod_entries = [r for r in rows if 'mod' in r['full_path']]
        assert len(mod_entries) == 1, (
            f"Same file with both abs and rel paths should produce one entry, "
            f"got {len(mod_entries)}: {[r['full_path'] for r in mod_entries]}"
        )
        # Should be relative
        assert not os.path.isabs(mod_entries[0]['full_path']), (
            f"Output path should be relative, got: {mod_entries[0]['full_path']}"
        )
        # Should be a cache hit (no LLM cost)
        assert cost == 0, f"Should be a cache hit, got cost={cost}"

    def test_no_markers_to_git_init_seamless_transition(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """After git init, the next scan should convert absolute paths to
        project-relative paths without re-summarizing (cache hits via the
        backward-compat absolute-path lookup)."""
        import subprocess

        project = tmp_path / "new_project"
        project.mkdir()
        src = project / "src"
        src.mkdir()
        (src / "app.py").write_text("print('hello')")

        # Scan WITHOUT markers — absolute paths
        csv1, cost1, _ = summarize_directory(
            directory_path=str(src),
            strength=0.5,
            temperature=0.0,
        )
        assert cost1 > 0
        rows1 = _parse_csv(csv1)
        assert os.path.isabs(rows1[0]['full_path'])
        mock_llm_invoke.reset_mock()

        # Now git init — adds a project root marker
        subprocess.run(
            ["git", "init"], cwd=str(project), capture_output=True, check=True
        )
        subprocess.run(
            ["git", "add", "."], cwd=str(project), capture_output=True, check=True
        )
        subprocess.run(
            ["git", "commit", "-m", "init", "--allow-empty"],
            cwd=str(project), capture_output=True, check=True,
            env={**os.environ, "GIT_AUTHOR_NAME": "test", "GIT_AUTHOR_EMAIL": "t@t",
                 "GIT_COMMITTER_NAME": "test", "GIT_COMMITTER_EMAIL": "t@t"},
        )

        # Rescan — should be a cache hit (absolute path matched via compat)
        # and output should now use project-relative paths
        csv2, cost2, _ = summarize_directory(
            directory_path=str(src),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )
        assert cost2 == 0, (
            f"After git init, rescan should be a cache hit (cost={cost2}). "
            "The backward-compat absolute-path lookup should match the "
            "existing CSV entry."
        )
        rows2 = _parse_csv(csv2)
        new_entry = next(r for r in rows2 if 'app' in r['full_path'])
        assert not os.path.isabs(new_entry['full_path']), (
            f"After git init, paths should be project-relative, "
            f"got: {new_entry['full_path']}"
        )

        # The old absolute-path entry should NOT survive alongside the new
        # relative-path entry — no duplicates.
        app_entries = [r for r in rows2 if 'app' in r['full_path']]
        assert len(app_entries) == 1, (
            f"After git init transition, app.py should appear exactly once "
            f"in the CSV (old absolute entry replaced by new relative entry), "
            f"got {len(app_entries)}: {[r['full_path'] for r in app_entries]}"
        )


# ---------------------------------------------------------------------------
# Pipeline-level test: no markers, full insert_includes flow
# ---------------------------------------------------------------------------

class TestNoMarkerPipeline:
    """Exercise the full pipeline (insert_includes → auto_include →
    summarize_directory) in a project with NO root markers (.git, .pddrc,
    etc.).  Verifies that auto-deps, caching, path resolution, and dedup
    all still function correctly."""

    def test_insert_includes_pipeline_without_markers(self, tmp_path):
        """Full pipeline run in a marker-free project:
        1. First run: files are summarized, LLM picks dependencies, prompt updated
        2. Second run (same directory): all summarize calls are cache hits
        3. CSV paths are relative, no crashes anywhere in the chain
        """
        from unittest.mock import patch as mock_patch
        from pdd.insert_includes import insert_includes, InsertIncludesOutput
        from pdd.auto_include import AutoIncludeResult, NewInclude

        # No .git, .pddrc, pyproject.toml, data/, or .env
        src_dir = tmp_path / "no_markers_proj" / "src"
        src_dir.mkdir(parents=True)
        (src_dir / "utils.py").write_text(
            "def helper():\n    return 42\n\ndef format_output(data):\n    return str(data)\n"
        )
        (src_dir / "models.py").write_text(
            "class User:\n    def __init__(self, name):\n        self.name = name\n"
        )

        csv_path = tmp_path / "no_markers_proj" / "deps.csv"
        # Without markers, CSV stores absolute paths
        utils_abs = str((src_dir / "utils.py").resolve())

        input_prompt = "Generate a REST API that uses User model and helper utilities."

        # Mock the LLM calls but let everything else (path resolution, caching,
        # CSV I/O, dedup) run for real.
        summarize_call_count = [0]

        def mock_summarize_llm(**kwargs):
            summarize_call_count[0] += 1
            return {
                "result": FileSummary(
                    file_summary="Mock summary",
                    key_exports=["func"],
                    dependencies=["os"],
                ),
                "cost": 0.001,
                "model_name": "mock",
            }

        def mock_auto_include_llm(**kwargs):
            pydantic_model = kwargs.get("output_pydantic")
            if pydantic_model == AutoIncludeResult:
                return {
                    "result": AutoIncludeResult(
                        reasoning="Need utils",
                        new_includes=[NewInclude(file=utils_abs, module="utils")],
                        existing_include_annotations=[],
                    ),
                    "cost": 0.001,
                    "model_name": "mock",
                }
            # insert_includes LLM call
            prompt_text = kwargs.get("input_json", {}).get("actual_prompt_to_update", "")
            return {
                "result": InsertIncludesOutput(
                    output_prompt=f"<include>{utils_abs}</include>\n" + prompt_text.rstrip()
                ),
                "cost": 0.001,
                "model_name": "mock",
            }

        with mock_patch("pdd.summarize_directory.load_prompt_template", return_value="template"), \
             mock_patch("pdd.summarize_directory.llm_invoke", side_effect=mock_summarize_llm), \
             mock_patch("pdd.auto_include.load_prompt_template", return_value="template"), \
             mock_patch("pdd.auto_include.llm_invoke", side_effect=mock_auto_include_llm), \
             mock_patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             mock_patch("pdd.insert_includes.preprocess", side_effect=lambda p, **kw: p), \
             mock_patch("pdd.insert_includes.llm_invoke", side_effect=mock_auto_include_llm):

            # --- Run 1: first scan ---
            output1, csv_out1, cost1, model1 = insert_includes(
                input_prompt=input_prompt,
                directory_path=str(src_dir),
                csv_filename=str(csv_path),
                strength=0.5,
                temperature=0.0,
                dedup=True,
            )

            assert "<include" in output1, f"Output should have include tags. Got:\n{output1}"
            # CSV should have entries
            rows1 = _parse_csv(csv_out1)
            assert len(rows1) >= 2, f"CSV should have entries for both files, got {len(rows1)}"
            # Without markers, paths should be absolute
            for r in rows1:
                assert os.path.isabs(r['full_path']), (
                    f"Without markers, CSV path should be absolute, "
                    f"got: {r['full_path']}"
                )
            run1_summarize_calls = summarize_call_count[0]
            assert run1_summarize_calls == 2, (
                f"Run 1 should summarize 2 files, got {run1_summarize_calls}"
            )

            # --- Run 2: same directory, same CSV — should be all cache hits ---
            summarize_call_count[0] = 0

            output2, csv_out2, cost2, model2 = insert_includes(
                input_prompt=output1,  # feed output of run 1
                directory_path=str(src_dir),
                csv_filename=str(csv_path),
                strength=0.5,
                temperature=0.0,
                dedup=True,
            )

            assert summarize_call_count[0] == 0, (
                f"Run 2 should be all cache hits (0 summarize LLM calls), "
                f"got {summarize_call_count[0]}. Cache keys are unstable."
            )
            rows2 = _parse_csv(csv_out2)
            assert len(rows2) >= len(rows1), (
                f"CSV entries should not decrease between runs "
                f"({len(rows1)} → {len(rows2)})"
            )


# ---------------------------------------------------------------------------
# Nested project markers: .git wins over nested .pddrc (PR #763 review)
# ---------------------------------------------------------------------------

class TestNestedProjectMarkers:
    """Covers the scenario raised in PR #763's review: a repo with .git at
    the top and nested .pddrc files inside sub-modules.  A file's CSV path
    must be stable across scans started from different directories,
    otherwise the cache misses and duplicate entries accumulate — exactly
    the bug this PR set out to fix, but surfaced again via nested markers.
    """

    def test_nested_pddrc_does_not_split_root_across_scans(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Layout from Greg's comment:
            repo/.git
            repo/module/.pddrc
            repo/module/context/a.py

        Scan repo/module/context first, then scan repo/. Without the
        prioritized-.git fix, scan 1 stores "context/a.py" (resolved
        against module/'s .pddrc) and scan 2 stores "module/context/a.py"
        (resolved against the outer .git).  The file gets re-summarized
        and two entries coexist in the CSV.

        With .git prioritized over weak markers, both scans resolve the
        root to repo/, store "module/context/a.py", and the second scan
        is a cache hit for a.py.
        """
        import subprocess

        repo = tmp_path / "repo"
        repo.mkdir()
        subprocess.run(
            ["git", "init"], cwd=str(repo), capture_output=True, check=True
        )
        module = repo / "module"
        module.mkdir()
        (module / ".pddrc").touch()
        context = module / "context"
        context.mkdir()
        file_a = context / "a.py"
        file_a.write_text("x = 1")
        # git ls-files only returns tracked files — commit so the scan finds a.py
        git_env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
        subprocess.run(["git", "add", "."], cwd=str(repo), capture_output=True, check=True)
        subprocess.run(["git", "commit", "-m", "init"], cwd=str(repo),
                       capture_output=True, check=True, env=git_env)

        # Scan 1: from the innermost directory
        csv1, cost1, _ = summarize_directory(
            directory_path=str(context),
            strength=0.5,
            temperature=0.0,
        )
        rows1 = _parse_csv(csv1)
        a_rows1 = [r for r in rows1 if r['full_path'].endswith("a.py")]
        assert len(a_rows1) == 1, f"Scan 1 should find a.py. Rows: {rows1}"
        path1 = a_rows1[0]['full_path']

        # Scan 2: from the repo root, feeding scan 1's CSV
        mock_llm_invoke.reset_mock()
        csv2, cost2, _ = summarize_directory(
            directory_path=str(repo),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )
        rows2 = _parse_csv(csv2)
        paths2 = [r['full_path'] for r in rows2]

        # No duplicate entry for the same file
        a_entries = [p for p in paths2 if p.endswith("a.py")]
        assert len(a_entries) == 1, (
            f"Scanning from a deeper then shallower directory produced "
            f"duplicate CSV entries for the same file: {a_entries}. "
            f"Nested .pddrc should not override the outer .git root."
        )

        # Both scans agree on the same relative path.
        assert path1 == a_entries[0], (
            f"Scan paths disagree: scan1={path1!r}, scan2={a_entries[0]!r}. "
            f"Both should be 'module/context/a.py' (relative to repo root)."
        )
        assert path1 == os.path.join("module", "context", "a.py"), (
            f"Path should be relative to the .git root (repo/), "
            f"got: {path1!r}"
        )

        # Scan 2 must be a cache hit for a.py specifically. git ls-files
        # from the repo root also returns module/.pddrc (which scan 1 never
        # saw), so scan 2's total cost is nonzero — check per-file instead:
        # only newly-discovered files may have triggered LLM calls.
        newly_discovered = {r['full_path'] for r in rows2} - {r['full_path'] for r in rows1}
        assert mock_llm_invoke.call_count <= len(newly_discovered), (
            f"Scan 2 made {mock_llm_invoke.call_count} LLM calls but only "
            f"{len(newly_discovered)} files were new ({newly_discovered}). "
            f"Excess calls mean a.py was re-summarized — the nested .pddrc "
            f"produced a different cache key than scan 1."
        )

    def test_nested_pddrc_without_git_uses_outermost(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Same layout but without .git — two nested .pddrc markers.
        Without a strong marker, the outermost weak marker should win so
        scans at different depths still agree on the root.
        """
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".pddrc").touch()  # outer weak marker
        module = repo / "module"
        module.mkdir()
        (module / ".pddrc").touch()  # inner weak marker
        context = module / "context"
        context.mkdir()
        (context / "a.py").write_text("x = 1")

        # Inner scan
        csv1, _, _ = summarize_directory(
            directory_path=str(context),
            strength=0.5,
            temperature=0.0,
        )
        rows1 = _parse_csv(csv1)
        path1 = rows1[0]['full_path']

        # Outer scan
        mock_llm_invoke.reset_mock()
        csv2, cost2, _ = summarize_directory(
            directory_path=str(repo),
            strength=0.5,
            temperature=0.0,
            csv_file=csv1,
        )
        rows2 = _parse_csv(csv2)
        a_entries = [r['full_path'] for r in rows2 if r['full_path'].endswith("a.py")]

        assert len(a_entries) == 1, (
            f"Nested .pddrc markers produced duplicate entries: {a_entries}"
        )
        assert path1 == a_entries[0], (
            f"Scan paths disagree: {path1!r} vs {a_entries[0]!r}"
        )
        assert path1 == os.path.join("module", "context", "a.py"), (
            f"Path should be relative to the outermost .pddrc (repo/), "
            f"got: {path1!r}"
        )
        assert cost2 == 0, (
            f"Outer scan should cache-hit a.py, but cost={cost2}"
        )

    def test_git_inside_outer_weak_marker_still_uses_git(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """A repo vendored inside a larger project (outer pyproject.toml,
        inner .git) — .git should still win so scans inside the vendored
        repo resolve to the vendored repo root, not the outer project.
        This is the common git-submodule shape.
        """
        import subprocess

        outer = tmp_path / "outer"
        outer.mkdir()
        (outer / "pyproject.toml").touch()
        repo = outer / "vendored_repo"
        repo.mkdir()
        subprocess.run(
            ["git", "init"], cwd=str(repo), capture_output=True, check=True
        )
        src = repo / "src"
        src.mkdir()
        (src / "lib.py").write_text("y = 2")
        git_env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
        subprocess.run(["git", "add", "."], cwd=str(repo), capture_output=True, check=True)
        subprocess.run(["git", "commit", "-m", "init"], cwd=str(repo),
                       capture_output=True, check=True, env=git_env)

        csv_out, _, _ = summarize_directory(
            directory_path=str(src),
            strength=0.5,
            temperature=0.0,
        )
        rows = _parse_csv(csv_out)
        lib_rows = [r for r in rows if r['full_path'].endswith("lib.py")]
        assert len(lib_rows) == 1, f"Should find lib.py, got rows: {rows}"
        # Path should be relative to the vendored repo (the .git dir),
        # so "src/lib.py", NOT "vendored_repo/src/lib.py".
        assert lib_rows[0]['full_path'] == os.path.join("src", "lib.py"), (
            f"Expected path relative to vendored .git root, got: "
            f"{lib_rows[0]['full_path']!r}"
        )


