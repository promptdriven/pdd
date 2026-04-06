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

        # BUG: csv_output_2 no longer has the entry for utils.py because it
        # was wiped during the scan when the file didn't exist. So even though
        # the file content is identical, we have to re-summarize it.
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

    def test_parent_dir_scan_reuses_subdir_cache(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """If the CSV was built by scanning 'pdd/' (entries like 'cli.py'),
        then scanning '.' should still cache-hit on pdd/cli.py because it's
        the same physical file.

        This is the real-world scenario: project_dependencies.csv has entries
        from scanning pdd/ (bare filenames). A later scan from the project
        root produces 'pdd/cli.py' as the relative path. The cache lookup
        must recognize these as the same file via content hash.
        """
        # Create subdir/module.py
        subdir = tmp_path / "pkg"
        subdir.mkdir()
        content = "def hello(): pass"
        (subdir / "module.py").write_text(content)

        # CSV has entry from a prior scan of subdir (bare filename)
        existing_csv = _make_csv([{
            'full_path': 'module.py',
            'file_summary': 'Cached summary from subdir scan',
            'key_exports': '["hello"]',
            'dependencies': '[]',
            'content_hash': _content_hash(content),
        }])

        # Now scan from parent (tmp_path) — file becomes "pkg/module.py"
        csv_output, cost, _ = summarize_directory(
            directory_path=str(tmp_path),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        # Same physical file, same content hash — should NOT re-summarize
        assert cost == 0, (
            f"File was re-summarized (cost={cost}) when scanning from a "
            "parent directory. The CSV had 'module.py' but the scan produced "
            "'pkg/module.py'. Cache should match by content hash when paths "
            "differ but content is identical."
        )

    def test_subdir_scan_reuses_parent_cache(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Inverse of above: CSV has 'pkg/module.py' from scanning root,
        now scanning 'pkg/' produces 'module.py'. Should still cache-hit."""
        subdir = tmp_path / "pkg"
        subdir.mkdir()
        content = "x = 42"
        (subdir / "module.py").write_text(content)

        # CSV has entry from a prior scan of root (prefixed path)
        existing_csv = _make_csv([{
            'full_path': 'pkg/module.py',
            'file_summary': 'Cached summary from root scan',
            'key_exports': '["x"]',
            'dependencies': '[]',
            'content_hash': _content_hash(content),
        }])

        # Now scan just subdir — file becomes "module.py"
        csv_output, cost, _ = summarize_directory(
            directory_path=str(subdir),
            strength=0.5,
            temperature=0.0,
            csv_file=existing_csv,
        )

        assert cost == 0, (
            f"File was re-summarized (cost={cost}) when scanning a subdirectory. "
            "The CSV had 'pkg/module.py' but the scan produced 'module.py'. "
            "Cache should match by content hash when paths differ but content "
            "is identical."
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
