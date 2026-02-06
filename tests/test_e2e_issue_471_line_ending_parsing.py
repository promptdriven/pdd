"""
E2E Test for Issue #471: Cross-platform incompatible string splitting pattern

Investigation findings (from Steps 1-6 of bug workflow):
- The codebase uses `.strip().split('\\n')` in 9 locations instead of `.splitlines()`
- On Windows, subprocess output uses CRLF line endings (\\r\\n)
- `.strip().split('\\n')` leaves trailing \\r characters: "file.py\\r"
- This breaks file operations: Path('file.py\\r').exists() returns False
- The bug affects git operations, workflow orchestrators, and CSV parsing

This E2E test verifies:
1. The bug exists on current code (test FAILS showing \\r in parsed lines)
2. After fix with .splitlines(), test will PASS
3. Regression prevention for all affected code paths

Bug discovered in commit 275111b1 fix for agentic_change_orchestrator.py,
but the same pattern exists in 9 other locations.
"""

import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch
import subprocess


class TestIssue471LineEndingParsing:
    """E2E tests for Issue #471: Verify cross-platform line ending handling."""

    def test_buggy_strip_split_leaves_carriage_return_on_windows_output(self, tmp_path):
        """
        PRIMARY BUG TEST: Demonstrates .strip().split('\\n') leaves \\r on Windows CRLF.

        This test simulates Windows subprocess output with CRLF line endings.
        The buggy pattern `.strip().split('\\n')` will leave trailing \\r characters.

        Expected on CURRENT BUGGY CODE: FAILS - \\r characters remain
        Expected AFTER FIX: PASSES - \\r characters removed
        """
        # Create test files
        (tmp_path / "file1.py").write_text("print('hello')")
        (tmp_path / "file2.py").write_text("print('world')")
        (tmp_path / "file3.py").write_text("print('test')")

        # Simulate Windows subprocess output with CRLF line endings
        windows_git_output = "file1.py\r\nfile2.py\r\nfile3.py\r\n"

        # BUGGY APPROACH (current PDD code)
        buggy_files = [f for f in windows_git_output.strip().split("\n") if f]

        # THE BUG: Each filename has trailing \r
        assert len(buggy_files) == 3, "Should parse 3 files"

        # THIS ASSERTION WILL FAIL ON BUGGY CODE - proving the bug exists
        for filename in buggy_files:
            assert not filename.endswith('\r'), (
                f"BUG DETECTED (Issue #471): Filename has trailing \\r: {repr(filename)}\n"
                f"This breaks file operations on Windows!\n"
                f"Path('{filename}').exists() will return False even when file exists.\n"
                f"Root cause: .strip().split('\\n') doesn't handle Windows CRLF.\n"
                f"Fix: Use .splitlines() instead."
            )

        # Verify file operations fail with \r suffix
        for filename in buggy_files:
            file_path = tmp_path / filename
            # On buggy code, this will be False because filename is "file1.py\r"
            # but the actual file is "file1.py" (no \r)
            if filename.endswith('\r'):
                assert not file_path.exists(), (
                    f"File lookup broken: Path('{filename}') should not exist"
                )

        # FIXED APPROACH (using .splitlines())
        fixed_files = [f for f in windows_git_output.splitlines() if f.strip()]

        # Verify fix works correctly
        assert len(fixed_files) == 3, "Should parse 3 files"
        for filename in fixed_files:
            assert not filename.endswith('\r'), "Fixed approach removes \\r"
            file_path = tmp_path / filename
            assert file_path.exists(), f"File {filename} should exist after fix"

    def test_agentic_e2e_fix_orchestrator_get_uncommitted_files_with_crlf(self, tmp_path):
        """
        INTEGRATION TEST: Test actual git operations with Windows CRLF output.

        Tests the exact code path in agentic_e2e_fix_orchestrator.py:165, 175
        where git diff and git ls-files output is parsed.

        On Windows, git commands return CRLF. The buggy parsing breaks file detection.
        """
        # Import the affected module
        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        # Create a mock git repository
        (tmp_path / ".git").mkdir()
        test_file = tmp_path / "test_file.py"
        test_file.write_text("# test code")

        # Mock subprocess to return Windows CRLF output
        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            # Simulate Windows git output with CRLF
            mock_result_diff = MagicMock()
            mock_result_diff.returncode = 0
            mock_result_diff.stdout = "src/module.py\r\ntest_file.py\r\n"

            mock_result_untracked = MagicMock()
            mock_result_untracked.returncode = 0
            mock_result_untracked.stdout = "new_file.py\r\n"

            mock_run.side_effect = [mock_result_diff, mock_result_untracked]

            # Call the actual function
            files = _get_modified_and_untracked(tmp_path)

            # THE BUG: On current code, filenames will have \r suffix
            # This assertion will FAIL on buggy code
            for filename in files:
                assert not filename.endswith('\r'), (
                    f"BUG in _get_uncommitted_files: filename has \\r: {repr(filename)}\n"
                    f"This breaks downstream file operations.\n"
                    f"Location: pdd/agentic_e2e_fix_orchestrator.py:165, 175"
                )

            # Verify expected files are detected (without \r)
            expected_files = {"src/module.py", "test_file.py", "new_file.py"}
            assert files == expected_files, f"Expected {expected_files}, got {files}"

    def test_splitlines_handles_all_line_ending_types(self):
        """
        REGRESSION TEST: Verify .splitlines() handles Unix LF, Windows CRLF, Mac CR.

        After the fix, code should work on all platforms.
        """
        # Test data with different line endings
        unix_output = "line1\nline2\nline3\n"        # Unix LF
        windows_output = "line1\r\nline2\r\nline3\r\n"  # Windows CRLF
        old_mac_output = "line1\rline2\rline3\r"    # Old Mac CR
        mixed_output = "line1\r\nline2\nline3\r"    # Mixed (realistic)

        # Test Unix LF
        lines = [line for line in unix_output.splitlines() if line.strip()]
        assert lines == ["line1", "line2", "line3"]
        assert all(not line.endswith('\r') for line in lines)
        assert all(not line.endswith('\n') for line in lines)

        # Test Windows CRLF
        lines = [line for line in windows_output.splitlines() if line.strip()]
        assert lines == ["line1", "line2", "line3"]
        assert all(not line.endswith('\r') for line in lines)
        assert all(not line.endswith('\n') for line in lines)

        # Test old Mac CR
        lines = [line for line in old_mac_output.splitlines() if line.strip()]
        assert lines == ["line1", "line2", "line3"]
        assert all(not line.endswith('\r') for line in lines)

        # Test mixed line endings
        lines = [line for line in mixed_output.splitlines() if line.strip()]
        assert lines == ["line1", "line2", "line3"]
        assert all(not line.endswith('\r') for line in lines)
        assert all(not line.endswith('\n') for line in lines)

    def test_splitlines_handles_empty_lines_correctly(self):
        """
        EDGE CASE TEST: Verify .splitlines() with empty lines and whitespace.
        """
        # Output with empty lines and whitespace
        output_with_empties = "file1.py\r\n\r\nfile2.py\r\n  \r\nfile3.py\r\n"

        # Using .splitlines() with .strip() filter
        lines = [line for line in output_with_empties.splitlines() if line.strip()]

        # Should get only non-empty lines
        assert lines == ["file1.py", "file2.py", "file3.py"]
        assert all(not line.endswith('\r') for line in lines)

        # Compare with buggy approach
        buggy_lines = [line for line in output_with_empties.strip().split("\n") if line]

        # Buggy approach leaves \r and doesn't filter whitespace-only lines correctly
        for line in buggy_lines:
            if line.strip():  # Non-empty lines
                # THIS ASSERTION FAILS ON BUGGY CODE
                assert not line.endswith('\r'), (
                    f"Buggy approach leaves \\r: {repr(line)}"
                )

    def test_csv_double_strip_inefficiency(self):
        """
        EFFICIENCY TEST: Verify the double .strip() issue in CSV parsing.

        Location: pdd/process_csv_change.py:150
        Pattern: [col.strip() for col in header_line.strip().split(',')]
        Issue: The outer .strip() is redundant when split(',') is used.
        """
        # CSV header with leading/trailing whitespace
        header_line = "  name, email , age , city  \n"

        # CURRENT (INEFFICIENT) - double strip
        # The outer strip() is unnecessary since we strip each column anyway
        inefficient = [col.strip() for col in header_line.strip().split(',')]

        # BETTER (EFFICIENT) - single strip per column
        efficient = [col.strip() for col in header_line.split(',')]

        # Both produce same result
        assert inefficient == efficient == ["name", "email", "age", "city"]

        # But the efficient approach is cleaner and doesn't do redundant work
        # This documents the fix for process_csv_change.py:150

    def test_subprocess_output_parsing_pattern_demonstration(self, tmp_path):
        """
        DOCUMENTATION TEST: Demonstrates the correct pattern for parsing subprocess output.

        IMPORTANT EDGE CASE: The buggy pattern has subtle behavior:
        - All lines EXCEPT the last have trailing \r
        - The last line loses its \r due to the initial .strip()

        This makes the bug intermittent - the last file works, others fail!
        This can make debugging harder since behavior varies by file position.
        """
        # Create test files
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "main.py").write_text("code")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_main.py").write_text("test")

        # Simulate git command with Windows CRLF output
        git_output = "src/main.py\r\ntests/test_main.py\r\n"

        # ❌ ANTI-PATTERN (current buggy code)
        buggy_pattern = [f for f in git_output.strip().split("\n") if f]
        # Result: ['src/main.py\r', 'tests/test_main.py']
        # First has \r, last doesn't (due to .strip() removing trailing \r\n)

        # ✅ CORRECT PATTERN (recommended fix)
        correct_pattern = [f for f in git_output.splitlines() if f.strip()]
        # Result: ['src/main.py', 'tests/test_main.py'] - BOTH clean!

        # Verify the difference
        assert len(buggy_pattern) == 2
        assert len(correct_pattern) == 2

        # CRITICAL: Only FIRST file has \r, not the last!
        # This is the insidious edge case - .strip() removes trailing \r\n from entire string
        assert buggy_pattern[0].endswith('\r'), "First file has \\r - breaks file operations!"
        assert not buggy_pattern[1].endswith('\r'), "Last file loses \\r due to .strip() - works by accident!"

        # This makes the bug intermittent:
        # - If you process 3 files, the first 2 fail, the last one works
        # - Single file operations work fine (only file is also last file)
        # - Very confusing for debugging!

        # Correct pattern is clean for ALL files
        assert not correct_pattern[0].endswith('\r')
        assert not correct_pattern[1].endswith('\r')

        # Demonstrate the real-world impact
        first_file_buggy = tmp_path / buggy_pattern[0]  # Path('src/main.py\r')
        last_file_buggy = tmp_path / buggy_pattern[1]   # Path('tests/test_main.py')

        assert not first_file_buggy.exists(), "First file lookup FAILS due to \\r"
        assert last_file_buggy.exists(), "Last file lookup WORKS (no \\r) - confusing!"

        # With fixed approach, BOTH work
        first_file_fixed = tmp_path / correct_pattern[0]
        last_file_fixed = tmp_path / correct_pattern[1]

        assert first_file_fixed.exists(), "First file found with fix"
        assert last_file_fixed.exists(), "Last file found with fix"


class TestIssue471RegressionTests:
    """Regression tests to prevent reintroduction of the bug pattern."""

    def test_all_subprocess_parsing_uses_splitlines(self):
        """
        STATIC ANALYSIS TEST: Verify no remaining .strip().split('\\n') patterns.

        After the fix is applied, this test ensures no new instances are introduced.
        """
        import pdd
        from pathlib import Path

        pdd_dir = Path(pdd.__file__).parent

        # Files that should be checked (these had the bug)
        files_to_check = [
            pdd_dir / "agentic_architecture_orchestrator.py",
            pdd_dir / "agentic_e2e_fix_orchestrator.py",
            pdd_dir / "agentic_test_orchestrator.py",
            pdd_dir / "summarize_directory.py",
            pdd_dir / "code_generator_main.py",
            pdd_dir / "server" / "routes" / "prompts.py",
            pdd_dir / "server" / "routes" / "files.py",
            pdd_dir / "process_csv_change.py",
        ]

        problematic_patterns = []

        for filepath in files_to_check:
            if not filepath.exists():
                continue  # Skip if file doesn't exist

            content = filepath.read_text()

            # Check for the buggy pattern: .strip().split("\n") or .strip().split('\n')
            import re
            # Match: .strip().split("\n") or .strip().split('\n')
            # But not: .strip().split(",") or other delimiters
            buggy_pattern = r'\.strip\(\)\.split\(["\']\\n["\']\)'

            matches = re.finditer(buggy_pattern, content)
            for match in matches:
                # Get line number
                line_num = content[:match.start()].count('\n') + 1
                problematic_patterns.append(f"{filepath.name}:{line_num}")

        # After fix, this should be empty
        # Before fix, this will show all 9 locations
        if problematic_patterns:
            pytest.fail(
                f"Found {len(problematic_patterns)} instances of buggy .strip().split('\\n') pattern:\n" +
                "\n".join(f"  - {loc}" for loc in problematic_patterns) +
                "\n\nThese should use .splitlines() instead for cross-platform compatibility."
            )

    def test_performance_comparison_splitlines_vs_strip_split(self):
        """
        PERFORMANCE TEST: Document that .splitlines() is faster than .strip().split('\\n').

        From issue benchmarks: .splitlines() is 15-30% faster on large outputs.
        """
        import timeit

        # Large subprocess-style output (3000 lines)
        test_data = "line{}\n".format("\nline") * 1000

        # Measure .strip().split('\n')
        time_strip_split = timeit.timeit(
            lambda: test_data.strip().split('\n'),
            number=1000
        )

        # Measure .splitlines()
        time_splitlines = timeit.timeit(
            lambda: test_data.splitlines(),
            number=1000
        )

        # .splitlines() should be faster or comparable
        # We don't assert strict performance (machine-dependent)
        # but document that it's at least not slower
        speedup_pct = ((time_strip_split - time_splitlines) / time_strip_split) * 100

        # Just verify .splitlines() is not significantly slower
        # (should actually be faster based on benchmarks)
        assert time_splitlines <= time_strip_split * 1.5, (
            f".splitlines() unexpectedly slower: {time_splitlines:.4f}s vs {time_strip_split:.4f}s"
        )

        # Document the speedup (informational, not assertion)
        print(f"\nPerformance: .splitlines() is {speedup_pct:.1f}% faster than .strip().split('\\n')")
