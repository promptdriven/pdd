"""
Tests for #1063: Deterministic grep verification of Step 6 FIX_LOCATIONS.

The functions under test:
  - _parse_pattern_search: extract PATTERN_SEARCH regex from Step 6 output
  - _sanitize_grep_pattern: validate a grep pattern is safe to execute
  - _extract_match_context: read surrounding code around grep matches
  - _verify_pattern_completeness: run grep, find files missing from FIX_LOCATIONS
  - _parse_classification_evidence: parse NEEDS_FIX / SAFE_EVIDENCE from retry output
"""

import sys
from pathlib import Path

project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import subprocess
import unittest.mock

import pytest

from pdd.agentic_bug_orchestrator import (
    _parse_pattern_search,
    _sanitize_grep_pattern,
    _extract_match_context,
    _verify_pattern_completeness,
    _parse_classification_evidence,
    _merge_fix_locations,
)


# ---------------------------------------------------------------------------
# _parse_pattern_search
# ---------------------------------------------------------------------------


class TestParsePatternSearch:
    """Extract PATTERN_SEARCH regex from Step 6 output."""

    def test_parses_simple_pattern(self):
        output = "Some analysis\nPATTERN_SEARCH: \\.glob\\(\nFIX_LOCATIONS: a.py"
        assert _parse_pattern_search(output) == "\\.glob\\("

    def test_strips_backticks(self):
        output = "PATTERN_SEARCH: `\\.glob\\(`"
        assert _parse_pattern_search(output) == "\\.glob\\("

    def test_returns_none_when_no_marker(self):
        output = "FIX_LOCATIONS: a.py\nSome text without pattern marker"
        assert _parse_pattern_search(output) is None

    def test_returns_none_for_empty_pattern(self):
        output = "PATTERN_SEARCH:   \n"
        assert _parse_pattern_search(output) is None

    def test_takes_first_match(self):
        output = "PATTERN_SEARCH: first_pattern\nPATTERN_SEARCH: second_pattern"
        assert _parse_pattern_search(output) == "first_pattern"

    def test_handles_complex_regex_with_alternation(self):
        output = "PATTERN_SEARCH: requests\\.(get|post|put|delete)\\("
        assert _parse_pattern_search(output) == "requests\\.(get|post|put|delete)\\("

    def test_strips_surrounding_whitespace(self):
        output = "PATTERN_SEARCH:   \\.glob\\(   "
        assert _parse_pattern_search(output) == "\\.glob\\("

    def test_strips_trailing_comment(self):
        output = "PATTERN_SEARCH: \\.glob\\( # broad pattern"
        assert _parse_pattern_search(output) == "\\.glob\\("

    def test_strips_trailing_comment_with_description(self):
        output = "PATTERN_SEARCH: subprocess\\.run\\( # matches all subprocess calls"
        assert _parse_pattern_search(output) == "subprocess\\.run\\("


# ---------------------------------------------------------------------------
# _sanitize_grep_pattern
# ---------------------------------------------------------------------------


class TestSanitizeGrepPattern:
    """Validate and sanitize grep patterns from LLM output."""

    def test_accepts_valid_pattern(self):
        assert _sanitize_grep_pattern("\\.glob\\(") == "\\.glob\\("

    def test_rejects_empty(self):
        assert _sanitize_grep_pattern("") is None

    def test_rejects_too_short(self):
        assert _sanitize_grep_pattern("ab") is None

    def test_rejects_pure_wildcard_dotstar(self):
        assert _sanitize_grep_pattern(".*") is None

    def test_rejects_pure_wildcard_dotplus(self):
        assert _sanitize_grep_pattern(".+") is None

    def test_rejects_shell_semicolon(self):
        assert _sanitize_grep_pattern("pattern; rm -rf /") is None

    def test_rejects_shell_ampersand(self):
        assert _sanitize_grep_pattern("pattern & echo pwned") is None

    def test_rejects_backtick_injection(self):
        assert _sanitize_grep_pattern("pat`whoami`tern") is None

    def test_rejects_dollar_expansion(self):
        assert _sanitize_grep_pattern("pat$HOME") is None

    def test_rejects_newline_injection(self):
        assert _sanitize_grep_pattern("pattern\nrm -rf /") is None

    def test_rejects_carriage_return(self):
        assert _sanitize_grep_pattern("pattern\r") is None

    def test_allows_pipe_for_regex_alternation(self):
        assert _sanitize_grep_pattern("(get|post)") == "(get|post)"

    def test_rejects_too_long(self):
        assert _sanitize_grep_pattern("a" * 201) is None

    def test_accepts_complex_valid_pattern(self):
        pattern = "requests\\.(get|post|put|delete)\\("
        assert _sanitize_grep_pattern(pattern) == pattern

    def test_accepts_sql_pattern(self):
        pattern = "(execute|cursor\\.execute)\\("
        assert _sanitize_grep_pattern(pattern) == pattern


# ---------------------------------------------------------------------------
# _extract_match_context
# ---------------------------------------------------------------------------


class TestExtractMatchContext:
    """Read surrounding code (context window) around grep matches."""

    def test_extracts_context_window(self, tmp_path):
        """30 lines before + 10 lines after the match."""
        # Create a file with 60 lines, match at line 35
        lines = [f"line_{i} = {i}" for i in range(1, 61)]
        lines[34] = "vulnerable = thing.glob(pattern)"  # line 35 (0-indexed: 34)
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [("code.py", 35, "vulnerable = thing.glob(pattern)")]
        result = _extract_match_context(matches, tmp_path)

        assert "code.py" in result
        context = result["code.py"]
        # Should include line 5 (35-30) through line 45 (35+10)
        assert "line_5" in context
        assert "line_45" in context
        # Should NOT include line 1 or line 55
        assert "line_1 =" not in context
        assert "line_55" not in context

    def test_clips_to_file_start(self, tmp_path):
        """Match near start of file — window doesn't go below line 1."""
        lines = [f"line_{i} = {i}" for i in range(1, 21)]
        lines[4] = "vulnerable = thing.glob(pattern)"  # line 5
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [("code.py", 5, "vulnerable = thing.glob(pattern)")]
        result = _extract_match_context(matches, tmp_path)

        context = result["code.py"]
        assert "line_1" in context  # Should start from line 1
        assert "line_15" in context  # 5 + 10

    def test_clips_to_file_end(self, tmp_path):
        """Match near end of file — window doesn't go past EOF."""
        lines = [f"line_{i} = {i}" for i in range(1, 21)]
        lines[18] = "vulnerable = thing.glob(pattern)"  # line 19
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [("code.py", 19, "vulnerable = thing.glob(pattern)")]
        result = _extract_match_context(matches, tmp_path)

        context = result["code.py"]
        assert "line_20" in context  # Last line included
        # No crash from trying to read beyond EOF

    def test_merges_overlapping_windows(self, tmp_path):
        """Two matches close together — windows merge into one."""
        lines = [f"line_{i} = {i}" for i in range(1, 101)]
        lines[29] = "match_one = thing.glob(p1)"   # line 30
        lines[34] = "match_two = thing.glob(p2)"   # line 35
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [
            ("code.py", 30, "match_one = thing.glob(p1)"),
            ("code.py", 35, "match_two = thing.glob(p2)"),
        ]
        result = _extract_match_context(matches, tmp_path)

        # Should be a single merged context, not two separate blocks
        context = result["code.py"]
        assert "match_one" in context
        assert "match_two" in context

    def test_returns_empty_for_missing_file(self, tmp_path):
        """File doesn't exist — returns empty dict for that file."""
        matches = [("nonexistent.py", 10, "some code")]
        result = _extract_match_context(matches, tmp_path)
        assert result.get("nonexistent.py", "") == ""

    def test_includes_line_numbers_in_output(self, tmp_path):
        """Context output includes line numbers for readability."""
        lines = [f"content_{i}" for i in range(1, 11)]
        lines[4] = "vulnerable_call()"  # line 5
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [("code.py", 5, "vulnerable_call()")]
        result = _extract_match_context(matches, tmp_path)

        context = result["code.py"]
        # Line numbers should appear in the output
        assert "5" in context

    def test_cross_line_vulnerability_above_match(self, tmp_path):
        """KEY TEST: Vulnerability 18 lines above the grep match is captured.

        This is the agentic_update.py case — the grep matches .glob(pattern)
        at line 35, but the vulnerability is pattern = f"test_{stem}*" at
        line 17 (18 lines above). The 30-line context window must include it.
        """
        lines = ["# filler"] * 50
        lines[16] = 'pattern = f"test_{stem}*{suffix}"'   # line 17: vulnerability
        lines[34] = "for p in dir.glob(pattern):"          # line 35: grep match
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [("code.py", 35, "for p in dir.glob(pattern):")]
        result = _extract_match_context(matches, tmp_path, context_before=30)

        context = result["code.py"]
        # The vulnerability at line 17 MUST be visible in the context
        assert 'f"test_{stem}' in context

    def test_context_below_match(self, tmp_path):
        """Vulnerability 5 lines below the match is captured."""
        lines = ["# filler"] * 30
        lines[9] = "result = db.execute(query)"   # line 10: grep match
        lines[14] = "query = f'SELECT * FROM {table}'"  # line 15: vulnerability
        (tmp_path / "code.py").write_text("\n".join(lines) + "\n")

        matches = [("code.py", 10, "result = db.execute(query)")]
        result = _extract_match_context(matches, tmp_path, context_after=10)

        context = result["code.py"]
        assert "SELECT * FROM" in context

    def test_multiple_files(self, tmp_path):
        """Matches in different files produce separate contexts."""
        for name in ["a.py", "b.py"]:
            (tmp_path / name).write_text("line1\nline2\nvulnerable()\nline4\n")

        matches = [
            ("a.py", 3, "vulnerable()"),
            ("b.py", 3, "vulnerable()"),
        ]
        result = _extract_match_context(matches, tmp_path)

        assert "a.py" in result
        assert "b.py" in result


# ---------------------------------------------------------------------------
# _verify_pattern_completeness
# ---------------------------------------------------------------------------


class TestVerifyPatternCompleteness:
    """Run deterministic grep and find files missing from FIX_LOCATIONS."""

    def test_finds_unclassified_files(self, tmp_path):
        """Grep finds files not in FIX_LOCATIONS."""
        for name in ["a.py", "b.py", "c.py", "d.py", "e.py"]:
            (tmp_path / name).write_text("x = thing.glob(pattern)\n")

        fix_locs = ["a.py", "b.py", "c.py"]
        unclassified, summary = _verify_pattern_completeness(
            "\\.glob\\(", fix_locs, tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        assert unclassified_files == {"d.py", "e.py"}
        assert "2 unclassified" in summary

    def test_returns_structured_tuples(self, tmp_path):
        """Results are (filepath, line_number, content) tuples."""
        (tmp_path / "code.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        assert len(unclassified) >= 1
        filepath, line_num, content = unclassified[0]
        assert filepath == "code.py"
        assert isinstance(line_num, int)
        assert "glob" in content

    def test_all_files_classified(self, tmp_path):
        """All grep results in FIX_LOCATIONS — no unclassified."""
        for name in ["a.py", "b.py"]:
            (tmp_path / name).write_text("x = thing.glob(pattern)\n")

        unclassified, summary = _verify_pattern_completeness(
            "\\.glob\\(", ["a.py", "b.py"], tmp_path
        )
        assert unclassified == []
        assert "0 unclassified" in summary

    def test_rejects_invalid_pattern(self, tmp_path):
        """Invalid pattern returns empty list."""
        unclassified, summary = _verify_pattern_completeness(
            ".*", ["a.py"], tmp_path
        )
        assert unclassified == []
        assert "rejected" in summary.lower()

    def test_handles_grep_timeout(self, tmp_path):
        """Timeout returns empty results gracefully."""
        with unittest.mock.patch(
            "pdd.agentic_bug_orchestrator.subprocess.run",
            side_effect=subprocess.TimeoutExpired("grep", 30),
        ):
            unclassified, summary = _verify_pattern_completeness(
                "\\.glob\\(", ["a.py"], tmp_path
            )
        assert unclassified == []
        assert "timed out" in summary.lower()

    def test_invalid_regex_returns_error_not_empty(self, tmp_path):
        """grep exit code 2 (invalid regex) must return an error summary,
        NOT silently return empty results (which would suppress the safety net)."""
        (tmp_path / "foo.py").write_text("x = thing.glob(pattern)\n")

        # '[unclosed' is an invalid POSIX extended regex — grep -E returns exit code 2
        unclassified, summary = _verify_pattern_completeness(
            "[unclosed", [], tmp_path
        )
        assert unclassified == []
        # Must mention rejection/error — NOT "Grep found 0 files"
        assert "rejected" in summary.lower() or "invalid" in summary.lower() or "error" in summary.lower(), (
            f"Expected error summary for invalid regex, got: {summary!r}"
        )

    def test_normalizes_dot_slash_paths(self, tmp_path):
        """./pdd/foo.py from grep matches pdd/foo.py in FIX_LOCATIONS."""
        sub = tmp_path / "pdd"
        sub.mkdir()
        (sub / "foo.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", ["pdd/foo.py"], tmp_path
        )
        assert unclassified == []

    def test_returns_all_unclassified_files(self, tmp_path):
        """All unclassified files are returned (no cap in grep function)."""
        for i in range(60):
            (tmp_path / f"file_{i}.py").write_text("x = thing.glob(pattern)\n")

        unclassified, summary = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        unique_files = {m[0] for m in unclassified}
        assert len(unique_files) == 60
        assert "60 unclassified" in summary

    def test_multi_match_per_file_preserved(self, tmp_path):
        """A file with multiple matches returns ALL match locations, not just the first."""
        (tmp_path / "multi.py").write_text(
            "line1 = safe_literal.glob('*.txt')\n"
            "line2 = x\n"
            "line3 = user_input.glob(pattern)\n"
        )

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        multi_matches = [m for m in unclassified if m[0] == "multi.py"]
        assert len(multi_matches) == 2, (
            f"Expected 2 matches for multi.py, got {len(multi_matches)}: {multi_matches}"
        )
        line_nums = {m[1] for m in multi_matches}
        assert line_nums == {1, 3}

    def test_full_path_in_fix_locs_does_not_suppress_other_dir(self, tmp_path):
        """pdd/utils.py in FIX_LOCATIONS must NOT suppress tests/utils.py."""
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "utils.py").write_text("x = thing.glob(pattern)\n")
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "utils.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", ["pdd/utils.py"], tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        assert "tests/utils.py" in unclassified_files, (
            f"tests/utils.py was suppressed by pdd/utils.py in FIX_LOCATIONS. "
            f"Found: {unclassified_files}"
        )
        assert "pdd/utils.py" not in unclassified_files

    def test_bare_name_in_fix_locs_covers_all_basenames(self, tmp_path):
        """Bare 'utils.py' in FIX_LOCATIONS covers pdd/utils.py and tests/utils.py."""
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "utils.py").write_text("x = thing.glob(pattern)\n")
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "utils.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", ["utils.py"], tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        # Bare name covers both
        assert "pdd/utils.py" not in unclassified_files
        assert "tests/utils.py" not in unclassified_files

    def test_excludes_git_directory(self, tmp_path):
        """Files inside .git/ are not included in grep results."""
        git_dir = tmp_path / ".git" / "hooks"
        git_dir.mkdir(parents=True)
        (git_dir / "pre-commit.py").write_text("x = thing.glob(pattern)\n")
        (tmp_path / "real.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        assert "real.py" in unclassified_files
        assert not any(".git" in f for f in unclassified_files)

    def test_excludes_node_modules(self, tmp_path):
        """Files inside node_modules/ are excluded."""
        nm = tmp_path / "node_modules" / "pkg"
        nm.mkdir(parents=True)
        (nm / "index.js").write_text("thing.glob(pattern)\n")
        (tmp_path / "real.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        assert "real.py" in unclassified_files
        assert not any("node_modules" in f for f in unclassified_files)

    def test_excludes_venv(self, tmp_path):
        """Files inside .venv/ are excluded."""
        venv = tmp_path / ".venv" / "lib"
        venv.mkdir(parents=True)
        (venv / "site.py").write_text("x = thing.glob(pattern)\n")
        (tmp_path / "real.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        assert "real.py" in unclassified_files
        assert not any(".venv" in f for f in unclassified_files)

    def test_excludes_pdd_worktrees(self, tmp_path):
        """Files inside .pdd/ worktrees are excluded."""
        pdd_dir = tmp_path / ".pdd" / "worktrees" / "fix-issue-42"
        pdd_dir.mkdir(parents=True)
        (pdd_dir / "stale.py").write_text("x = thing.glob(pattern)\n")
        (tmp_path / "real.py").write_text("x = thing.glob(pattern)\n")

        unclassified, _ = _verify_pattern_completeness(
            "\\.glob\\(", [], tmp_path
        )
        unclassified_files = {m[0] for m in unclassified}
        assert "real.py" in unclassified_files
        assert not any(".pdd" in f for f in unclassified_files)


# ---------------------------------------------------------------------------
# _parse_classification_evidence
# ---------------------------------------------------------------------------


class TestParseClassificationEvidence:
    """Parse NEEDS_FIX / SAFE_EVIDENCE markers from retry LLM output."""

    def test_parses_needs_fix(self):
        output = "Analysis...\nNEEDS_FIX: pdd/agentic_update.py\nMore text"
        needs_fix, safe = _parse_classification_evidence(output)
        assert "pdd/agentic_update.py" in needs_fix

    def test_parses_safe_evidence(self):
        output = "SAFE_EVIDENCE: pdd/safe_file.py | 42 | uses hardcoded literal string"
        needs_fix, safe = _parse_classification_evidence(output)
        assert "pdd/safe_file.py" in safe
        assert "pdd/safe_file.py" not in needs_fix

    def test_multiple_classifications(self):
        output = (
            "NEEDS_FIX: file_a.py\n"
            "SAFE_EVIDENCE: file_b.py | 10 | hardcoded\n"
            "NEEDS_FIX: file_c.py\n"
            "SAFE_EVIDENCE: file_d.py | 20 | already escaped\n"
        )
        needs_fix, safe = _parse_classification_evidence(output)
        assert set(needs_fix) == {"file_a.py", "file_c.py"}
        assert set(safe) == {"file_b.py", "file_d.py"}

    def test_strips_backticks(self):
        output = "NEEDS_FIX: `pdd/code.py`"
        needs_fix, _ = _parse_classification_evidence(output)
        assert "pdd/code.py" in needs_fix

    def test_strips_whitespace(self):
        output = "NEEDS_FIX:   pdd/code.py   "
        needs_fix, _ = _parse_classification_evidence(output)
        assert "pdd/code.py" in needs_fix

    def test_unmentioned_file_not_in_either_list(self):
        """A file not mentioned in the output is absent from both lists."""
        output = "NEEDS_FIX: file_a.py\nSAFE_EVIDENCE: file_b.py | 5 | safe"
        needs_fix, safe = _parse_classification_evidence(output)
        assert "file_c.py" not in needs_fix
        assert "file_c.py" not in safe

    def test_empty_output_returns_empty_lists(self):
        needs_fix, safe = _parse_classification_evidence("")
        assert needs_fix == []
        assert safe == []


# ---------------------------------------------------------------------------
# Merge semantics (integration-level)
# ---------------------------------------------------------------------------


class TestMergeSemantics:
    """Verify that _merge_fix_locations uses correct union semantics.

    Tests call the REAL production function — not a local copy.
    Original FIX_LOCATIONS must NEVER be removed by the retry.
    New NEEDS_FIX files are added. Unclassified files default to NEEDS_FIX.
    """

    def test_original_fix_locations_never_removed(self):
        """Even if retry marks an original file as SAFE, it stays."""
        original = ["a.py", "b.py", "c.py"]
        needs_fix = []
        safe = ["b.py"]  # retry says b.py is safe
        unclassified = []

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        # b.py is STILL in merged because it was in original
        assert "b.py" in merged
        assert set(merged) == {"a.py", "b.py", "c.py"}

    def test_new_needs_fix_added(self):
        """Retry identifies new files as NEEDS_FIX — they are added."""
        original = ["a.py", "b.py"]
        needs_fix = ["d.py", "e.py"]
        safe = []
        unclassified = []

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert set(merged) == {"a.py", "b.py", "d.py", "e.py"}

    def test_unclassified_default_to_needs_fix(self):
        """Files not mentioned in retry output default to NEEDS_FIX."""
        original = ["a.py"]
        needs_fix = []
        safe = []
        unclassified = ["x.py", "y.py"]  # grep found these, retry didn't mention them

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert "x.py" in merged
        assert "y.py" in merged

    def test_safe_files_excluded_from_new_additions(self):
        """Files with SAFE_EVIDENCE are NOT added (but originals are kept)."""
        original = ["a.py"]
        needs_fix = ["c.py"]
        safe = ["b.py"]  # proven safe by retry
        unclassified = []

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert "b.py" not in merged  # not in original, marked safe → excluded
        assert set(merged) == {"a.py", "c.py"}

    def test_basename_normalization_no_duplicate(self):
        """LLM returns 'agentic_update.py', grep returns 'pdd/agentic_update.py'.
        They are the same file — the merge must not add both."""
        original = ["pdd/sync_main.py"]
        # Grep found pdd/agentic_update.py as unclassified
        unclassified = ["pdd/agentic_update.py"]
        # Retry LLM classified it using just the basename
        needs_fix = ["agentic_update.py"]
        safe = []

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        # Should contain exactly ONE entry for agentic_update, not both paths
        agentic_entries = [f for f in merged if "agentic_update" in f]
        assert len(agentic_entries) == 1, (
            f"Duplicate path entries for same file: {agentic_entries}"
        )

    def test_basename_normalization_safe_excludes_full_path(self):
        """LLM marks 'safe_util.py' as SAFE. Grep found 'pdd/safe_util.py' as
        unclassified. The full path must NOT be added to merged."""
        original = ["a.py"]
        unclassified = ["pdd/safe_util.py"]  # grep full path
        needs_fix = []
        safe = ["safe_util.py"]  # LLM basename

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert "pdd/safe_util.py" not in merged
        assert "safe_util.py" not in merged
        assert set(merged) == {"a.py"}

    def test_basename_collision_different_dirs_both_added(self):
        """tests/utils.py and pdd/utils.py are different files — both must be added."""
        original = ["a.py"]
        needs_fix = ["tests/utils.py", "pdd/utils.py"]
        safe = []
        unclassified = []

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert "tests/utils.py" in merged
        assert "pdd/utils.py" in merged
        assert len(merged) == 3

    def test_basename_collision_unclassified_both_added(self):
        """Two unclassified files with the same basename in different dirs."""
        original = ["a.py"]
        needs_fix = []
        safe = []
        unclassified = ["pdd/__init__.py", "tests/__init__.py"]

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert "pdd/__init__.py" in merged
        assert "tests/__init__.py" in merged

    def test_bare_name_with_multiple_full_path_matches(self):
        """LLM returns bare 'utils.py' as NEEDS_FIX. Grep finds pdd/utils.py
        AND tests/utils.py as unclassified. Both must appear in merged —
        the bare classification is ambiguous when multiple files share the basename."""
        original = ["a.py"]
        needs_fix = ["utils.py"]  # bare name from LLM
        safe = []
        unclassified = ["pdd/utils.py", "tests/utils.py"]

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert "pdd/utils.py" in merged or "utils.py" in merged
        assert "tests/utils.py" in merged
        # Must have at least: a.py + both utils paths
        utils_entries = [f for f in merged if "utils" in f]
        assert len(utils_entries) >= 2, (
            f"Expected both utils.py files, got: {utils_entries}"
        )

    def test_bare_safe_with_multiple_full_path_unclassified(self):
        """LLM marks bare 'config.py' as SAFE. Grep finds pdd/config.py and
        tests/config.py. Since the classification is ambiguous, both should
        get the conservative NEEDS_FIX default."""
        original = ["a.py"]
        needs_fix = []
        safe = ["config.py"]  # bare name — which config.py?
        unclassified = ["pdd/config.py", "tests/config.py"]

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        # Both should be added (conservative default) since the bare SAFE
        # classification is ambiguous
        assert "pdd/config.py" in merged
        assert "tests/config.py" in merged

    def test_retry_failure_applies_conservative_default(self):
        """When retry fails, all unclassified files are added (needs_fix=[], safe=[])."""
        original = ["a.py", "b.py"]
        # Retry failed — no classification available
        needs_fix = []
        safe = []
        unclassified = ["x.py", "y.py", "z.py"]

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        # All originals preserved
        assert "a.py" in merged
        assert "b.py" in merged
        # All unclassified added via conservative default
        assert "x.py" in merged
        assert "y.py" in merged
        assert "z.py" in merged
        assert len(merged) == 5

    def test_full_scenario(self):
        """Complete scenario matching the #1048 case.

        Original Step 6 found 6 files. Grep found 1 more (agentic_update.py).
        The retry should classify agentic_update.py as NEEDS_FIX and add it.
        """
        original = [
            "pdd/sync_main.py",
            "pdd/sync_determine_operation.py",
            "pdd/sync_order.py",
            "pdd/construct_paths.py",
            "pdd/code_generator_main.py",
            "pdd/agentic_change_orchestrator.py",
        ]
        needs_fix = ["pdd/agentic_update.py"]
        safe = []
        unclassified = []

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified)
        assert len(merged) == 7
        assert "pdd/agentic_update.py" in merged
        # All originals preserved
        for f in original:
            assert f in merged


# ---------------------------------------------------------------------------
# Non-pattern bugs (no regression)
# ---------------------------------------------------------------------------


class TestNoPatternSearchRegression:
    """Step 6 output without PATTERN_SEARCH marker — no verification runs."""

    def test_no_pattern_search_returns_none(self):
        """Standard Step 6 output for a single-site bug."""
        output = (
            "## Root Cause Analysis\n"
            "The bug is in sync_main.py line 42.\n"
            "FIX_LOCATIONS: pdd/sync_main.py\n"
        )
        assert _parse_pattern_search(output) is None
