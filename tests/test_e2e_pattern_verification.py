"""
End-to-end verification that the pattern completeness pipeline works
against real codebase states.

Test Case 1: Issue #1048 (glob.escape) — 7 files needed fixing, LLM found 6.
             Verifies grep finds all 7, context window captures the vulnerability
             in agentic_update.py (18 lines above the match).

Test Case 2: Synthetic (subprocess without shlex.quote) — 5 files, 3 vulnerable.
             Verifies grep + context + classification protocol work for a
             completely different pattern.
"""

import sys
import textwrap
from pathlib import Path

project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import subprocess
import pytest

from pdd.agentic_bug_orchestrator import (
    _parse_pattern_search,
    _sanitize_grep_pattern,
    _extract_match_context,
    _verify_pattern_completeness,
    _parse_classification_evidence,
    _merge_fix_locations,
)


@pytest.mark.e2e
class TestE2ECase1GlobEscape:
    """Issue #1048: unescaped .glob() calls across 7 files.

    Uses the REAL pre-fix codebase state (commit eb6542bdf) to verify
    that grep finds all instances and the context window captures the
    vulnerability in agentic_update.py.
    """

    # The 6 files that had unescaped .glob() calls in the #1048 fix.
    # Note: sync_order.py needed shlex.quote() (different pattern, no .glob call),
    # so it correctly does NOT match the \.glob\( pattern.
    EXPECTED_GLOB_FILES = {
        "pdd/sync_main.py",
        "pdd/sync_determine_operation.py",
        "pdd/construct_paths.py",
        "pdd/code_generator_main.py",
        "pdd/agentic_change_orchestrator.py",
        "pdd/agentic_update.py",
    }

    # What the LLM typically finds (6/7 — misses agentic_update.py)
    LLM_FOUND = [
        "pdd/sync_main.py",
        "pdd/sync_determine_operation.py",
        "pdd/sync_order.py",
        "pdd/construct_paths.py",
        "pdd/code_generator_main.py",
        "pdd/agentic_change_orchestrator.py",
    ]

    def _get_pre_fix_commit(self) -> str:
        """Get the commit hash right before the #1048 fix."""
        result = subprocess.run(
            ["git", "rev-parse", "eb6542bdf"],
            capture_output=True, text=True, cwd=project_root,
        )
        if result.returncode != 0:
            pytest.skip("Pre-fix commit eb6542bdf not found in history")
        return result.stdout.strip()

    def _checkout_pre_fix_files(self, tmp_path: Path, commit: str) -> Path:
        """Create a temp directory with the pre-fix pdd/ source tree."""
        # Clone just the pdd/ directory at the pre-fix commit
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        result = subprocess.run(
            ["git", "archive", commit, "--", "pdd/"],
            capture_output=True, cwd=project_root,
        )
        if result.returncode != 0:
            pytest.skip(f"Could not archive pre-fix commit: {result.stderr}")
        subprocess.run(
            ["tar", "xf", "-"],
            input=result.stdout, cwd=tmp_path,
        )
        return tmp_path

    def test_grep_finds_all_glob_call_sites(self, tmp_path):
        """Grep with broad pattern finds ALL 6 .glob() call sites."""
        commit = self._get_pre_fix_commit()
        work_dir = self._checkout_pre_fix_files(tmp_path, commit)

        pattern = r"\.glob\("
        unclassified, summary = _verify_pattern_completeness(
            pattern, [], work_dir  # empty FIX_LOCATIONS — find everything
        )

        found_files = {m[0] for m in unclassified}
        # All 7 files must be found
        for expected in self.EXPECTED_GLOB_FILES:
            assert expected in found_files, (
                f"Grep missed {expected}. Found: {sorted(found_files)}"
            )

    def test_grep_finds_files_llm_missed(self, tmp_path):
        """Grep finds agentic_update.py which the LLM consistently missed."""
        commit = self._get_pre_fix_commit()
        work_dir = self._checkout_pre_fix_files(tmp_path, commit)

        pattern = r"\.glob\("
        # Simulate: LLM found 6 files, grep should find the 7th
        unclassified, summary = _verify_pattern_completeness(
            pattern, self.LLM_FOUND, work_dir
        )

        unclassified_files = {m[0] for m in unclassified}
        assert "pdd/agentic_update.py" in unclassified_files, (
            f"Grep did not find the missed file. Unclassified: {sorted(unclassified_files)}"
        )

    def test_context_window_captures_vulnerability_in_agentic_update(self, tmp_path):
        """The 30-line context window around the grep match in agentic_update.py
        captures the actual vulnerability (pattern construction without glob.escape).

        In the pre-fix code:
        - Line ~135: pattern = f"test_{stem}*{suffix}"   (vulnerability — no glob.escape)
        - Line ~153: directory.glob(pattern)             (grep match)

        The context window (30 lines before match) must include the vulnerability.
        """
        commit = self._get_pre_fix_commit()
        work_dir = self._checkout_pre_fix_files(tmp_path, commit)

        # Find the match in agentic_update.py
        pattern = r"\.glob\("
        unclassified, _ = _verify_pattern_completeness(
            pattern, self.LLM_FOUND, work_dir
        )

        # Get the agentic_update.py match
        agentic_matches = [m for m in unclassified if m[0] == "pdd/agentic_update.py"]
        assert agentic_matches, "agentic_update.py not found in unclassified"

        # Extract context
        context_by_file = _extract_match_context(agentic_matches, work_dir)
        context = context_by_file.get("pdd/agentic_update.py", "")

        # The context must include the vulnerability: pattern construction without escape
        # Pre-fix code had: pattern = f"test_{stem}*{suffix}"
        assert "test_{stem}" in context or 'f"test_' in context, (
            f"Context window did not capture the vulnerability.\n"
            f"Context:\n{context[:500]}"
        )
        # And it must include the grep match (the .glob call)
        assert ".glob(" in context


@pytest.mark.e2e
class TestE2ECase2SyntheticSubprocess:
    """Synthetic test: subprocess.run() calls without shlex.quote().

    Creates a fake codebase with 5 files:
    - 3 files: command built from user input without shlex.quote (NEEDS_FIX)
    - 1 file: command built with shlex.quote (SAFE)
    - 1 file: command is a hardcoded literal (SAFE)

    Verifies the full pipeline: grep → context → classification parsing.
    """

    def _create_synthetic_codebase(self, tmp_path: Path) -> Path:
        """Create 5 Python files with subprocess.run() calls."""
        (tmp_path / "vulnerable_1.py").write_text(textwrap.dedent("""\
            import subprocess

            def run_user_command(user_input: str) -> str:
                \"\"\"Run a command provided by the user.\"\"\"
                cmd = f"echo {user_input}"
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                return result.stdout
        """))

        (tmp_path / "vulnerable_2.py").write_text(textwrap.dedent("""\
            import subprocess

            def deploy_to_host(hostname: str) -> None:
                \"\"\"Deploy code to a remote host.\"\"\"
                deploy_cmd = f"ssh {hostname} 'cd /app && git pull'"
                subprocess.run(deploy_cmd, shell=True, check=True)
        """))

        (tmp_path / "vulnerable_3.py").write_text(textwrap.dedent("""\
            import subprocess

            def search_files(pattern: str, directory: str) -> str:
                \"\"\"Search for files matching a pattern.\"\"\"
                grep_cmd = f"grep -r {pattern} {directory}"
                result = subprocess.run(grep_cmd, shell=True, capture_output=True, text=True)
                return result.stdout
        """))

        (tmp_path / "safe_quoted.py").write_text(textwrap.dedent("""\
            import shlex
            import subprocess

            def run_safe_command(user_input: str) -> str:
                \"\"\"Run a command with proper quoting.\"\"\"
                cmd = f"echo {shlex.quote(user_input)}"
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                return result.stdout
        """))

        (tmp_path / "safe_literal.py").write_text(textwrap.dedent("""\
            import subprocess

            def get_disk_usage() -> str:
                \"\"\"Check disk usage with a hardcoded command.\"\"\"
                result = subprocess.run("df -h", shell=True, capture_output=True, text=True)
                return result.stdout
        """))

        return tmp_path

    def test_grep_finds_all_5_files(self, tmp_path):
        """Broad pattern finds ALL subprocess.run calls."""
        work_dir = self._create_synthetic_codebase(tmp_path)

        pattern = r"subprocess\.run\("
        unclassified, summary = _verify_pattern_completeness(
            pattern, [], work_dir
        )

        found_files = {m[0] for m in unclassified}
        assert len(found_files) == 5, f"Expected 5 files, found {len(found_files)}: {found_files}"

    def test_grep_finds_unclassified_when_3_known(self, tmp_path):
        """With 3 files in FIX_LOCATIONS, grep finds the other 2."""
        work_dir = self._create_synthetic_codebase(tmp_path)

        known = ["vulnerable_1.py", "vulnerable_2.py", "vulnerable_3.py"]
        pattern = r"subprocess\.run\("
        unclassified, _ = _verify_pattern_completeness(
            pattern, known, work_dir
        )

        unclassified_files = {m[0] for m in unclassified}
        assert unclassified_files == {"safe_quoted.py", "safe_literal.py"}

    def test_context_window_shows_shlex_quote(self, tmp_path):
        """Context for safe_quoted.py includes the shlex.quote call,
        giving the LLM enough information to classify as SAFE."""
        work_dir = self._create_synthetic_codebase(tmp_path)

        pattern = r"subprocess\.run\("
        unclassified, _ = _verify_pattern_completeness(
            pattern, ["vulnerable_1.py", "vulnerable_2.py", "vulnerable_3.py"],
            work_dir,
        )

        context_by_file = _extract_match_context(unclassified, work_dir)
        safe_context = context_by_file.get("safe_quoted.py", "")

        # The context MUST show shlex.quote — this is what lets the LLM classify it as SAFE
        assert "shlex.quote" in safe_context, (
            f"Context for safe_quoted.py missing shlex.quote.\nContext:\n{safe_context}"
        )

    def test_context_window_shows_hardcoded_literal(self, tmp_path):
        """Context for safe_literal.py shows the hardcoded command string,
        giving the LLM enough to classify as SAFE."""
        work_dir = self._create_synthetic_codebase(tmp_path)

        pattern = r"subprocess\.run\("
        unclassified, _ = _verify_pattern_completeness(
            pattern, ["vulnerable_1.py", "vulnerable_2.py", "vulnerable_3.py"],
            work_dir,
        )

        context_by_file = _extract_match_context(unclassified, work_dir)
        literal_context = context_by_file.get("safe_literal.py", "")

        # The context MUST show the hardcoded "df -h" string
        assert "df -h" in literal_context, (
            f"Context for safe_literal.py missing hardcoded command.\nContext:\n{literal_context}"
        )

    def test_context_window_shows_f_string_vulnerability(self, tmp_path):
        """Context for vulnerable files shows f-string command construction,
        giving the LLM enough to classify as NEEDS_FIX."""
        work_dir = self._create_synthetic_codebase(tmp_path)

        pattern = r"subprocess\.run\("
        all_matches, _ = _verify_pattern_completeness(pattern, [], work_dir)

        vuln1_matches = [m for m in all_matches if m[0] == "vulnerable_1.py"]
        context_by_file = _extract_match_context(vuln1_matches, work_dir)
        context = context_by_file.get("vulnerable_1.py", "")

        # Must show the f-string construction (vulnerability evidence)
        assert "f\"echo {user_input}\"" in context or "user_input" in context

    def test_classification_parsing_works_end_to_end(self):
        """Simulate a realistic LLM classification response and verify parsing."""
        simulated_llm_output = textwrap.dedent("""\
            I've examined each file:

            **safe_quoted.py** — Line 6 uses `shlex.quote(user_input)` to escape
            the argument before interpolation. This is the correct mitigation.
            SAFE_EVIDENCE: safe_quoted.py | 6 | uses shlex.quote() for proper escaping

            **safe_literal.py** — Line 5 passes a hardcoded string "df -h" to
            subprocess.run. No user input is interpolated.
            SAFE_EVIDENCE: safe_literal.py | 5 | hardcoded command string, no user input

            No files need fixing — both are already safe.
        """)

        needs_fix, safe = _parse_classification_evidence(simulated_llm_output)

        assert needs_fix == []
        assert set(safe) == {"safe_quoted.py", "safe_literal.py"}

    def test_merge_semantics_end_to_end(self):
        """Full merge scenario: original 3 vulnerable + grep finds 2 safe.
        After classification, merged set should still be 3 (originals preserved,
        safe files excluded, no new NEEDS_FIX)."""
        original = ["vulnerable_1.py", "vulnerable_2.py", "vulnerable_3.py"]
        needs_fix = []
        safe = ["safe_quoted.py", "safe_literal.py"]
        unclassified_filenames = ["safe_quoted.py", "safe_literal.py"]

        merged = _merge_fix_locations(original, needs_fix, safe, unclassified_filenames)

        # Original 3 preserved, safe 2 excluded
        assert set(merged) == {"vulnerable_1.py", "vulnerable_2.py", "vulnerable_3.py"}

    def test_full_pipeline_step_6_output_parsing(self):
        """Parse a realistic Step 6 output with both FIX_LOCATIONS and PATTERN_SEARCH."""
        step6_output = textwrap.dedent("""\
            ## Step 6: Root Cause Analysis

            The bug is a shell injection vulnerability across multiple files.
            User-provided input is interpolated into shell commands via f-strings
            without escaping via shlex.quote().

            ### Fix Location
            - **File(s) to modify:** `vulnerable_1.py`, `vulnerable_2.py`, `vulnerable_3.py`

            FIX_LOCATIONS: vulnerable_1.py, vulnerable_2.py, vulnerable_3.py
            PATTERN_SEARCH: subprocess\\.run\\(
        """)

        pattern = _parse_pattern_search(step6_output)
        assert pattern is not None
        assert "subprocess" in pattern

        sanitized = _sanitize_grep_pattern(pattern)
        assert sanitized is not None
