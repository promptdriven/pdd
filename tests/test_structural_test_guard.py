"""
Tests for structural test detection guard (Option A).

Issue: pdd-bug step 9 generated tests using `inspect.getsource` + string matching
instead of behavioral assertions, which allowed pdd-fix to produce dead code that
satisfied the structural test without implementing real behavior.

The guard function `detect_structural_test_patterns()` scans generated test files
for banned patterns and returns a list of violations.

Issue #990 added start_line support so the validator only flags patterns in
newly generated lines, not pre-existing code in the same file.
"""

import textwrap
from pathlib import Path
from typing import List

import pytest

from pdd.agentic_bug_orchestrator import detect_structural_test_patterns

# Fixture files: real pdd-bug output from issue #591 validation run.
_FIXTURES = Path(__file__).parent / "fixtures"


# --- E2E: validate against real pdd-bug output from issue #591 ---


class TestE2EAgainstRealOutput:
    """Run the guard against real LLM-generated test files from issue #591."""

    def test_dockerfile_test_not_flagged(self) -> None:
        """The real Dockerfile version-pin test should not be flagged."""
        f = _FIXTURES / "issue591_dockerfile_test.py.fixture"
        violations = detect_structural_test_patterns(str(f))
        assert violations == [], (
            f"Dockerfile config test should not be flagged. Got: {violations}"
        )

    def test_getsource_test_still_flagged(self) -> None:
        """The real inspect.getsource structural test should be caught."""
        f = _FIXTURES / "issue591_structural_getsource_test.py.fixture"
        violations = detect_structural_test_patterns(str(f))
        assert any("inspect.getsource" in v for v in violations), (
            "inspect.getsource patterns should still be flagged"
        )

    def test_behavioral_signal_test_clean(self) -> None:
        """The retry-generated behavioral signal handler test should be clean."""
        f = _FIXTURES / "issue591_behavioral_signal_test.py.fixture"
        violations = detect_structural_test_patterns(str(f))
        assert violations == [], (
            f"Behavioral signal test should not be flagged. Got: {violations}"
        )


# --- Detection of individual banned patterns ---


class TestDetectInspectGetsource:
    """Tests that inspect.getsource usage is flagged."""

    def test_getsource_with_string_assertion(self, tmp_path: Path) -> None:
        """inspect.getsource + `assert "keyword" in source` is the exact pattern from #591."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import inspect
            from src import job_runner

            def test_signal_handler():
                source = inspect.getsource(job_runner.main)
                assert "signal" in source
                assert "SIGTERM" in source
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0
        assert any("inspect.getsource" in v for v in violations)

    def test_getsource_with_module_source(self, tmp_path: Path) -> None:
        """inspect.getsource on a module (not just a function) is also structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import inspect
            from src import job_runner

            def test_module_has_signal():
                source = inspect.getsource(job_runner)
                assert "signal" in source
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0


class TestDetectInspectSignature:
    """Tests that inspect.signature usage is flagged."""

    def test_signature_parameter_check(self, tmp_path: Path) -> None:
        """Inspecting function signature to check parameter names is structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import inspect
            from src.services import executor_job_service

            def test_function_accepts_label():
                sig = inspect.signature(executor_job_service.launch_executor_job)
                assert "label" in sig.parameters
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0
        assert any("inspect.signature" in v for v in violations)


class TestDetectSourceStringMatching:
    """Tests that `assert "keyword" in source` patterns are caught even without inspect import."""

    def test_read_text_source_scan(self, tmp_path: Path) -> None:
        """Reading a .py file with Path.read_text() and asserting keywords is structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            from pathlib import Path

            def test_source_has_signal():
                content = Path("src/job_runner.py").read_text()
                assert "import signal" in content
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0

    def test_open_read_source_scan(self, tmp_path: Path) -> None:
        """Reading file with open() and asserting keywords is structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            def test_file_contains_keyword():
                with open("src/job_runner.py") as f:
                    source = f.read()
                assert "finally" in source
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0


class TestDetectHasattr:
    """Tests that hasattr used as a primary assertion is flagged."""

    def test_hasattr_as_assertion(self, tmp_path: Path) -> None:
        """assert hasattr(module, 'function_name') is structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            from src import job_runner

            def test_module_has_handler():
                assert hasattr(job_runner, '_handle_sigterm')
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0
        assert any("hasattr" in v for v in violations)


# --- Clean behavioral tests should NOT be flagged ---


class TestBehavioralTestsPassClean:
    """Behavioral tests must not produce false positives."""

    def test_function_call_with_assertion(self, tmp_path: Path) -> None:
        """A test that calls a function and asserts on the result is behavioral."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            from src.services.executor_job_service import _get_resource_overrides

            def test_opus_bug_gets_32gi():
                result = _get_resource_overrides(label="bug", model_override="claude-oauth")
                assert result["memory"] == "32Gi"
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == []

    def test_mock_verify_side_effects(self, tmp_path: Path) -> None:
        """A test that verifies mock calls (side effects) is behavioral."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            from unittest.mock import AsyncMock, patch
            from src.job_runner import main

            async def test_crash_marks_job_failed():
                with patch("src.job_runner.update_job_status", new_callable=AsyncMock) as mock_update:
                    with patch("src.job_runner.pdd_executor.execute_pdd_job", side_effect=RuntimeError("OOM")):
                        try:
                            await main()
                        except RuntimeError:
                            pass
                mock_update.assert_called_once_with("job-123", "failed", {"error": "Job crashed"})
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == []

    def test_signal_send_behavioral(self, tmp_path: Path) -> None:
        """A test that actually sends a signal and checks behavior is fine."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import os
            import signal
            from src.job_runner import _handle_sigterm, _shutdown_event

            def test_sigterm_sets_shutdown_event():
                _shutdown_event.clear()
                _handle_sigterm(signal.SIGTERM, None)
                assert _shutdown_event.is_set()
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == []

    def test_hasattr_in_setup_not_flagged(self, tmp_path: Path) -> None:
        """hasattr used in test setup/skip logic (not as the assertion) is OK."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import pytest
            from src import job_runner

            @pytest.mark.skipif(not hasattr(job_runner, '_handle_sigterm'), reason="not implemented")
            def test_sigterm_handler_behavior():
                job_runner._handle_sigterm(15, None)
                assert job_runner._shutdown_event.is_set()
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == []


# --- Multiple violations in one file ---


class TestMultipleViolations:
    """Files with multiple structural patterns should report all of them."""

    def test_getsource_and_hasattr_both_reported(self, tmp_path: Path) -> None:
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import inspect
            from src import job_runner

            def test_has_handler():
                assert hasattr(job_runner, '_handle_sigterm')

            def test_source_has_signal():
                source = inspect.getsource(job_runner.main)
                assert "signal" in source
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) >= 2


# --- Edge cases ---


class TestEdgeCases:
    """Edge cases for the detector."""

    def test_nonexistent_file_returns_empty(self) -> None:
        """Missing file should return empty list, not crash."""
        violations = detect_structural_test_patterns("/nonexistent/test_file.py")
        assert violations == []

    def test_empty_file_returns_empty(self, tmp_path: Path) -> None:
        """Empty test file is fine."""
        test_file = tmp_path / "test_empty.py"
        test_file.write_text("")

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == []

    def test_dockerfile_read_text_not_flagged(self, tmp_path: Path) -> None:
        """Reading a Dockerfile and asserting on config content is NOT structural."""
        test_file = tmp_path / "test_dockerfile.py"
        test_file.write_text(textwrap.dedent("""\
            import re
            from pathlib import Path

            def test_claude_code_version_pinned():
                dockerfile_path = Path(__file__).resolve().parents[1] / "Dockerfile.worker"
                content = dockerfile_path.read_text()
                pin_pattern = r"@anthropic-ai/claude-code@\\d+\\.\\d+\\.\\d+"
                assert re.search(pin_pattern, content)
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == [], (
            f"Dockerfile content assertion should not be flagged as structural. "
            f"Got: {violations}"
        )

    def test_yaml_read_text_not_flagged(self, tmp_path: Path) -> None:
        """Reading YAML/JSON config and asserting on content is NOT structural."""
        test_file = tmp_path / "test_config.py"
        test_file.write_text(textwrap.dedent("""\
            from pathlib import Path

            def test_config_has_required_field():
                content = Path("config.yaml").read_text()
                assert "database_url:" in content
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == [], (
            f"YAML config assertion should not be flagged. Got: {violations}"
        )

    def test_token_file_read_not_flagged(self, tmp_path: Path) -> None:
        """Reading a token file and asserting its value is NOT structural."""
        test_file = tmp_path / "test_tokens.py"
        test_file.write_text(textwrap.dedent("""\
            from pathlib import Path

            def test_token_written_correctly():
                content = Path(token_path).read_text()
                assert content == "ghp_test_token_123"
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == [], (
            f"Token file assertion should not be flagged. Got: {violations}"
        )

    def test_py_file_read_text_still_flagged(self, tmp_path: Path) -> None:
        """Reading a .py source file and asserting on keywords IS still structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            from pathlib import Path

            def test_source_has_import():
                content = Path("src/job_runner.py").read_text()
                assert "import signal" in content
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0, (
            "Reading a .py file and asserting keywords should still be flagged"
        )

    def test_open_dockerfile_not_flagged(self, tmp_path: Path) -> None:
        """Reading a Dockerfile via open() as f: f.read() is NOT structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            def test_dockerfile_has_pin():
                with open("Dockerfile.worker") as f:
                    content = f.read()
                assert "@anthropic-ai/claude-code@" in content
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == [], (
            f"open(Dockerfile) + f.read() should not be flagged. Got: {violations}"
        )

    def test_open_yaml_not_flagged(self, tmp_path: Path) -> None:
        """Reading a YAML file via open() as f: f.read() is NOT structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            def test_config_has_field():
                with open("config.yaml") as f:
                    content = f.read()
                assert "database_url:" in content
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == [], (
            f"open(config.yaml) + f.read() should not be flagged. Got: {violations}"
        )

    def test_open_py_file_still_flagged(self, tmp_path: Path) -> None:
        """Reading a .py file via open() and asserting keywords IS structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            def test_file_has_finally():
                with open("src/job_runner.py") as f:
                    source = f.read()
                assert "finally" in source
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert len(violations) > 0, (
            "Reading a .py file via open() should still be flagged"
        )

    def test_mixed_dockerfile_and_getsource(self, tmp_path: Path) -> None:
        """File with both Dockerfile read (OK) and getsource (bad) only flags getsource."""
        test_file = tmp_path / "test_mixed.py"
        test_file.write_text(textwrap.dedent("""\
            import inspect
            import re
            from pathlib import Path
            from src import job_runner

            def test_dockerfile_pinned():
                content = Path("Dockerfile.worker").read_text()
                assert "@anthropic-ai/claude-code@" in content

            def test_source_has_signal():
                source = inspect.getsource(job_runner.main)
                assert "signal" in source
        """))

        violations = detect_structural_test_patterns(str(test_file))
        # Should flag getsource but NOT the Dockerfile read
        assert any("inspect.getsource" in v for v in violations)
        assert not any("source string matching" in v for v in violations), (
            f"Dockerfile read_text should not be flagged. Violations: {violations}"
        )

    def test_inspect_used_for_non_structural_purpose(self, tmp_path: Path) -> None:
        """inspect.getfile or inspect.getmodule used for path resolution is not structural."""
        test_file = tmp_path / "test_example.py"
        test_file.write_text(textwrap.dedent("""\
            import inspect
            from src import job_runner

            def test_module_location():
                # Using inspect to find the file, then doing behavioral test
                module_path = inspect.getfile(job_runner)
                # ... then imports and calls the function
                result = job_runner.main()
                assert result is not None
        """))

        violations = detect_structural_test_patterns(str(test_file))
        assert violations == []


# --- start_line support (issue #990) ---
# Helpers build anti-pattern lines via concatenation so this test file itself
# does not contain the literal patterns that the validator would flag.

_MOD = "inspect"


def _sig_check_lines() -> List[str]:
    """Return lines containing a signature-check anti-pattern."""
    return [
        "def test_old_sig():",
        "    sig = " + _MOD + "." + "signature(module.func)",
        "    " + 'assert "param" in sig.parameters',
    ]


def _getsource_lines() -> List[str]:
    """Return lines containing a getsource anti-pattern."""
    return [
        "def test_old_source():",
        "    source = " + _MOD + "." + "getsource(module.main)",
        "    " + 'assert "signal" in source',
    ]


def _hasattr_lines() -> List[str]:
    """Return lines containing a hasattr anti-pattern."""
    prefix = "    "
    kw = "hasattr"
    return [
        "def test_old_attr():",
        prefix + "assert " + kw + "(module, 'attr')",
    ]


def _clean_test_lines(count: int = 5) -> List[str]:
    """Return *count* innocuous test lines."""
    lines: List[str] = ["import os", ""]
    for i in range(count):
        lines.append(f"def test_clean_{i}():")
        lines.append(f"    assert {i} == {i}")
        lines.append("")
    return lines


def _write_fixture(path: Path, sections: List[List[str]]) -> None:
    """Write a fixture file from a list of line-groups."""
    all_lines: List[str] = []
    for section in sections:
        all_lines.extend(section)
        all_lines.append("")  # blank separator
    path.write_text("\n".join(all_lines) + "\n")


class TestStartLineFiltersPreexistingPatterns:
    """Pre-existing anti-patterns are excluded when start_line skips them."""

    def test_preexisting_patterns_not_reported_with_start_line(
        self, tmp_path: Path
    ) -> None:
        """When start_line is past all pre-existing violations, result is empty."""
        test_file = tmp_path / "test_example.py"
        _write_fixture(test_file, [
            _sig_check_lines(),
            _getsource_lines(),
            _hasattr_lines(),
        ])
        pre_line_count = len(test_file.read_text().splitlines())

        clean = _clean_test_lines(3)
        with open(test_file, "a") as f:
            f.write("\n".join(clean) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), start_line=pre_line_count + 1
        )

        assert violations == [], (
            f"Pre-existing patterns should be ignored when start_line is set. "
            f"Got {len(violations)} violation(s): {violations}"
        )


class TestStartLineCatchesNewViolations:
    """New violations appearing after start_line are still caught."""

    def test_new_violations_detected_after_start_line(
        self, tmp_path: Path
    ) -> None:
        """Violations on lines >= start_line must still be reported."""
        test_file = tmp_path / "test_example.py"

        clean = _clean_test_lines(5)
        pre_line_count = len(clean) + 1

        bad_section = _sig_check_lines() + [""] + _hasattr_lines()
        all_lines = clean + [""] + bad_section
        test_file.write_text("\n".join(all_lines) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), start_line=pre_line_count
        )

        assert len(violations) >= 2, (
            f"Expected at least 2 violations in new section, got {len(violations)}: "
            f"{violations}"
        )
        violation_text = " ".join(violations).lower()
        assert "signature" in violation_text or "hasattr" in violation_text, (
            f"Expected signature or hasattr violations, got: {violations}"
        )


class TestStartLineMixedScenario:
    """Only new-section violations are reported, old ones are ignored."""

    def test_mixed_old_and_new_violations(self, tmp_path: Path) -> None:
        """File has violations both before and after start_line."""
        test_file = tmp_path / "test_example.py"

        old_section = _sig_check_lines()
        old_line_count = len(old_section) + 1  # +1 for blank separator

        new_section = _hasattr_lines()

        _write_fixture(test_file, [old_section, new_section])

        violations = detect_structural_test_patterns(
            str(test_file), start_line=old_line_count + 1
        )

        assert len(violations) >= 1, (
            f"Expected at least 1 new-section violation, got: {violations}"
        )
        violation_text = " ".join(violations).lower()
        assert "hasattr" in violation_text, (
            f"Expected hasattr violation from new section, got: {violations}"
        )
        assert not any("Line 2:" in v for v in violations), (
            f"Old-section violations should not be reported: {violations}"
        )


class TestStartLineSourceStringMatching:
    """Source-string-matching (second scan phase) respects start_line."""

    def test_source_read_pattern_filtered_by_start_line(
        self, tmp_path: Path
    ) -> None:
        """The read_text + assert-in-var pattern should be filtered by start_line."""
        test_file = tmp_path / "test_example.py"

        rt_call = '    src_txt = Path("module.py")' + ".read_text()"
        rt_assert = '    assert "def main" in ' + "src_txt"
        old_lines = [
            "from pathlib import Path",
            "",
            "def test_old_source_read():",
            rt_call,
            rt_assert,
        ]
        old_line_count = len(old_lines) + 1

        new_lines = [
            "def test_new_clean():",
            "    assert 1 + 1 == 2",
        ]

        all_lines = old_lines + [""] + new_lines
        test_file.write_text("\n".join(all_lines) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), start_line=old_line_count + 1
        )

        assert violations == [], (
            f"Old source-string-matching should be ignored with start_line. "
            f"Got: {violations}"
        )


class TestBackwardCompatNoStartLine:
    """Omitting start_line (or passing None) still scans everything."""

    def test_no_start_line_scans_full_file(self, tmp_path: Path) -> None:
        """Passing start_line=None should behave identically to the old API."""
        test_file = tmp_path / "test_example.py"
        _write_fixture(test_file, [
            _sig_check_lines(),
            _hasattr_lines(),
        ])

        violations = detect_structural_test_patterns(
            str(test_file), start_line=None
        )

        assert len(violations) >= 2, (
            f"With start_line=None, all violations should be found. "
            f"Got {len(violations)}: {violations}"
        )

    def test_no_start_line_arg_scans_full_file(self, tmp_path: Path) -> None:
        """Omitting start_line entirely preserves backward-compatible behavior."""
        test_file = tmp_path / "test_example.py"
        _write_fixture(test_file, [
            _sig_check_lines(),
            _hasattr_lines(),
        ])

        violations = detect_structural_test_patterns(str(test_file))

        assert len(violations) >= 2, (
            f"Without start_line, all violations should be found. "
            f"Got {len(violations)}: {violations}"
        )


class TestStartLineTruncationSafety:
    """When start_line exceeds file length, clamp to 1 and scan everything.

    This handles the case where Step 9 rewrites a file shorter than the
    pre-step-9 snapshot — the offset would overshoot EOF, so clamping to 1
    ensures violations in the rewritten content are still caught.
    """

    def test_start_line_beyond_eof_scans_full_file(self, tmp_path: Path) -> None:
        """When start_line exceeds file length, all violations are reported."""
        test_file = tmp_path / "test_example.py"
        _write_fixture(test_file, [
            _sig_check_lines(),
            _getsource_lines(),
        ])
        total_lines = len(test_file.read_text().splitlines())

        violations = detect_structural_test_patterns(
            str(test_file), start_line=total_lines + 100
        )

        assert len(violations) >= 2, (
            f"start_line beyond EOF should clamp to 1 and scan everything. "
            f"Got {len(violations)}: {violations}"
        )

    def test_truncated_file_scans_from_line_1(self, tmp_path: Path) -> None:
        """Simulates a file rewritten shorter than the snapshot line count."""
        test_file = tmp_path / "test_example.py"
        # Write a short file with violations (5 lines)
        _write_fixture(test_file, [_hasattr_lines()])
        current_lines = len(test_file.read_text().splitlines())

        # Pass a start_line as if the original file had 50 lines
        violations = detect_structural_test_patterns(
            str(test_file), start_line=50
        )

        assert current_lines < 50, "Precondition: file is shorter than start_line"
        assert len(violations) >= 1, (
            f"Truncated file should be fully scanned. Got: {violations}"
        )


class TestStartLineCrossBoundaryVarTracking:
    """Source-var tracking scans full file but only reports new-line violations."""

    def test_new_assertion_using_old_getsource_var_is_flagged(
        self, tmp_path: Path
    ) -> None:
        """New code that asserts on a variable assigned via getsource in old code
        should still be flagged — the assertion is new structural code."""
        test_file = tmp_path / "test_example.py"

        # Old section: assigns source var via getsource (line ~2)
        old_lines = _getsource_lines()
        old_line_count = len(old_lines) + 1  # +1 for blank separator

        # New section: uses the same var name in a new assertion
        # (In reality new code wouldn't reference old locals, but this
        # tests that the tracking logic scans the full file.)
        new_assert = '    assert "new_thing" in ' + "source"
        new_lines = [
            "def test_new_but_structural():",
            new_assert,
        ]

        all_lines = old_lines + [""] + new_lines
        test_file.write_text("\n".join(all_lines) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), start_line=old_line_count + 1
        )

        # The getsource on the old line should NOT be reported.
        old_line_violations = [v for v in violations if f"Line 2:" in v]
        assert old_line_violations == [], (
            f"Old-line getsource should not be reported: {violations}"
        )

        # The NEW source-string-matching assertion SHOULD be reported.
        # Pre-existing getsource must not suppress new-line violations.
        new_line_num = old_line_count + 2  # blank separator + def line + assert line
        new_line_violations = [
            v
            for v in violations
            if f"Line {new_line_num}:" in v and "source string matching" in v
        ]
        assert len(new_line_violations) == 1, (
            f"New source-string assertion should be flagged: {violations}"
        )


# ---------------------------------------------------------------------------
# Tests for the new previous_content API (issue #774 fix)
# These tests FAIL on the current start_line-based implementation and PASS
# once detect_structural_test_patterns is updated to accept previous_content.
# ---------------------------------------------------------------------------


class TestPreviousContentOffByOneRegression:
    """Regression: unchanged file with previous_content snapshot returns no violations.

    The off-by-one bug: when start_line = len(lines) + 1 (nothing appended),
    the clamp fires and rescans the entire file, flagging pre-existing patterns.
    Fix: use previous_content snapshot + difflib diff; empty diff → no reportable lines.
    """

    def test_unchanged_file_with_structural_patterns_returns_no_violations(
        self, tmp_path: Path
    ) -> None:
        """Off-by-one regression: unchanged file with a full content snapshot returns [].

        File contains inspect.getsource at two locations (mirrors the real scenario:
        inspect.getsource at lines 3346/3362 of a 4144-line file).
        No lines were appended, so the diff is empty and no violations should be reported.

        FAILS on buggy code: calling with previous_content= is a TypeError because the
        parameter doesn't exist. After the fix, the diff is empty → returns [].
        """
        test_file = tmp_path / "test_preexisting.py"
        _write_fixture(test_file, [_getsource_lines(), _hasattr_lines()])

        # Snapshot the content — nothing is appended after this
        previous_content = test_file.read_text()

        # File is unchanged: diff is empty → no new lines → no reportable violations
        violations = detect_structural_test_patterns(
            str(test_file), previous_content=previous_content
        )

        assert violations == [], (
            f"Unchanged file with previous_content snapshot should return no violations. "
            f"The diff is empty — no new lines exist to report. "
            f"Got {len(violations)} violation(s): {violations}"
        )


class TestPreviousContentAppendedViolations:
    """Only violations on lines appended after the snapshot are reported."""

    def test_only_appended_line_numbers_are_flagged(self, tmp_path: Path) -> None:
        """Snapshot has no patterns; appended lines contain inspect.signature.

        Only the appended region line numbers should appear in violations.

        FAILS on buggy code: previous_content= is not a valid parameter (TypeError).
        """
        test_file = tmp_path / "test_append.py"
        clean = _clean_test_lines(3)
        test_file.write_text("\n".join(clean) + "\n")

        previous_content = test_file.read_text()
        pre_line_count = len(clean)

        # Append structural pattern lines after taking the snapshot
        bad_lines = _sig_check_lines()
        with open(test_file, "a") as f:
            f.write("\n".join(bad_lines) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), previous_content=previous_content
        )

        assert len(violations) >= 1, (
            f"Expected at least 1 violation in the appended section. Got: {violations}"
        )
        # All reported violations must refer to lines in the appended region
        for v in violations:
            import re as _re
            m = _re.search(r"Line (\d+):", v)
            if m:
                line_num = int(m.group(1))
                assert line_num > pre_line_count, (
                    f"Violation at Line {line_num} is in the pre-snapshot region "
                    f"(pre_line_count={pre_line_count}): {v}"
                )


class TestPreviousContentPreexistingViolationsSuppressed:
    """Snapshot already contains structural patterns; they must not be re-reported."""

    def test_preexisting_violations_not_reported_with_previous_content(
        self, tmp_path: Path
    ) -> None:
        """File has inspect.signature + hasattr in snapshot; appending a clean test
        must return [] because the pre-existing violations are not new.

        FAILS on buggy code: previous_content= is not a valid parameter (TypeError).
        """
        test_file = tmp_path / "test_preexisting_then_clean.py"
        _write_fixture(test_file, [_sig_check_lines(), _hasattr_lines()])

        previous_content = test_file.read_text()

        # Append a clean test — no new violations
        with open(test_file, "a") as f:
            f.write("\n".join(_clean_test_lines(2)) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), previous_content=previous_content
        )

        assert violations == [], (
            f"Pre-existing violations should not be reported when previous_content "
            f"snapshot includes them. Got: {violations}"
        )


class TestPreviousContentTruncationSafe:
    """File rewritten shorter than snapshot: all current lines treated as new."""

    def test_truncated_file_violations_still_caught(self, tmp_path: Path) -> None:
        """Snapshot is a long clean file; file is overwritten with a short file
        containing a hasattr assertion.  The rewritten lines are fully new per
        the diff, so violations must be reported.

        FAILS on buggy code: previous_content= is not a valid parameter (TypeError).
        """
        test_file = tmp_path / "test_truncated.py"
        # Original: long clean file
        original_lines = _clean_test_lines(20)
        test_file.write_text("\n".join(original_lines) + "\n")
        previous_content = test_file.read_text()

        # Overwrite with a short file that has a violation
        test_file.write_text("\n".join(_hasattr_lines()) + "\n")
        current_lines = len(test_file.read_text().splitlines())

        assert current_lines < len(original_lines), (
            "Precondition: rewritten file must be shorter than the snapshot"
        )

        violations = detect_structural_test_patterns(
            str(test_file), previous_content=previous_content
        )

        assert len(violations) >= 1, (
            f"Truncated/rewritten file should be fully scanned. Got: {violations}"
        )


class TestPreviousContentCrossBoundaryVarTracking:
    """Cross-boundary: var assigned in snapshot, asserted in new lines."""

    def test_cross_boundary_var_new_assertion_flagged(self, tmp_path: Path) -> None:
        """Old content assigns src = Path('module.py').read_text(); new content
        contains assert 'def main' in src.  The new assertion line must be flagged
        as source string matching.  The old assignment line must NOT be flagged.

        FAILS on buggy code: previous_content= is not a valid parameter (TypeError).
        """
        test_file = tmp_path / "test_cross_boundary.py"

        # Old section: read_text assignment (in snapshot)
        rt_call = '    src = Path("module.py")' + ".read_text()"
        old_lines = [
            "from pathlib import Path",
            "",
            "def test_old_reads():",
            rt_call,
        ]
        test_file.write_text("\n".join(old_lines) + "\n")
        previous_content = test_file.read_text()
        pre_line_count = len(old_lines)

        # New section: assertion using the variable
        new_assert = '    assert "def main" in ' + "src"
        new_lines = [
            "def test_new_asserts():",
            new_assert,
        ]
        with open(test_file, "a") as f:
            f.write("\n".join(new_lines) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), previous_content=previous_content
        )

        # The new assertion line must be flagged
        assert len(violations) >= 1, (
            f"New source-string assertion should be flagged as structural. "
            f"Got: {violations}"
        )

        # The old assignment line (rt_call) must NOT be reported
        old_line_violations = [
            v for v in violations
            if any(f"Line {n}:" in v for n in range(1, pre_line_count + 2))
        ]
        assert old_line_violations == [], (
            f"Old-region lines should not be reported. "
            f"Old violations: {old_line_violations}, all violations: {violations}"
        )


class TestPreviousContentNoneScansEverything:
    """previous_content=None (or omitted) scans the entire file — unchanged behavior."""

    def test_no_snapshot_scans_entire_file(self, tmp_path: Path) -> None:
        """Calling with previous_content=None or without the argument must behave like
        the old API with no start_line: all violations across the file are reported.

        FAILS on buggy code: previous_content= is not a valid parameter (TypeError).
        After fix: None means no snapshot → scan everything.
        """
        test_file = tmp_path / "test_full_scan.py"
        _write_fixture(test_file, [_getsource_lines(), _sig_check_lines()])

        violations_explicit_none = detect_structural_test_patterns(
            str(test_file), previous_content=None
        )
        violations_no_arg = detect_structural_test_patterns(str(test_file))

        assert len(violations_explicit_none) >= 2, (
            f"previous_content=None should scan everything. "
            f"Got {len(violations_explicit_none)}: {violations_explicit_none}"
        )
        assert len(violations_no_arg) >= 2, (
            f"No previous_content arg should scan everything. "
            f"Got {len(violations_no_arg)}: {violations_no_arg}"
        )


class TestPreviousContentMiddleInsertion:
    """difflib correctly identifies mid-file insertions — impossible with start_line."""

    def test_middle_insertion_caught_by_diff(self, tmp_path: Path) -> None:
        """File has 10 clean lines in snapshot.  Three inspect.getsource lines are
        inserted between lines 5 and 6.  The inserted lines must be flagged.
        Original lines renumbered after the insertion must NOT be flagged.

        FAILS on buggy code: previous_content= is not a valid parameter (TypeError).
        The old start_line approach cannot handle mid-file insertions at all.
        """
        test_file = tmp_path / "test_middle_insert.py"

        # Snapshot: 10 clean lines
        original_lines: List[str] = []
        for i in range(1, 11):
            original_lines.append(f"def test_clean_{i}():")
            original_lines.append(f"    assert {i} == {i}")
            original_lines.append("")
        test_file.write_text("\n".join(original_lines) + "\n")
        previous_content = test_file.read_text()

        # Insert getsource lines between lines 15 and 16 (after test_clean_5)
        current_text = test_file.read_text()
        current_lines_list = current_text.splitlines()
        insert_at = 15  # 0-based, after test_clean_5's assert
        inserted = _getsource_lines()
        new_lines = (
            current_lines_list[:insert_at]
            + inserted
            + current_lines_list[insert_at:]
        )
        test_file.write_text("\n".join(new_lines) + "\n")

        violations = detect_structural_test_patterns(
            str(test_file), previous_content=previous_content
        )

        assert len(violations) >= 1, (
            f"Inserted getsource lines should be flagged. Got: {violations}"
        )
        # Reported line numbers must fall within the inserted region
        import re as _re2
        for v in violations:
            m = _re2.search(r"Line (\d+):", v)
            if m:
                line_num = int(m.group(1))
                # Inserted at 0-based position 15 → 1-based lines 16..18
                assert insert_at < line_num <= insert_at + len(inserted) + 1, (
                    f"Violation at Line {line_num} is outside the inserted region "
                    f"(expected ~lines {insert_at + 1}–{insert_at + len(inserted) + 1}): {v}"
                )


# ---------------------------------------------------------------------------
# Caller-side test: orchestrator snapshot stores full content, not line count
# ---------------------------------------------------------------------------


class TestCallerPassesPreviousContentToGuard:
    """The orchestrator's step-9 scan must pass previous_content=<str> to the guard,
    not start_line=<int>, after the snapshot dict is updated from Dict[str, int]
    to Dict[str, str].

    FAILS on buggy code: the caller passes start_line=pre_count+1 (an int),
    so 'previous_content' is absent from mock.call_args.kwargs.
    """

    def test_step9_caller_passes_previous_content_string(
        self, tmp_path: Path
    ) -> None:
        """After the fix, the orchestrator passes previous_content=<file content string>
        to detect_structural_test_patterns for files that existed before Step 9.

        Setup:
        - A test file exists in the worktree's tests/ dir before Step 9 runs.
        - Step 9 output claims FILES_CREATED: tests/test_preexisting.py.
        - detect_structural_test_patterns is patched.
        - We assert it was called with previous_content=<string>, not start_line=<int>.
        """
        from unittest.mock import patch, MagicMock
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        mock_worktree_path.mkdir(parents=True, exist_ok=True)

        # Create a pre-existing test file in the worktree tests/ directory.
        # The orchestrator snapshots this before Step 9 runs.
        tests_dir = mock_worktree_path / "tests"
        tests_dir.mkdir(parents=True, exist_ok=True)
        pre_existing_file = tests_dir / "test_preexisting.py"
        pre_existing_content = "def test_clean():\n    assert 1 + 1 == 2\n"
        pre_existing_file.write_text(pre_existing_content)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template",
                   return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree",
                   return_value=(mock_worktree_path, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess",
                   side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state",
                   return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root",
                   return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked",
                   return_value=[]), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns") as mock_detect, \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests",
                   return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests",
                   return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step9":
                    # Step 9 claims it created/modified the pre-existing file
                    return (
                        True,
                        "Generated tests.\nFILES_CREATED: tests/test_preexisting.py",
                        0.1,
                        "model",
                    )
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect
            mock_detect.return_value = []  # no violations → no retry loop
            mock_subprocess.run.return_value = MagicMock(
                returncode=0, stdout="", stderr=""
            )

            run_agentic_bug_orchestrator(
                issue_url="http://github.com/owner/repo/issues/1",
                issue_content="Bug description",
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                issue_author="user",
                issue_title="Bug Title",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
            )

        # The guard must have been called at least once during the step 9 scan
        mock_detect.assert_called()

        # Find the call for test_preexisting.py and check its keyword arguments.
        # On buggy code: kwargs has start_line=<int> → assertion fails.
        # On fixed code: kwargs has previous_content=<str> → assertion passes.
        target_calls = [
            c for c in mock_detect.call_args_list
            if c.args and "test_preexisting" in str(c.args[0])
        ]
        assert len(target_calls) >= 1, (
            f"detect_structural_test_patterns was never called for test_preexisting.py. "
            f"All calls: {mock_detect.call_args_list}"
        )
        call = target_calls[0]
        assert "previous_content" in call.kwargs, (
            f"Caller should pass previous_content=<str> after the fix, "
            f"not start_line=<int>. Got kwargs: {call.kwargs}"
        )
        assert isinstance(call.kwargs["previous_content"], str), (
            f"previous_content must be a string (file content), not "
            f"{type(call.kwargs['previous_content'])}. Got: {call.kwargs}"
        )
