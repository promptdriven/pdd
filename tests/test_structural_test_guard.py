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

from pdd.agentic_bug_orchestrator import (
    _scan_step9_file_for_new_patterns,
    detect_structural_test_patterns,
)

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


class TestStartLinePastEOF:
    """When start_line exceeds file length, no violations are reported.

    The old clamp (``effective_start = 1 if start_line > len(lines)``)
    treated "past EOF" as "file shrank, rescan everything", but the
    normal "no new lines appended" case is ``start_line = len(lines) + 1``
    — which tripped the clamp and false-flagged every pre-existing
    pattern.  This was the pdd_cloud #1064 failure (issue #774).

    With the clamp removed, past-EOF start_line naturally reports no
    violations because the line-iteration loop only runs up to
    ``len(lines)``.  The "file shrank" case is now correctly handled at
    the call site by ``_scan_step9_file_for_new_patterns``, which uses
    content comparison (not line counts) to distinguish unchanged from
    rewritten files.
    """

    def test_start_line_beyond_eof_reports_no_violations(self, tmp_path: Path) -> None:
        """start_line past EOF must not report violations (fix for #774)."""
        test_file = tmp_path / "test_example.py"
        _write_fixture(test_file, [
            _sig_check_lines(),
            _getsource_lines(),
        ])
        total_lines = len(test_file.read_text().splitlines())

        violations = detect_structural_test_patterns(
            str(test_file), start_line=total_lines + 100
        )

        assert len(violations) == 0, (
            f"start_line beyond EOF must not report violations. "
            f"Got {len(violations)}: {violations}. "
            f"This was the #774 bug — the clamp rescanned the whole file, "
            f"false-flagging pre-existing patterns when Step 9 left the file "
            f"untouched."
        )

    def test_start_line_equals_len_plus_one_reports_no_violations(
        self, tmp_path: Path
    ) -> None:
        """The exact #774 scenario: start_line = len(lines) + 1 (off-by-one)."""
        test_file = tmp_path / "test_example.py"
        _write_fixture(test_file, [_hasattr_lines()])
        total_lines = len(test_file.read_text().splitlines())

        # This is the snapshot+1 case that tripped #774 on pdd_cloud.
        violations = detect_structural_test_patterns(
            str(test_file), start_line=total_lines + 1
        )

        assert len(violations) == 0, (
            f"Snapshot+1 (no lines appended) must report 0 violations. "
            f"Got {len(violations)}: {violations}. Issue #774."
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


# ============================================================================
# Helper: _scan_step9_file_for_new_patterns
#
# Content-based change detection (introduced after the gltanaka review of
# pdd_cloud #1064 surfaced two false negatives in the line-count-only
# approach).  The helper distinguishes:
#   - file unchanged          -> skip (no violations)
#   - pure append             -> scan only appended lines (#990 optimisation)
#   - rewrite (any line count)-> full scan (catch real violations)
#   - brand-new file          -> full scan
# ============================================================================


def _build_violation_text() -> str:
    """Return file content containing a real structural violation."""
    mod = "inspect"
    return (
        "import inspect\n\n"
        "def test_thing():\n"
        "    src = " + mod + "." + "getsource(thing.fn)\n"
        "    " + 'assert "signal" in src\n'
    )


def _build_clean_text(n: int = 5) -> str:
    """Return clean test file content with ``n`` simple test functions."""
    body = "import pytest\n\n"
    for i in range(n):
        body += f"def test_thing_{i}():\n    assert {i} == {i}\n\n"
    return body


class TestScanStep9HelperUnchanged:
    """Unchanged file (current == pre_snapshot) reports zero violations.

    Even when the snapshot itself contains pre-existing structural
    patterns, an unchanged file means Step 9 introduced nothing new — so
    the helper must report zero violations.  This is the pdd_cloud #1064
    failure mode that drove the SIGKILL retry loop.
    """

    def test_unchanged_file_with_preexisting_violation_reports_zero(
        self, tmp_path: Path
    ) -> None:
        f = tmp_path / "test_x.py"
        snap = _build_violation_text()
        f.write_text(snap)

        violations = _scan_step9_file_for_new_patterns(str(f), snap)

        assert violations == [], (
            f"Unchanged file (current == snapshot) must report 0 violations "
            f"even when the snapshot itself contains structural patterns. "
            f"Got: {violations}"
        )

    def test_unchanged_clean_file_reports_zero(self, tmp_path: Path) -> None:
        f = tmp_path / "test_y.py"
        snap = _build_clean_text(5)
        f.write_text(snap)

        violations = _scan_step9_file_for_new_patterns(str(f), snap)

        assert violations == []


class TestScanStep9HelperRewriteShorter:
    """Rewrite that produces a SHORTER file must still flag new violations.

    This is the first false-negative the gltanaka review identified:
    line-count-only logic computed start_line = pre_count + 1 which
    overshoots the new (shorter) file length, suppressing all violations.
    Content comparison correctly recognises this as a rewrite (snapshot
    is not a line-prefix of current) and triggers a full scan.
    """

    def test_rewrite_shorter_with_new_violation_is_flagged(
        self, tmp_path: Path
    ) -> None:
        f = tmp_path / "test_x.py"
        # Pre-snapshot: long, clean file
        pre_snap = _build_clean_text(20)
        # Post-Step-9: short file with a new violation
        new_content = _build_violation_text()
        assert len(new_content.splitlines()) < len(pre_snap.splitlines()), (
            "Precondition: rewritten file is strictly shorter than snapshot"
        )
        f.write_text(new_content)

        violations = _scan_step9_file_for_new_patterns(str(f), pre_snap)

        assert len(violations) > 0, (
            f"Rewritten shorter file must still flag violations. Got: {violations}. "
            f"This is gltanaka's first review case: line-count-only logic would "
            f"compute start_line past EOF and silently report zero."
        )
        assert any("inspect.getsource" in v for v in violations)


class TestScanStep9HelperRewriteSameLength:
    """Rewrite that lands on the SAME line count must still flag new violations.

    This is the second false-negative the gltanaka review identified:
    line-count-only logic would compute start_line = len(lines) + 1, which
    is past EOF for the same-length rewrite.  Content comparison rejects
    the prefix match and triggers a full scan.
    """

    def test_rewrite_same_length_with_new_violation_is_flagged(
        self, tmp_path: Path
    ) -> None:
        f = tmp_path / "test_x.py"
        viol = _build_violation_text()
        # Build a clean snapshot with EXACTLY the same line count.
        target_lines = len(viol.splitlines())
        clean = "import os\n\n" + "\n".join(["x = 1"] * (target_lines - 2))
        assert len(clean.splitlines()) == target_lines, (
            "Precondition: snapshot has same line count as rewritten content"
        )
        f.write_text(viol)

        violations = _scan_step9_file_for_new_patterns(str(f), clean)

        assert len(violations) > 0, (
            f"Same-line-count rewrite must still flag violations. Got: {violations}. "
            f"This is gltanaka's second review case."
        )
        assert any("inspect.getsource" in v for v in violations)


class TestScanStep9HelperPureAppend:
    """Pure append (snapshot is a line-prefix of current) skips pre-existing
    violations but flags new ones — preserving the issue #990 optimisation.
    """

    def test_pure_append_skips_preexisting_violation(self, tmp_path: Path) -> None:
        f = tmp_path / "test_x.py"
        snap = _build_violation_text()  # snapshot already has violation
        f.write_text(snap + "\n\ndef test_clean():\n    assert True\n")

        violations = _scan_step9_file_for_new_patterns(str(f), snap)

        assert violations == [], (
            f"Pure append must skip pre-existing violations (#990). Got: {violations}"
        )

    def test_pure_append_flags_new_violation_in_appended_lines(
        self, tmp_path: Path
    ) -> None:
        f = tmp_path / "test_x.py"
        snap = _build_clean_text(5)
        f.write_text(snap + "\n\n" + _build_violation_text())

        violations = _scan_step9_file_for_new_patterns(str(f), snap)

        assert len(violations) > 0, (
            f"Pure append with new violation must be flagged. Got: {violations}"
        )


class TestScanStep9HelperEdgeCases:
    """Brand-new files, missing files, empty snapshots."""

    def test_brand_new_file_with_violation_is_flagged(self, tmp_path: Path) -> None:
        """pre_snapshot=None → file did not exist pre-Step 9 → full scan."""
        f = tmp_path / "test_new.py"
        f.write_text(_build_violation_text())

        violations = _scan_step9_file_for_new_patterns(str(f), None)

        assert len(violations) > 0

    def test_missing_file_returns_empty(self, tmp_path: Path) -> None:
        """Missing file (Step 9 deleted it?) is not an error condition."""
        f = tmp_path / "test_gone.py"
        # File was never created
        violations = _scan_step9_file_for_new_patterns(str(f), "old content")
        assert violations == []

    def test_partial_prefix_match_triggers_full_scan(self, tmp_path: Path) -> None:
        """If snapshot's first lines match but middle differs, treat as rewrite."""
        f = tmp_path / "test_x.py"
        snap = _build_clean_text(5)
        # Replace first line, keep the rest, then add a violation.
        # Snapshot is NOT a strict line-prefix of new content.
        new = "import inspect\n" + snap + "\n" + _build_violation_text()
        f.write_text(new)

        violations = _scan_step9_file_for_new_patterns(str(f), snap)

        assert len(violations) > 0, (
            f"Non-prefix change should trigger full scan. Got: {violations}"
        )
