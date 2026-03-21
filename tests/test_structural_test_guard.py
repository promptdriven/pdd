"""
Tests for structural test detection guard (Option A).

Issue: pdd-bug step 9 generated tests using `inspect.getsource` + string matching
instead of behavioral assertions, which allowed pdd-fix to produce dead code that
satisfied the structural test without implementing real behavior.

The guard function `detect_structural_test_patterns()` scans generated test files
for banned patterns and returns a list of violations.
"""

import textwrap
from pathlib import Path

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
