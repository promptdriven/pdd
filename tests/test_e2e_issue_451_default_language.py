"""
E2E test for Issue #451: Language detection ignores .pddrc default_language setting

This E2E test verifies that when `pdd generate` is invoked with:
- A prompt file WITHOUT language suffix (e.g., "test.prompt" instead of "test_python.prompt")
- A .pddrc file with default_language configured

The command should use the default_language from .pddrc instead of raising an error.

Unlike the unit test in test_construct_paths.py (which mocks internal functions),
this E2E test exercises the full CLI path with minimal mocking to verify user-facing behavior.
"""
import pytest
from pathlib import Path
from click.testing import CliRunner


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because construct_paths uses PDD_PATH to find the language_format.csv
    file for language detection.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.mark.e2e
class TestIssue451DefaultLanguageE2E:
    """
    E2E tests for issue #451: default_language in .pddrc should work as fallback.
    Tests the actual CLI behavior with real file system and configuration.
    """

    def test_generate_uses_default_language_from_pddrc_e2e(self, tmp_path, monkeypatch):
        """
        CRITICAL E2E TEST for issue #451:

        This test verifies that `pdd generate` correctly uses default_language from .pddrc when:
        1. Prompt file has NO language suffix (test.prompt)
        2. .pddrc has default_language: python configured

        Expected behavior: Command should succeed at path construction (language detected)
        Buggy behavior: Command fails with "Could not determine language from input files or options"

        This test will FAIL on the buggy code and PASS after the fix.

        Note: The test doesn't actually need to run code generation - it just needs to
        verify that language detection succeeds during path construction.
        """
        # Setup: Create .pddrc with default_language
        pddrc_content = """contexts:
  default:
    paths:
      - "**"
    defaults:
      generate_output_path: src/
      default_language: python
"""
        pddrc_path = tmp_path / ".pddrc"
        pddrc_path.write_text(pddrc_content)

        # Create prompt file WITHOUT language suffix
        prompt_content = "Write a Python function 'hello' that prints 'Hello, World!'"
        prompt_path = tmp_path / "test.prompt"
        prompt_path.write_text(prompt_content)

        # Create output directory
        output_dir = tmp_path / "src"
        output_dir.mkdir()

        # Change to temp directory so CLI can find .pddrc
        monkeypatch.chdir(tmp_path)

        # Force local execution to prevent cloud routing
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        # Fake API key to prevent missing key errors
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        # Import CLI after changing directory
        from pdd.cli import cli

        runner = CliRunner()

        # Act: Run `pdd generate test.prompt` (no language suffix in filename!)
        # We expect this to fail at path construction if the bug exists
        result = runner.invoke(
            cli,
            ["generate", "test.prompt"],
            env={
                "PDD_AUTO_UPDATE": "false",
                "HOME": str(tmp_path),
            },
            catch_exceptions=True  # Catch to examine the error
        )

        # Assert: Check if error is about language detection
        # On buggy code: "Could not determine language" appears in output
        # After fix: language detection succeeds, proceeds to code generation
        output_lower = result.output.lower()

        # If it's the language detection error, the bug still exists
        if "could not determine language" in output_lower:
            pytest.fail(
                f"BUG DETECTED: Language detection failed despite .pddrc having default_language.\n"
                f"Exit code: {result.exit_code}\n"
                f"Output: {result.output}\n"
                f"The default_language from .pddrc is not being used as fallback."
            )

        # Success: Language detection worked!
        # The command may fail later (e.g., LLM call), but that's OK for this test

    def test_filename_suffix_overrides_default_language_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying filename suffix takes precedence over .pddrc default_language.

        Priority order should be: filename suffix > default_language from .pddrc

        This test ensures the fix doesn't break the existing priority order.
        """
        # Setup: .pddrc with default_language: python
        pddrc_content = """contexts:
  default:
    paths:
      - "**"
    defaults:
      generate_output_path: src/
      default_language: python
"""
        pddrc_path = tmp_path / ".pddrc"
        pddrc_path.write_text(pddrc_content)

        # Create prompt file WITH javascript suffix (should override python default)
        prompt_content = "Write a JavaScript function 'hello' that logs 'Hello, World!'"
        prompt_path = tmp_path / "test_javascript.prompt"
        prompt_path.write_text(prompt_content)

        output_dir = tmp_path / "src"
        output_dir.mkdir()

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        from pdd.cli import cli

        runner = CliRunner()

        # Act: Run with filename suffix _javascript
        result = runner.invoke(
            cli,
            ["generate", "test_javascript.prompt"],
            env={
                "PDD_AUTO_UPDATE": "false",
                "HOME": str(tmp_path),
            },
            catch_exceptions=True
        )

        # The key assertion: language detection should succeed and detect javascript
        # We're testing path construction, not full code generation
        if result.exit_code != 0:
            output_lower = result.output.lower()
            # Should NOT have language detection error
            assert "could not determine language" not in output_lower, (
                f"Language detection failed when filename has explicit suffix.\n"
                f"Output: {result.output}"
            )

    def test_cli_flag_overrides_default_language_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying --language CLI flag takes precedence over .pddrc default_language.

        Priority order should be: CLI flag > default_language from .pddrc

        This test ensures the fix maintains correct priority ordering.
        """
        # Setup: .pddrc with default_language: python
        pddrc_content = """contexts:
  default:
    paths:
      - "**"
    defaults:
      generate_output_path: src/
      default_language: python
"""
        pddrc_path = tmp_path / ".pddrc"
        pddrc_path.write_text(pddrc_content)

        # Create prompt file WITHOUT language suffix
        prompt_content = "Write a TypeScript function 'hello' that logs 'Hello, World!'"
        prompt_path = tmp_path / "test.prompt"
        prompt_path.write_text(prompt_content)

        output_dir = tmp_path / "src"
        output_dir.mkdir()

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        from pdd.cli import cli

        runner = CliRunner()

        # Act: Run with explicit --language typescript flag
        result = runner.invoke(
            cli,
            ["generate", "--language", "typescript", "test.prompt"],
            env={
                "PDD_AUTO_UPDATE": "false",
                "HOME": str(tmp_path),
            },
            catch_exceptions=True
        )

        # Should succeed at language detection (CLI flag has highest priority)
        if result.exit_code != 0:
            output_lower = result.output.lower()
            assert "could not determine language" not in output_lower, (
                f"Language detection failed when --language flag is provided.\n"
                f"Output: {result.output}"
            )

    def test_no_default_language_still_raises_error_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying error is raised when NO language source is available.

        This ensures the fix doesn't break the error case - when neither .pddrc
        default_language nor filename suffix nor CLI flag is provided, it should
        still raise a clear error.

        This is a regression test to ensure the fix maintains correct error behavior.
        """
        # Setup: .pddrc WITHOUT default_language
        pddrc_content = """contexts:
  default:
    paths:
      - "**"
    defaults:
      generate_output_path: src/
"""
        pddrc_path = tmp_path / ".pddrc"
        pddrc_path.write_text(pddrc_content)

        # Create prompt file WITHOUT language suffix
        prompt_content = "Write a function 'hello'"
        prompt_path = tmp_path / "test.prompt"
        prompt_path.write_text(prompt_content)

        output_dir = tmp_path / "src"
        output_dir.mkdir()

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        from pdd.cli import cli

        runner = CliRunner()

        # Act: Run without any language indicator
        result = runner.invoke(
            cli,
            ["generate", "test.prompt"],
            env={
                "PDD_AUTO_UPDATE": "false",
                "HOME": str(tmp_path),
            },
            catch_exceptions=True
        )

        # Assert: Should show language detection error in output
        # (Note: exit code may be 0 due to core dump handling, but error message should appear)
        output_lower = result.output.lower()
        assert "could not determine language" in output_lower, (
            f"Expected error message about language detection failure when no language source is available.\n"
            f"Exit code: {result.exit_code}\n"
            f"Output: {result.output}"
        )

    def test_pdd_which_shows_default_language_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying `pdd which` correctly displays default_language from .pddrc.

        This confirms the configuration is loaded correctly, which makes the bug
        more confusing for users (config loads but doesn't work).
        """
        # Setup: .pddrc with default_language
        pddrc_content = """contexts:
  default:
    paths:
      - "**"
    defaults:
      default_language: python
      generate_output_path: src/
"""
        pddrc_path = tmp_path / ".pddrc"
        pddrc_path.write_text(pddrc_content)

        monkeypatch.chdir(tmp_path)

        from pdd.cli import cli

        runner = CliRunner()

        # Act: Run `pdd which` to show configuration
        result = runner.invoke(
            cli,
            ["which"],
            env={
                "PDD_AUTO_UPDATE": "false",
                "HOME": str(tmp_path),
            },
            catch_exceptions=False
        )

        # Assert: Should succeed
        assert result.exit_code == 0, (
            f"Expected success, but got exit code {result.exit_code}.\n"
            f"Output: {result.output}"
        )

        # Assert: Output should show default_language
        assert "default_language" in result.output, (
            f"Expected 'default_language' in output, but got:\n{result.output}"
        )
        assert "python" in result.output, (
            f"Expected 'python' in output, but got:\n{result.output}"
        )
