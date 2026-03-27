"""
E2E tests for operation fingerprint hash population.

Verifies that after running CLI commands (generate, example), the fingerprint
metadata files in .pdd/meta/ contain actual SHA-256 content hashes instead of
null values.  Only the LLM call is mocked; the entire fingerprint pipeline
(log_operation decorator -> save_fingerprint -> calculate_current_hashes) runs
for real so any fix strategy is validated end-to-end.

Bug reference: https://github.com/promptdriven/pdd/issues/437
"""

import json
import pytest
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def pdd_project(tmp_path, monkeypatch):
    """
    Create a minimal PDD project directory with a prompt file and a
    generated code file, then chdir into it.

    Returns (project_dir, basename, language).
    """
    project = tmp_path / "project"
    project.mkdir()
    monkeypatch.chdir(project)

    # Directories PDD expects
    (project / "prompts").mkdir()
    (project / "src").mkdir()
    (project / "tests").mkdir()
    (project / "examples").mkdir()

    basename = "hello"
    language = "Python"

    # Prompt file – must follow {basename}_{language}.prompt convention
    prompt = project / "prompts" / f"{basename}_{language}.prompt"
    prompt.write_text(
        "% Hello Module\n"
        "Create a function called `say_hello` that prints 'Hello, World!'.\n"
    )

    # Pre-create the code output file at the default path that
    # get_pdd_file_paths resolves to (project root, not src/)
    code_file = project / f"{basename}.py"
    code_file.write_text(
        'def say_hello():\n'
        '    """Print a greeting."""\n'
        '    print("Hello, World!")\n'
    )

    return project, basename, language


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class TestGenerateFingerprintHashes:
    """CLI-level tests that pdd generate populates fingerprint hashes."""

    def test_generate_creates_fingerprint_with_non_null_hashes(self, pdd_project):
        """
        After `pdd generate`, the fingerprint file must contain real SHA-256
        hashes for at least prompt_hash (prompt file always exists).

        Bug #437: The @log_operation decorator calls save_fingerprint() without
        the paths parameter, so all hashes end up null.
        """
        project, basename, language = pdd_project
        prompt_path = str(project / "prompts" / f"{basename}_{language}.prompt")

        def fake_code_generator_main(**kwargs):
            """Mock that skips the LLM but returns the expected 4-tuple."""
            return ("generated code", False, 0.001, "mock-model")

        runner = CliRunner()

        with patch(
            "pdd.commands.generate.code_generator_main",
            side_effect=fake_code_generator_main,
        ):
            result = runner.invoke(
                _cli(),
                ["generate", prompt_path],
                catch_exceptions=False,
            )

        assert result.exit_code == 0, (
            f"pdd generate failed (exit {result.exit_code}):\n{result.output}"
        )

        # Read the fingerprint metadata
        fp_file = project / ".pdd" / "meta" / f"{basename}_{language}.json"
        assert fp_file.exists(), (
            f"Fingerprint file not created at {fp_file}. "
            f"Contents of .pdd/: {list((project / '.pdd').rglob('*')) if (project / '.pdd').exists() else 'missing'}"
        )

        fp_data = json.loads(fp_file.read_text())

        # ---- Bug detection assertions ----
        # With bug #437, all hash fields are null because the decorator
        # never passes paths to save_fingerprint().
        assert fp_data.get("prompt_hash") is not None, (
            f"Bug #437: prompt_hash is null after pdd generate.\n"
            f"The @log_operation decorator must pass paths to save_fingerprint().\n"
            f"Fingerprint: {json.dumps(fp_data, indent=2)}"
        )

        # Validate SHA-256 format (64 hex chars)
        prompt_hash = fp_data["prompt_hash"]
        assert len(prompt_hash) == 64 and all(c in "0123456789abcdef" for c in prompt_hash), (
            f"prompt_hash should be a 64-char hex SHA-256 string, got: {prompt_hash!r}"
        )

        # code_hash should also be populated since the code file exists
        code_hash = fp_data.get("code_hash")
        assert code_hash is not None, (
            f"Bug #437: code_hash is null after pdd generate.\n"
            f"Fingerprint: {json.dumps(fp_data, indent=2)}"
        )
        assert len(code_hash) == 64 and all(c in "0123456789abcdef" for c in code_hash), (
            f"code_hash should be a 64-char hex SHA-256 string, got: {code_hash!r}"
        )

    def test_generate_fingerprint_command_field_is_generate(self, pdd_project):
        """
        Verify the fingerprint records 'generate' as the command and includes
        standard metadata fields (pdd_version, timestamp).
        """
        project, basename, language = pdd_project
        prompt_path = str(project / "prompts" / f"{basename}_{language}.prompt")

        def fake_code_generator_main(**kwargs):
            return ("code", False, 0.0, "mock")

        runner = CliRunner()

        with patch(
            "pdd.commands.generate.code_generator_main",
            side_effect=fake_code_generator_main,
        ):
            result = runner.invoke(
                _cli(),
                ["generate", prompt_path],
                catch_exceptions=False,
            )

        assert result.exit_code == 0

        fp_file = project / ".pdd" / "meta" / f"{basename}_{language}.json"
        assert fp_file.exists()
        fp_data = json.loads(fp_file.read_text())

        assert fp_data["command"] == "generate"
        assert "pdd_version" in fp_data
        assert "timestamp" in fp_data


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _cli():
    """Lazy import to avoid side-effects at collection time."""
    from pdd.cli import cli
    return cli
