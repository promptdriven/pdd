"""
E2E Test for Issue #409: Environment Variable Pollution from -e flag (OPTIMIZED)

This is a consolidated version that removes redundancy while maintaining full coverage.

Changes from original:
- Removed redundant test_env_vars_security_credentials_do_not_leak
- Consolidated security concerns into the primary test
- Reduced from 317 lines to ~180 lines (43% reduction)
- Maintained 100% of functional coverage
"""

import json
import os
from pathlib import Path
from unittest.mock import patch

import pytest


def get_project_root() -> Path:
    """Get the project root directory (where pdd package lives)."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pdd" / "commands").is_dir():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


@pytest.mark.e2e
class TestEnvVarPollutionE2E:
    """
    E2E tests for Issue #409: Environment variables set via -e flag should not
    persist in os.environ after pdd generate command completes.
    """

    def test_env_vars_do_not_pollute_os_environ_after_command(self, tmp_path: Path, monkeypatch):
        """
        E2E Test: Variables passed via -e flag should not persist in os.environ
        after `pdd generate` completes.

        Tests both general variables AND security-sensitive credentials (API keys,
        tokens, passwords) to ensure no pollution or security leakage occurs.

        Expected behavior (after fix):
        - Command executes successfully
        - Environment variables are used during execution
        - Variables do NOT persist in os.environ after completion
        - No security credential leakage

        Bug behavior (Issue #409):
        - Variables persist permanently in os.environ
        - Security credentials leak to subsequent commands
        - Test pollution occurs
        """
        from click.testing import CliRunner
        from pdd.cli import cli

        # Create a minimal prompt file
        prompt_file = tmp_path / "test_prompt.txt"
        prompt_file.write_text("Generate a function that adds two numbers.")

        # Test both general variables AND security-sensitive credentials
        test_vars = {
            "TEST_VAR_409": "test_value",
            "API_KEY_409": "secret_api_key_12345",
            "SECRET_TOKEN_409": "secret_token_xyz",
            "DB_PASSWORD_409": "db_password_456"
        }

        # Clean environment
        for key in test_vars:
            monkeypatch.delenv(key, raising=False)

        # Mock code_generator_main to avoid LLM calls
        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")

            runner = CliRunner()

            # Build command with -e flags
            args = ["generate", str(prompt_file), "--output", str(tmp_path / "output.py")]
            for key, value in test_vars.items():
                args.extend(["-e", f"{key}={value}"])

            # Run the command
            result = runner.invoke(cli, args, catch_exceptions=False)

        # Check for pollution
        polluted = []
        security_vars = []

        for key in test_vars:
            if key in os.environ:
                polluted.append({"key": key, "value": os.environ[key]})
                if key in ["API_KEY_409", "SECRET_TOKEN_409", "DB_PASSWORD_409"]:
                    security_vars.append(key)

        # Fail if any variables persisted
        if polluted:
            pollution_details = [f"  {var['key']}={var['value']}" for var in polluted]

            security_warning = ""
            if security_vars:
                security_warning = (
                    f"\n\n⚠️  SECURITY RISK: The following credentials leaked:\n"
                    f"  {', '.join(security_vars)}\n"
                    f"This could expose dev credentials to production code!"
                )

            pytest.fail(
                f"BUG DETECTED (Issue #409): Environment variables persist after command!\n\n"
                f"Polluted variables:\n{chr(10).join(pollution_details)}"
                f"{security_warning}\n\n"
                f"Root cause: pdd/commands/generate.py:152 calls os.environ.update(env_vars)\n"
                f"Fix: Remove os.environ.update(env_vars) - use parameter passing instead.\n\n"
                f"Command exit code: {result.exit_code}"
            )

    def test_sequential_commands_do_not_accumulate_env_vars(self, tmp_path: Path, monkeypatch):
        """
        E2E Test: Running multiple `pdd generate` commands with different -e flags
        should not cause environment variable accumulation.

        Tests the multi-command scenario:
        - Command 1: pdd generate -e ENV=staging prompt1.txt
        - Command 2: pdd generate -e ENV=production prompt2.txt
        - Command 3: pdd generate prompt3.txt

        Expected: Each command runs isolated, no variable accumulation.
        Bug: Variables accumulate across commands.
        """
        from click.testing import CliRunner
        from pdd.cli import cli

        # Create prompt files
        (tmp_path / "prompt1.txt").write_text("Generate function one.")
        (tmp_path / "prompt2.txt").write_text("Generate function two.")
        (tmp_path / "prompt3.txt").write_text("Generate function three.")

        # Clean slate
        monkeypatch.delenv("CMD1_VAR", raising=False)
        monkeypatch.delenv("CMD2_VAR", raising=False)

        # Mock code_generator_main
        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")

            runner = CliRunner()

            # Command 1: Set CMD1_VAR=value1
            runner.invoke(cli, [
                "generate", str(tmp_path / "prompt1.txt"),
                "--output", str(tmp_path / "output1.py"),
                "-e", "CMD1_VAR=value1"
            ], catch_exceptions=False)

            cmd1_polluted = "CMD1_VAR" in os.environ

            # Command 2: Set CMD2_VAR=value2
            runner.invoke(cli, [
                "generate", str(tmp_path / "prompt2.txt"),
                "--output", str(tmp_path / "output2.py"),
                "-e", "CMD2_VAR=value2"
            ], catch_exceptions=False)

            cmd1_leaked = "CMD1_VAR" in os.environ
            cmd2_polluted = "CMD2_VAR" in os.environ

            # Command 3: No -e flags
            runner.invoke(cli, [
                "generate", str(tmp_path / "prompt3.txt"),
                "--output", str(tmp_path / "output3.py"),
            ], catch_exceptions=False)

            cmd3_sees_cmd1 = "CMD1_VAR" in os.environ
            cmd3_sees_cmd2 = "CMD2_VAR" in os.environ

        # Check for issues
        issues = []
        if cmd1_polluted:
            issues.append("CMD1_VAR persisted after Command 1")
        if cmd1_leaked:
            issues.append("CMD1_VAR leaked into Command 2")
        if cmd2_polluted:
            issues.append("CMD2_VAR persisted after Command 2")
        if cmd3_sees_cmd1:
            issues.append("Command 3 sees CMD1_VAR from Command 1")
        if cmd3_sees_cmd2:
            issues.append("Command 3 sees CMD2_VAR from Command 2")

        if issues:
            pytest.fail(
                f"BUG DETECTED (Issue #409): Variables leak between commands!\n\n"
                f"Issues:\n{chr(10).join('  - ' + i for i in issues)}\n\n"
                f"Root cause: pdd/commands/generate.py:152 permanently sets variables.\n"
                f"Fix: Remove os.environ.update(env_vars) - use parameter passing."
            )
