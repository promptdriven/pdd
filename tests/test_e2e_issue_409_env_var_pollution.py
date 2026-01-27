"""
E2E Test for Issue #409: Environment Variable Pollution from -e flag

This test exercises the full CLI path to verify that environment variables set via
the `-e`/`--env` flag do NOT persist in os.environ after command completion.

The Bug:
- Users run: pdd generate -e API_KEY=secret123 -e MODULE=orders prompt.txt
- Code at generate.py:152 calls os.environ.update(env_vars) with no cleanup
- Variables persist permanently in os.environ for entire process lifetime
- Causes test pollution, security leaks, and unpredictable multi-command behavior

E2E Test Strategy:
- Use subprocess to run pdd generate in a fresh Python process
- Pass environment variables via -e flags
- After command completes, check if those variables persist in os.environ
- Use a Python script that runs the command then inspects os.environ

The test should:
- FAIL on the current buggy code (pollution detected)
- PASS once os.environ.update(env_vars) is removed from generate.py:152
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List

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

        This is the primary E2E test for Issue #409. It simulates real-world usage:
        1. User runs: pdd generate -e SECRET=value1 -e API_KEY=value2 prompt.txt
        2. Command completes successfully
        3. Variables should NOT remain in os.environ

        Expected behavior (after fix):
        - Command executes successfully
        - Environment variables are used during execution
        - Variables do NOT persist in os.environ after completion
        - Process environment is clean

        Bug behavior (Issue #409):
        - Command executes successfully
        - Variables are set in os.environ at generate.py:152
        - Variables PERSIST permanently (no cleanup)
        - All subsequent code sees these variables
        """
        from click.testing import CliRunner
        from pdd.cli import cli
        from unittest.mock import patch

        # Create a minimal prompt file
        prompt_file = tmp_path / "test_prompt.txt"
        prompt_file.write_text("Generate a function that adds two numbers.")

        # Define test variables that should NOT persist
        test_vars = {
            "TEST_VAR_409_E2E": "value_from_e_flag",
            "SECRET_KEY_409_E2E": "secret123",
            "API_TOKEN_409_E2E": "token456"
        }

        # Clean environment: ensure test vars don't exist before
        for key in test_vars:
            monkeypatch.delenv(key, raising=False)

        # Mock code_generator_main to avoid LLM calls
        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")

            runner = CliRunner()

            # Build command args
            args = [
                "generate",
                str(prompt_file),
                "--output", str(tmp_path / "output.py"),
            ]

            # Add -e flags for each test variable
            for key, value in test_vars.items():
                args.extend(["-e", f"{key}={value}"])

            # Run the command (this will trigger the bug at generate.py:152)
            result = runner.invoke(cli, args, catch_exceptions=False)

        # After command completes, check if variables persisted
        polluted = []
        for key in test_vars:
            if key in os.environ:
                polluted.append({"key": key, "value": os.environ[key]})

        # THE BUG CHECK: No test variables should persist
        if polluted:
            pollution_details = [
                f"  {var['key']}={var['value']}" for var in polluted
            ]

            pytest.fail(
                f"BUG DETECTED (Issue #409): Environment variables persist after command completion!\n\n"
                f"After running 'pdd generate -e VAR=value', the following variables\n"
                f"remained in os.environ:\n"
                f"{chr(10).join(pollution_details)}\n\n"
                f"Root cause: pdd/commands/generate.py:152 calls os.environ.update(env_vars)\n"
                f"with no cleanup mechanism. Variables persist for entire process lifetime.\n\n"
                f"Impact:\n"
                f"- Test pollution: Variables leak between test cases\n"
                f"- Security risk: Credentials persist across commands\n"
                f"- Unpredictable behavior: Multi-command scripts accumulate variables\n\n"
                f"Fix: Remove os.environ.update(env_vars) from generate.py:152.\n"
                f"The env_vars parameter already passes variables correctly.\n\n"
                f"Command exit code: {result.exit_code}\n"
                f"Command output: {result.output[:200] if result.output else 'N/A'}"
            )

    def test_sequential_commands_do_not_accumulate_env_vars(self, tmp_path: Path, monkeypatch):
        """
        E2E Test: Running multiple `pdd generate` commands with different -e flags
        should not cause environment variable accumulation.

        This tests the real-world scenario described in Issue #409:
        - Command 1: pdd generate -e ENV=staging prompt1.txt
        - Command 2: pdd generate -e ENV=production prompt2.txt
        - Command 3: pdd generate prompt3.txt

        Expected behavior (after fix):
        - Each command runs with its own environment variables
        - Variables from Command 1 do NOT affect Command 2
        - Command 3 runs with clean environment (no accumulated vars)

        Bug behavior (Issue #409):
        - Command 1 sets ENV=staging permanently
        - Command 2 sets ENV=production (now BOTH values exist or last wins)
        - Command 3 inherits all variables from previous commands
        """
        from click.testing import CliRunner
        from pdd.cli import cli
        from unittest.mock import patch

        # Create prompt files
        (tmp_path / "prompt1.txt").write_text("Generate function one.")
        (tmp_path / "prompt2.txt").write_text("Generate function two.")
        (tmp_path / "prompt3.txt").write_text("Generate function three.")

        # Clean slate
        monkeypatch.delenv("CMD1_VAR", raising=False)
        monkeypatch.delenv("CMD2_VAR", raising=False)

        # Mock code_generator_main to avoid LLM calls
        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")

            runner = CliRunner()
            results = []

            # Command 1: Set CMD1_VAR=value1
            result1 = runner.invoke(cli, [
                "generate", str(tmp_path / "prompt1.txt"),
                "--output", str(tmp_path / "output1.py"),
                "-e", "CMD1_VAR=value1"
            ], catch_exceptions=False)

            # Check if CMD1_VAR persists after Command 1
            cmd1_polluted = "CMD1_VAR" in os.environ
            results.append({"command": 1, "var": "CMD1_VAR", "persisted": cmd1_polluted})

            # Command 2: Set CMD2_VAR=value2 (different variable)
            result2 = runner.invoke(cli, [
                "generate", str(tmp_path / "prompt2.txt"),
                "--output", str(tmp_path / "output2.py"),
                "-e", "CMD2_VAR=value2"
            ], catch_exceptions=False)

            # Check pollution after Command 2
            cmd1_leaked = "CMD1_VAR" in os.environ  # Should NOT be present
            cmd2_polluted = "CMD2_VAR" in os.environ
            results.append({"command": 2, "cmd1_leaked": cmd1_leaked, "cmd2_persisted": cmd2_polluted})

            # Command 3: No -e flags (should have clean environment)
            result3 = runner.invoke(cli, [
                "generate", str(tmp_path / "prompt3.txt"),
                "--output", str(tmp_path / "output3.py"),
            ], catch_exceptions=False)

            # Check if any variables from previous commands are still present
            cmd3_sees_cmd1 = "CMD1_VAR" in os.environ
            cmd3_sees_cmd2 = "CMD2_VAR" in os.environ
            results.append({"command": 3, "sees_cmd1": cmd3_sees_cmd1, "sees_cmd2": cmd3_sees_cmd2})

        # Check for pollution
        issues = []

        # Check Command 1
        if results[0].get("persisted"):
            issues.append("Command 1: CMD1_VAR persisted after completion")

        # Check Command 2
        if results[1].get("cmd1_leaked"):
            issues.append("Command 2: CMD1_VAR from Command 1 leaked into Command 2")
        if results[1].get("cmd2_persisted"):
            issues.append("Command 2: CMD2_VAR persisted after completion")

        # Check Command 3
        if results[2].get("sees_cmd1"):
            issues.append("Command 3: Still sees CMD1_VAR from Command 1")
        if results[2].get("sees_cmd2"):
            issues.append("Command 3: Still sees CMD2_VAR from Command 2")

        if issues:
            pytest.fail(
                f"BUG DETECTED (Issue #409): Environment variables leak between commands!\n\n"
                f"Detected issues:\n"
                f"{chr(10).join('  - ' + issue for issue in issues)}\n\n"
                f"This is the multi-command scenario described in Issue #409:\n"
                f"Variables set via -e flag in one command persist and affect\n"
                f"subsequent commands, causing unpredictable behavior.\n\n"
                f"Root cause: pdd/commands/generate.py:152 calls os.environ.update(env_vars)\n"
                f"without cleanup. Each command accumulates variables from previous commands.\n\n"
                f"Test results: {json.dumps(results, indent=2)}"
            )

    def test_env_vars_security_credentials_do_not_leak(self, tmp_path: Path, monkeypatch):
        """
        E2E Test: Security-sensitive variables (API keys, tokens, secrets) should
        not persist after command completion.

        This tests the security implication described in Issue #409:
        - Morning: pdd generate -e API_KEY=dev_key_123 prompt1.txt
        - Afternoon: pdd generate prompt2.txt
        - BUG: prompt2.txt generation still uses API_KEY=dev_key_123

        This is a serious security issue: credentials intended for one operation
        leak into subsequent operations, potentially exposing dev credentials to
        production code generation.
        """
        from click.testing import CliRunner
        from pdd.cli import cli
        from unittest.mock import patch

        (tmp_path / "morning_prompt.txt").write_text("Generate dev code.")
        (tmp_path / "afternoon_prompt.txt").write_text("Generate prod code.")

        # Simulate morning: developer sets dev credentials
        monkeypatch.delenv("API_KEY_409", raising=False)
        monkeypatch.delenv("SECRET_TOKEN_409", raising=False)
        monkeypatch.delenv("DB_PASSWORD_409", raising=False)

        # Mock code_generator_main to avoid LLM calls
        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")

            runner = CliRunner()

            # Morning command: Set sensitive dev credentials
            morning_result = runner.invoke(cli, [
                "generate", str(tmp_path / "morning_prompt.txt"),
                "--output", str(tmp_path / "morning_output.py"),
                "-e", "API_KEY_409=dev_key_12345",
                "-e", "SECRET_TOKEN_409=dev_secret_xyz",
                "-e", "DB_PASSWORD_409=dev_password_456"
            ], catch_exceptions=False)

            # Check if credentials persisted (SECURITY BUG!)
            credentials_leaked = {
                "API_KEY_409": os.environ.get("API_KEY_409"),
                "SECRET_TOKEN_409": os.environ.get("SECRET_TOKEN_409"),
                "DB_PASSWORD_409": os.environ.get("DB_PASSWORD_409")
            }

        # Filter to only leaked credentials
        leaked_creds = {k: v for k, v in credentials_leaked.items() if v is not None}

        if leaked_creds:
            cred_list = [f"  {k}={v}" for k, v in leaked_creds.items()]

            pytest.fail(
                f"BUG DETECTED (Issue #409): SECURITY RISK - Credentials persist after command!\n\n"
                f"The following sensitive credentials remained in os.environ:\n"
                f"{chr(10).join(cred_list)}\n\n"
                f"Security Impact:\n"
                f"- Developer runs 'pdd generate -e API_KEY=dev_key' in morning\n"
                f"- Later runs 'pdd generate' for production code\n"
                f"- Production code generation uses dev_key from morning! ❌\n\n"
                f"This can lead to:\n"
                f"- Dev credentials leaked to production code\n"
                f"- Wrong API keys used for code generation\n"
                f"- Security violations and compliance issues\n\n"
                f"Root cause: pdd/commands/generate.py:152 permanently sets credentials\n"
                f"in os.environ with no cleanup. This violates principle of least privilege.\n\n"
                f"Fix: Remove os.environ.update(env_vars) - use parameter passing instead."
            )
