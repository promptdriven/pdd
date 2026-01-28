"""E2E tests for Issue #409: Environment variable pollution from -e flag."""

import json
import os
from pathlib import Path
from unittest.mock import patch

import pytest


def get_project_root() -> Path:
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pdd" / "commands").is_dir():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


@pytest.mark.e2e
class TestEnvVarPollutionE2E:

    def test_env_vars_do_not_pollute_os_environ_after_command(self, tmp_path: Path, monkeypatch):
        """Test that -e flag variables don't persist in os.environ after command completion."""
        from click.testing import CliRunner
        from pdd.cli import cli

        prompt_file = tmp_path / "test_prompt.txt"
        prompt_file.write_text("Generate a function that adds two numbers.")

        test_vars = {
            "TEST_VAR_409": "test_value",
            "API_KEY_409": "secret_api_key_12345",
            "SECRET_TOKEN_409": "secret_token_xyz",
            "DB_PASSWORD_409": "db_password_456"
        }

        for key in test_vars:
            monkeypatch.delenv(key, raising=False)

        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")
            runner = CliRunner()
            args = ["generate", str(prompt_file), "--output", str(tmp_path / "output.py")]
            for key, value in test_vars.items():
                args.extend(["-e", f"{key}={value}"])
            result = runner.invoke(cli, args, catch_exceptions=False)

        polluted = []
        security_vars = []

        for key in test_vars:
            if key in os.environ:
                polluted.append({"key": key, "value": os.environ[key]})
                if key in ["API_KEY_409", "SECRET_TOKEN_409", "DB_PASSWORD_409"]:
                    security_vars.append(key)

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
        """Test that multiple commands don't accumulate environment variables."""
        from click.testing import CliRunner
        from pdd.cli import cli

        (tmp_path / "prompt1.txt").write_text("Generate function one.")
        (tmp_path / "prompt2.txt").write_text("Generate function two.")
        (tmp_path / "prompt3.txt").write_text("Generate function three.")

        monkeypatch.delenv("CMD1_VAR", raising=False)
        monkeypatch.delenv("CMD2_VAR", raising=False)

        with patch('pdd.commands.generate.code_generator_main') as mock_gen:
            mock_gen.return_value = ("# Generated code", False, 0.0, "test-model")
            runner = CliRunner()

            runner.invoke(cli, [
                "generate", str(tmp_path / "prompt1.txt"),
                "--output", str(tmp_path / "output1.py"),
                "-e", "CMD1_VAR=value1"
            ], catch_exceptions=False)

            cmd1_polluted = "CMD1_VAR" in os.environ

            runner.invoke(cli, [
                "generate", str(tmp_path / "prompt2.txt"),
                "--output", str(tmp_path / "output2.py"),
                "-e", "CMD2_VAR=value2"
            ], catch_exceptions=False)

            cmd1_leaked = "CMD1_VAR" in os.environ
            cmd2_polluted = "CMD2_VAR" in os.environ

            runner.invoke(cli, [
                "generate", str(tmp_path / "prompt3.txt"),
                "--output", str(tmp_path / "output3.py"),
            ], catch_exceptions=False)

            cmd3_sees_cmd1 = "CMD1_VAR" in os.environ
            cmd3_sees_cmd2 = "CMD2_VAR" in os.environ

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
