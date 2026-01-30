"""
E2E Test for Issue #437: Fingerprint metadata files have null hash fields after generate

This test exercises the full CLI path from `pdd generate` to verify that after a successful
generate command, the fingerprint metadata files in `.pdd/meta/` contain actual content hashes
instead of null values.

The bug: After running `pdd generate`, the fingerprint metadata files have all hash fields
(prompt_hash, code_hash, example_hash, test_hash) set to `null` instead of containing
actual SHA-256 content hashes.

Bug location:
- pdd/operation_log.py:338 - The @log_operation decorator calls save_fingerprint() without
  the required `paths` parameter, causing all hashes to be None.

This E2E test:
1. Creates a test project with a prompt file
2. Runs `pdd generate` command through Click's CliRunner
3. Verifies that the resulting fingerprint metadata file contains actual hash values (not null)

The test should FAIL on buggy code (all hashes are null) and PASS once the fix is applied.

Issue: https://github.com/promptdriven/pdd/issues/437
"""

import json
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner


class TestIssue437NullHashesE2E:
    """
    E2E tests for Issue #437: Verify CLI generate command creates fingerprints
    with actual content hashes instead of null values.
    """

    def test_pdd_generate_creates_fingerprint_with_valid_hashes(self, tmp_path, monkeypatch):
        """
        E2E Test: `pdd generate` should create fingerprint metadata with actual hash values

        This test runs the full CLI path and verifies that when generating code from a prompt,
        the resulting fingerprint metadata file contains valid SHA-256 hashes for all fields
        instead of null values.

        Expected behavior (after fix):
        - Fingerprint file should contain valid 64-character hex hashes for prompt_hash, code_hash, etc.
        - Hashes should be different from null/None

        Bug behavior (Issue #437):
        - All hash fields are null: {"prompt_hash": null, "code_hash": null, ...}
        - This breaks fingerprint-based change detection feature
        """
        # 1. Set up test project structure
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()
        monkeypatch.chdir(project_dir)

        # Create a simple prompt file
        prompt_file = project_dir / "hello_Python.prompt"
        prompt_content = """# Prompt: Hello World Function

Create a simple Python function that prints "Hello, World!".

## Requirements
- Function should be named `say_hello`
- Function should print "Hello, World!" to stdout
- Include a docstring

## Example
```python
def say_hello():
    \"\"\"Print a friendly greeting.\"\"\"
    print("Hello, World!")
```
"""
        prompt_file.write_text(prompt_content)

        # 2. Mock the LLM call to avoid actual API calls and costs
        # We need to mock code_generator_main to return a successful result
        mock_result = {
            "basename": "hello",
            "language": "Python",
            "code_file": str(project_dir / "hello.py"),
            "success": True,
        }

        def mock_code_generator_main(*args, **kwargs):
            """Mock code generator that creates output files and returns success."""
            # Create the output code file
            code_file = project_dir / "hello.py"
            code_content = '''"""Hello World module."""

def say_hello():
    """Print a friendly greeting."""
    print("Hello, World!")


if __name__ == "__main__":
    say_hello()
'''
            code_file.write_text(code_content)

            # Create example file (optional but often generated)
            example_file = project_dir / "hello_example.py"
            example_content = '''"""Example usage of hello module."""
from hello import say_hello

say_hello()
'''
            example_file.write_text(example_content)

            # Return success tuple: (message, cost, model)
            return ("Generated hello.py successfully", 0.001, "mock-gpt-4")

        # 3. Patch the code generator and run the CLI command
        with patch("pdd.commands.generate.code_generator_main", side_effect=mock_code_generator_main):
            from pdd.cli import cli

            runner = CliRunner()
            result = runner.invoke(
                cli,
                ["generate", str(prompt_file)],
                catch_exceptions=False,  # Let exceptions propagate for debugging
            )

        # 5. THE KEY ASSERTIONS

        # Check that command succeeded
        assert result.exit_code == 0, (
            f"Command failed with exit code {result.exit_code}\n"
            f"Output: {result.output}\n"
            f"Exception: {result.exception}"
        )

        # 6. Verify the fingerprint metadata file exists
        meta_dir = project_dir / ".pdd" / "meta"
        fingerprint_file = meta_dir / "hello_Python.json"

        assert fingerprint_file.exists(), (
            f"Fingerprint metadata file not found at {fingerprint_file}\n"
            f"Contents of .pdd/meta/: {list(meta_dir.glob('*')) if meta_dir.exists() else 'directory does not exist'}"
        )

        # 7. Read and parse the fingerprint metadata
        fingerprint_data = json.loads(fingerprint_file.read_text())

        # 8. THE BUG CHECK: Verify hash fields are NOT null
        hash_fields = ["prompt_hash", "code_hash", "example_hash", "test_hash"]
        null_hashes = []

        for field in hash_fields:
            if field in fingerprint_data:
                value = fingerprint_data[field]
                if value is None:
                    null_hashes.append(field)

        if null_hashes:
            pytest.fail(
                f"BUG DETECTED (Issue #437): Fingerprint metadata has null hash fields!\n\n"
                f"Null fields: {null_hashes}\n\n"
                f"Full fingerprint data:\n{json.dumps(fingerprint_data, indent=2)}\n\n"
                f"Root cause: The @log_operation decorator at pdd/operation_log.py:338\n"
                f"calls save_fingerprint() without the required 'paths' parameter,\n"
                f"causing calculate_current_hashes() to return an empty dict.\n\n"
                f"Expected: All hash fields should contain 64-character hex SHA-256 hashes.\n"
                f"Actual: Hash fields are null, breaking fingerprint-based change detection.\n\n"
                f"This breaks PDD's core feature of detecting which files have changed\n"
                f"and intelligently deciding when to regenerate code."
            )

        # 9. Additional validation: Verify hashes are valid SHA-256 format
        # SHA-256 hashes are 64 hexadecimal characters
        for field in hash_fields:
            if field in fingerprint_data and fingerprint_data[field] is not None:
                hash_value = fingerprint_data[field]
                assert isinstance(hash_value, str), (
                    f"Hash field {field} should be a string, got {type(hash_value)}"
                )
                assert len(hash_value) == 64, (
                    f"Hash field {field} should be 64 characters (SHA-256), got {len(hash_value)}"
                )
                assert all(c in "0123456789abcdef" for c in hash_value.lower()), (
                    f"Hash field {field} should be hexadecimal, got {hash_value}"
                )

    def test_pdd_generate_with_mock_llm_minimal(self, tmp_path, monkeypatch):
        """
        Minimal E2E test for Issue #437 with simpler setup.

        This test focuses purely on the fingerprint hash bug without
        requiring full project setup.
        """
        project_dir = tmp_path / "minimal_project"
        project_dir.mkdir()
        monkeypatch.chdir(project_dir)

        # Create minimal prompt
        prompt_file = project_dir / "test_Python.prompt"
        prompt_file.write_text("# Test\nCreate a test function.")

        # Mock to create minimal output
        def mock_generator(*args, **kwargs):
            (project_dir / "test.py").write_text("def test(): pass")
            return ("Success", 0.0, "mock-model")

        with patch("pdd.commands.generate.code_generator_main", side_effect=mock_generator):
            from pdd.cli import cli
            runner = CliRunner()
            result = runner.invoke(cli, ["generate", str(prompt_file)], catch_exceptions=False)

        assert result.exit_code == 0, f"Command failed: {result.output}"

        # Check fingerprint
        fingerprint_file = project_dir / ".pdd" / "meta" / "test_Python.json"
        assert fingerprint_file.exists(), "Fingerprint file not created"

        fingerprint_data = json.loads(fingerprint_file.read_text())

        # THE BUG: Check if prompt_hash is null
        if fingerprint_data.get("prompt_hash") is None:
            pytest.fail(
                f"BUG Issue #437: prompt_hash is null!\n"
                f"Fingerprint: {json.dumps(fingerprint_data, indent=2)}\n\n"
                f"The @log_operation decorator doesn't pass 'paths' to save_fingerprint(),\n"
                f"causing all hash fields to be null instead of containing SHA-256 hashes."
            )

        # Verify prompt_hash is a valid SHA-256 hash
        prompt_hash = fingerprint_data.get("prompt_hash")
        assert prompt_hash is not None, "prompt_hash should not be None"
        assert isinstance(prompt_hash, str), "prompt_hash should be a string"
        assert len(prompt_hash) == 64, f"prompt_hash should be 64 chars, got {len(prompt_hash)}"
        assert all(c in "0123456789abcdef" for c in prompt_hash.lower()), (
            f"prompt_hash should be hex, got {prompt_hash}"
        )
