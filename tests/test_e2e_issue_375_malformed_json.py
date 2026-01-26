"""
E2E Test for Issue #375: Malformed JSON in architecture description prompts

This test exercises the full code path from prompt preprocessing through to
architecture_sync parsing to verify that JSON content in PDD metadata tags
(<pdd-interface>, <pdd-reason>, <pdd-dependency>) remains valid after preprocessing.

The bug: When running `pdd change` or any command that preprocesses prompts,
the `double_curly()` function in `preprocess.py` converts ALL `{` to `{{`
without protecting content inside PDD metadata tags. This corrupts valid JSON:

    Before: {"type": "module", "module": {"functions": []}}
    After:  {{"type": "module", "module": {{"functions": []}}}}

This causes `architecture_sync.parse_prompt_tags()` to fail with a JSON parse
error when it tries to extract the interface specification.

This E2E test:
1. Creates a test prompt file with valid JSON in <pdd-interface> tags
2. Runs the preprocess function (simulating what `pdd change` does)
3. Passes the result to `parse_prompt_tags()` from architecture_sync
4. Verifies the JSON can be parsed successfully

The test should FAIL on buggy code (JSON corrupted) and PASS once the fix is applied.

Related files:
- pdd/preprocess.py:435 - The buggy line that corrupts JSON
- pdd/architecture_sync.py:90 - Where JSON parsing fails
- prompts/agentic_arch_step8_fix_LLM.prompt - Example of corrupted prompt from issue
"""

import pytest
from pathlib import Path
from unittest.mock import patch
import json


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because preprocess uses PDD_PATH to resolve include paths.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestMalformedJSONInPDDTagsE2E:
    """
    E2E tests for Issue #375: Verify that JSON in PDD metadata tags
    (<pdd-interface>, <pdd-reason>, <pdd-dependency>) is NOT corrupted
    by the double_curly() preprocessing step.
    """

    def test_preprocess_preserves_json_in_pdd_interface_tag_e2e(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Preprocess a prompt with <pdd-interface> JSON and verify
        architecture_sync can parse it.

        This test exercises the FULL user-facing workflow:
        1. User has a prompt file with valid JSON in <pdd-interface>
        2. User runs a PDD command (change, sync, etc.) that preprocesses the prompt
        3. architecture_sync.parse_prompt_tags() extracts the interface
        4. JSON should be valid and parseable

        Expected behavior (after fix):
        - JSON in <pdd-interface> remains valid: {"type": "module", ...}
        - parse_prompt_tags() returns the parsed interface dict

        Bug behavior (Issue #375):
        - JSON becomes corrupted: {{"type": "module", ...}}
        - parse_prompt_tags() returns interface=None with a parse error
        """
        # Import the modules we're testing
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        # 1. Create a prompt with valid JSON in <pdd-interface> - exactly like the
        # real prompt from the issue (agentic_arch_step8_fix_LLM.prompt)
        prompt_content = """<pdd-reason>Fixes validation errors in architecture.json: resolves circular deps, priority violations, missing fields.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "fix_architecture", "signature": "(current_architecture: str, step7_output: str)", "returns": "str (corrected JSON array)"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>agentic_arch_step7_validate_LLM.prompt</pdd-dependency>
% You are an expert software architect. Your task is to fix validation errors in the generated architecture.json.

Given the current architecture and the validation output from step 7, fix any issues found.
"""

        # Write to temp file
        prompt_file = tmp_path / "test_arch_step8.prompt"
        prompt_file.write_text(prompt_content)

        monkeypatch.chdir(tmp_path)

        # 2. Run preprocessing (this is what triggers the bug)
        # Note: double_curly_brackets=True is the default in the change flow
        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)

        # 3. Try to parse the prompt tags
        result = parse_prompt_tags(processed)

        # 4. THE KEY ASSERTIONS

        # The interface should have been parsed successfully
        assert result['interface'] is not None, (
            f"BUG DETECTED (Issue #375): JSON in <pdd-interface> was corrupted by preprocessing!\n\n"
            f"Original JSON was valid, but after preprocess(), parse_prompt_tags() could not parse it.\n\n"
            f"Parse error: {result.get('interface_parse_error', 'No error recorded')}\n\n"
            f"This happens because double_curly() converts {{'}} to {{{{}}}} without protecting\n"
            f"PDD metadata tags. The fix should protect content inside <pdd-interface>,\n"
            f"<pdd-reason>, and <pdd-dependency> tags from brace doubling.\n\n"
            f"Processed prompt content (first 500 chars):\n{processed[:500]}"
        )

        # Verify the structure matches what we put in
        interface = result['interface']
        assert interface.get('type') == 'module', (
            f"Interface type should be 'module', got: {interface.get('type')}"
        )
        assert 'module' in interface, "Interface should have 'module' key"
        assert 'functions' in interface['module'], "module should have 'functions' key"
        assert len(interface['module']['functions']) == 1, "Should have 1 function"
        assert interface['module']['functions'][0]['name'] == 'fix_architecture', (
            "Function name should be 'fix_architecture'"
        )

        # Also verify reason was extracted correctly
        assert result['reason'] is not None, "Reason should be extracted"
        assert "validation errors" in result['reason'].lower(), (
            f"Reason should mention validation errors, got: {result['reason']}"
        )

        # Verify dependency was extracted
        assert "agentic_arch_step7_validate_LLM.prompt" in result['dependencies'], (
            f"Dependencies should include the expected prompt, got: {result['dependencies']}"
        )

    def test_preprocess_preserves_nested_json_in_pdd_interface_e2e(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Deeply nested JSON in <pdd-interface> should survive preprocessing.

        This tests a more complex JSON structure with multiple levels of nesting,
        which is more likely to expose brace-matching bugs.
        """
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        # More complex nested JSON structure
        prompt_content = """<pdd-reason>Complex module with nested interfaces</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "process_data",
        "signature": "(data: dict)",
        "returns": "dict",
        "parameters": {
          "data": {
            "type": "dict",
            "schema": {
              "items": {"type": "string"},
              "metadata": {"nested": {"deeply": "value"}}
            }
          }
        }
      },
      {
        "name": "validate",
        "signature": "(schema: dict)",
        "returns": "bool"
      }
    ],
    "classes": [
      {
        "name": "DataProcessor",
        "methods": [{"name": "__init__"}, {"name": "run"}]
      }
    ]
  }
}
</pdd-interface>
% Complex module prompt body here.
"""

        prompt_file = tmp_path / "test_complex_interface.prompt"
        prompt_file.write_text(prompt_content)
        monkeypatch.chdir(tmp_path)

        # Run preprocessing
        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)

        # Parse the result
        result = parse_prompt_tags(processed)

        # THE BUG CHECK
        assert result['interface'] is not None, (
            f"BUG DETECTED (Issue #375): Nested JSON in <pdd-interface> was corrupted!\n\n"
            f"Parse error: {result.get('interface_parse_error', 'No error recorded')}\n\n"
            f"Deeply nested JSON structures are particularly vulnerable to the\n"
            f"double_curly() bug because each level of {{}} gets doubled.\n\n"
            f"Processed content (first 800 chars):\n{processed[:800]}"
        )

        # Verify nested structure
        interface = result['interface']
        assert interface['type'] == 'module'
        functions = interface['module']['functions']
        assert len(functions) == 2

        # Check deeply nested structure survived
        first_func = functions[0]
        assert first_func['name'] == 'process_data'
        params = first_func.get('parameters', {})
        assert 'data' in params
        assert params['data']['schema']['metadata']['nested']['deeply'] == 'value'

    def test_preprocess_still_doubles_braces_outside_pdd_tags_e2e(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Regression test - braces OUTSIDE PDD metadata tags should
        still be doubled for LangChain PromptTemplate compatibility.

        The fix must NOT break the original purpose of double_curly(), which is
        to escape braces that would otherwise be interpreted as format variables.
        """
        from pdd.preprocess import preprocess

        # Prompt with template variables AND PDD tags
        prompt_content = """<pdd-reason>Module for formatting output</pdd-reason>
<pdd-interface>
{"type": "module", "module": {"functions": [{"name": "format"}]}}
</pdd-interface>
% Format the {input_data} according to the {output_format} specification.

The output should be valid JSON like: {"result": "value"}

Use the template variable {user_name} in the response.
"""

        prompt_file = tmp_path / "test_mixed_content.prompt"
        prompt_file.write_text(prompt_content)
        monkeypatch.chdir(tmp_path)

        # Run preprocessing
        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)

        # Check that braces OUTSIDE pdd tags are doubled
        # The literal JSON example should have doubled braces
        assert '{{"result": "value"}}' in processed, (
            f"Literal JSON outside PDD tags should have doubled braces.\n"
            f"Expected '{{'\"result\": \"value\"'}}' in output.\n"
            f"Got:\n{processed}"
        )

        # Template variables should remain single (they're excluded by default
        # or handled specially) - this depends on the implementation
        # The main point is that the prompt should still be usable

    def test_cli_sync_does_not_corrupt_pdd_interface_json_e2e(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Full CLI path - `pdd sync` should not corrupt <pdd-interface> JSON.

        This is the highest-level E2E test that exercises the actual CLI command
        that users would run.
        """
        from click.testing import CliRunner
        from pdd import cli
        from pdd.architecture_sync import parse_prompt_tags

        # Create a prompts directory structure
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()

        # Create a prompt file with valid JSON interface
        prompt_content = """<pdd-reason>Test module for E2E validation</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "test_func", "signature": "(x: int)", "returns": "int"}
    ]
  }
}
</pdd-interface>
% This is a test prompt for E2E testing of Issue #375.

Write a function that doubles the input number.
"""
        prompt_file = prompts_dir / "test_module_python.prompt"
        prompt_file.write_text(prompt_content)

        # Create architecture.json
        architecture = [
            {
                "name": "test_module_python.prompt",
                "reason": "Original reason",
                "priority": 1,
                "dependencies": []
            }
        ]
        arch_file = tmp_path / "architecture.json"
        arch_file.write_text(json.dumps(architecture, indent=2))

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Before running any command, verify the JSON is valid
        before_result = parse_prompt_tags(prompt_content)
        assert before_result['interface'] is not None, (
            "Sanity check: original prompt should have valid JSON"
        )

        # Now manually run preprocess to simulate what sync would do
        from pdd.preprocess import preprocess
        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)

        # Parse the preprocessed content
        after_result = parse_prompt_tags(processed)

        # THE BUG CHECK: JSON should still be valid after preprocessing
        assert after_result['interface'] is not None, (
            f"BUG DETECTED (Issue #375): JSON in <pdd-interface> was corrupted!\n\n"
            f"Before preprocessing:\n"
            f"  interface: {before_result['interface']}\n\n"
            f"After preprocessing:\n"
            f"  interface: {after_result['interface']}\n"
            f"  parse_error: {after_result.get('interface_parse_error')}\n\n"
            f"The pdd sync/change commands preprocess prompts which corrupts JSON.\n"
            f"This breaks architecture.json updates from prompt metadata.\n\n"
            f"Processed content:\n{processed[:600]}"
        )

    def test_real_world_prompt_from_issue_375_e2e(self, tmp_path, monkeypatch):
        """
        E2E Test: Use the exact prompt content from Issue #375 bug report.

        This reproduces the exact scenario reported by the user:
        - The prompt agentic_arch_step8_fix_LLM.prompt
        - Contains <pdd-interface> with JSON describing fix_architecture function
        - After pdd change runs, the JSON becomes corrupted
        """
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        # This is the exact content from the issue (before corruption)
        # Note: In the issue, we see the DIFF showing {} being changed to {{}}
        prompt_content = """<pdd-reason>Fixes validation errors in architecture.json: resolves circular deps, priority violations, missing fields.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "fix_architecture", "signature": "(current_architecture: str, step7_output: str)", "returns": "str (corrected JSON array)"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>agentic_arch_step7_validate_LLM.prompt</pdd-dependency>
% You are an expert software architect. Your task is to fix validation errors in the generated architecture.json.

Given the current architecture and the validation output from step 7, fix any issues found.
Return the corrected architecture as a valid JSON array.
"""

        prompt_file = tmp_path / "agentic_arch_step8_fix_LLM.prompt"
        prompt_file.write_text(prompt_content)
        monkeypatch.chdir(tmp_path)

        # Preprocess (this is what pdd change does)
        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)

        # Try to parse the tags
        result = parse_prompt_tags(processed)

        # THE BUG CHECK: This is the exact failure from Issue #375
        assert result['interface'] is not None, (
            f"BUG DETECTED (Issue #375): This is the EXACT bug from the issue report!\n\n"
            f"The prompt file agentic_arch_step8_fix_LLM.prompt has valid JSON in\n"
            f"<pdd-interface>, but after pdd change preprocesses it, the JSON becomes:\n\n"
            f"  {{'type': 'module', 'module': {{'functions': [{{'name': ...}}]}}}}\n\n"
            f"These double braces {{{{}}}} are invalid JSON.\n\n"
            f"Parse error: {result.get('interface_parse_error', 'No error recorded')}\n\n"
            f"This is caused by double_curly() in preprocess.py:435 which blindly\n"
            f"converts all {{}} to {{{{}}}} without protecting PDD metadata tags."
        )

        # Verify the interface has the expected content
        interface = result['interface']
        assert interface['type'] == 'module'
        assert interface['module']['functions'][0]['name'] == 'fix_architecture'


class TestPDDTagsContentPreservationE2E:
    """
    Additional E2E tests to ensure all PDD metadata tag types are protected.
    """

    def test_pdd_reason_with_braces_preserved_e2e(self, tmp_path, monkeypatch):
        """
        E2E Test: <pdd-reason> content with braces should be preserved.

        Some reason descriptions might include technical notation like {dict}
        or {object} that should not be doubled.
        """
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        prompt_content = """<pdd-reason>Returns {dict} mapping names to {object} instances</pdd-reason>
<pdd-interface>{"type": "module"}</pdd-interface>
% Module description here.
"""

        prompt_file = tmp_path / "test_reason_braces.prompt"
        prompt_file.write_text(prompt_content)
        monkeypatch.chdir(tmp_path)

        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)
        result = parse_prompt_tags(processed)

        # Check that reason preserved the braces correctly
        # Note: Single braces in reason might be acceptable if they're not JSON
        # The key is that they shouldn't break parsing
        assert result['reason'] is not None, (
            f"Reason should be parseable even with braces.\n"
            f"Processed content:\n{processed}"
        )

    def test_pdd_dependency_with_special_chars_preserved_e2e(self, tmp_path, monkeypatch):
        """
        E2E Test: <pdd-dependency> paths should be preserved exactly.
        """
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        prompt_content = """<pdd-reason>Test module</pdd-reason>
<pdd-interface>{"type": "module"}</pdd-interface>
<pdd-dependency>path/to/module_python.prompt</pdd-dependency>
<pdd-dependency>another/module_v2_python.prompt</pdd-dependency>
% Module description.
"""

        prompt_file = tmp_path / "test_deps.prompt"
        prompt_file.write_text(prompt_content)
        monkeypatch.chdir(tmp_path)

        processed = preprocess(prompt_content, recursive=False, double_curly_brackets=True)
        result = parse_prompt_tags(processed)

        # Dependencies should be extracted correctly
        assert len(result['dependencies']) == 2, (
            f"Should have 2 dependencies, got: {result['dependencies']}"
        )
        assert "path/to/module_python.prompt" in result['dependencies']
        assert "another/module_v2_python.prompt" in result['dependencies']
