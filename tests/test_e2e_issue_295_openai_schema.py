"""
E2E Test for Issue #295: OpenAI strict mode requires additionalProperties: false

This test exercises the full CLI path from `pdd generate` down to the llm_invoke
layer to verify that the JSON schema sent to OpenAI includes `additionalProperties: false`.

The bug: When using `pdd generate`, the postprocess step uses the ExtractedCode Pydantic
model with structured output. The standard completion path (llm_invoke.py:1899-1906)
passes the raw Pydantic schema without adding `additionalProperties: false`, causing
OpenAI to reject the request with:
    "Invalid schema for response_format 'ExtractedCode': In context=(),
     'additionalProperties' is required to be supplied and to be false."

This E2E test:
1. Sets up a temp directory with a simple prompt file
2. Runs the generate command through Click's CliRunner
3. Mocks litellm.completion at the very edge to capture the schema
4. Verifies the schema includes additionalProperties: false

The test should FAIL on buggy code (missing additionalProperties: false) and
PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
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


class TestOpenAIStrictModeSchemaE2E:
    """
    E2E tests for Issue #295: Verify additionalProperties: false is included in
    JSON schemas sent to OpenAI models via the standard completion path.
    """

    def test_pdd_generate_openai_schema_includes_additional_properties_false(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: pdd generate -> postprocess -> llm_invoke -> litellm.completion

        This test runs the full CLI path and verifies that when the ExtractedCode
        Pydantic model is used for structured output, the schema sent to OpenAI
        includes `additionalProperties: false`.

        Expected behavior:
        - The schema should include additionalProperties: false
        - OpenAI should accept the request (not reject with schema error)

        Bug behavior (Issue #295):
        - Schema is missing additionalProperties
        - OpenAI rejects: "'additionalProperties' is required to be supplied and to be false"
        """
        # 1. Create a simple prompt file (use _python suffix for language detection)
        prompt_content = """I need a Python program that prints "Hello, World!"."""
        (tmp_path / "test_python.prompt").write_text(prompt_content)

        monkeypatch.chdir(tmp_path)

        # Force local execution to prevent cloud routing
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        # Ensure we have an OpenAI API key (fake for mocking)
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Track the schema that would be sent to OpenAI
        captured_schemas = []

        # 2. Mock litellm.completion and litellm.responses
        # OpenAI gpt-5* models use the Responses API path, others use completion
        call_count = [0]

        def mock_completion_with_counter(*args, **kwargs):
            """Mock that handles litellm.completion calls."""
            call_count[0] += 1

            # Capture schema if it's a structured output call
            response_format = kwargs.get("response_format")
            if response_format and response_format.get("type") == "json_schema":
                json_schema = response_format.get("json_schema", {})
                schema = json_schema.get("schema", {})
                captured_schemas.append({
                    "call_number": call_count[0],
                    "source": "completion",
                    "name": json_schema.get("name"),
                    "strict": json_schema.get("strict"),
                    "schema": schema,
                    "additionalProperties": schema.get("additionalProperties"),
                })

            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].finish_reason = "stop"
            mock_response.model = "gpt-5-nano"
            mock_response.usage = MagicMock()
            mock_response.usage.prompt_tokens = 100
            mock_response.usage.completion_tokens = 50
            mock_response.usage.total_tokens = 150

            # First call is code generation (not structured output)
            # Second call is postprocess (structured output with ExtractedCode)
            if response_format and response_format.get("type") == "json_schema":
                # This is a structured output call (postprocess)
                mock_response.choices[0].message.content = '''{"focus": "hello world", "explanation": "Simple print statement", "extracted_code": "print(\\"Hello, World!\\")"}'''
            else:
                # Code generation call
                mock_response.choices[0].message.content = '''```python
print("Hello, World!")
```'''

            return mock_response

        def mock_responses_api(*args, **kwargs):
            """Mock that handles litellm.responses calls (OpenAI Responses API)."""
            call_count[0] += 1

            # Capture schema from text.format block (Responses API uses different structure)
            text_block = kwargs.get("text", {})
            format_block = text_block.get("format", {})
            if format_block.get("type") == "json_schema":
                schema = format_block.get("schema", {})
                captured_schemas.append({
                    "call_number": call_count[0],
                    "source": "responses",
                    "name": format_block.get("name"),
                    "strict": format_block.get("strict"),
                    "schema": schema,
                    "additionalProperties": schema.get("additionalProperties"),
                })

            # Build mock response matching Responses API structure
            mock_response = MagicMock()

            # Responses API returns output as list of items with content
            mock_content_item = MagicMock()
            mock_content_item.text = '''{"focus": "hello world", "explanation": "Simple print statement", "extracted_code": "print(\\"Hello, World!\\")"}'''

            mock_message_item = MagicMock()
            mock_message_item.type = "message"
            mock_message_item.content = [mock_content_item]

            mock_response.output = [mock_message_item]
            mock_response.model = "gpt-5-nano"
            mock_response.usage = MagicMock()
            mock_response.usage.prompt_tokens = 100
            mock_response.usage.completion_tokens = 50
            mock_response.usage.total_tokens = 150

            return mock_response

        # 3. Mock the model data to use only OpenAI models
        import pandas as pd
        from collections import namedtuple

        MockModelInfoData = namedtuple("MockModelInfoData", [
            "provider", "model", "input", "output", "coding_arena_elo",
            "structured_output", "base_url", "api_key",
            "max_tokens", "max_completion_tokens",
            "reasoning_type", "max_reasoning_tokens"
        ])

        openai_model_data = [
            MockModelInfoData(
                provider='OpenAI', model='gpt-5-nano', input=0.02, output=0.03,
                coding_arena_elo=1500, structured_output=True, base_url="",
                api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="",
                reasoning_type='none', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in openai_model_data])
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)

        # 4. Run the CLI command
        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch('pdd.llm_invoke.litellm.completion', side_effect=mock_completion_with_counter):
                with patch('pdd.llm_invoke.litellm.responses', side_effect=mock_responses_api):
                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001, "input_tokens": 100, "output_tokens": 50}):
                        from pdd import cli

                        runner = CliRunner()
                        result = runner.invoke(cli.cli, [
                            "--local",  # Force local execution
                            "generate",
                            "test_python.prompt",
                            "--output", "output.py"
                        ], catch_exceptions=False)

        # 5. THE KEY ASSERTIONS
        # There should be at least one captured schema (from postprocess calling llm_invoke)
        assert len(captured_schemas) > 0, \
            f"No structured output schemas were captured - postprocess may not have been called. CLI output: {result.output}"

        # Find the ExtractedCode schema call
        extracted_code_schemas = [s for s in captured_schemas if s.get("name") == "ExtractedCode"]
        assert len(extracted_code_schemas) > 0, \
            f"ExtractedCode schema not found in captured calls. Found: {[s.get('name') for s in captured_schemas]}"

        # THE BUG CHECK: additionalProperties must be False
        for schema_info in extracted_code_schemas:
            assert schema_info.get("additionalProperties") == False, (
                f"BUG DETECTED (Issue #295): ExtractedCode schema is missing 'additionalProperties: false'.\n"
                f"OpenAI strict mode requires additionalProperties to be explicitly set to false.\n"
                f"Schema received: {schema_info.get('schema')}\n"
                f"additionalProperties value: {schema_info.get('additionalProperties')}\n\n"
                f"This causes OpenAI to reject requests with:\n"
                f"  'Invalid schema for response_format \"ExtractedCode\": In context=(), "
                f"\"additionalProperties\" is required to be supplied and to be false.'"
            )

    def test_any_pydantic_model_gets_additional_properties_false_for_openai(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Any Pydantic model used with llm_invoke should get additionalProperties: false

        This is a more targeted test that directly calls llm_invoke with a custom
        Pydantic model to verify the fix applies to all models, not just ExtractedCode.
        """
        from pydantic import BaseModel
        from pdd.llm_invoke import llm_invoke
        import pandas as pd
        from collections import namedtuple

        # Force local execution
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Custom Pydantic model for testing
        class CustomTestModel(BaseModel):
            name: str
            value: int

        # Track captured schemas
        captured_schemas = []

        def capture_completion(*args, **kwargs):
            response_format = kwargs.get("response_format")
            if response_format and response_format.get("type") == "json_schema":
                json_schema = response_format.get("json_schema", {})
                schema = json_schema.get("schema", {})
                captured_schemas.append({
                    "name": json_schema.get("name"),
                    "additionalProperties": schema.get("additionalProperties"),
                    "schema": schema,
                })

            # Return mock response
            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = '{"name": "test", "value": 42}'
            mock_response.choices[0].finish_reason = "stop"
            mock_response.model = "gpt-5-nano"
            mock_response.usage = MagicMock()
            mock_response.usage.prompt_tokens = 10
            mock_response.usage.completion_tokens = 5
            mock_response.usage.total_tokens = 15
            return mock_response

        # Set up mock model data - OpenAI only
        MockModelInfoData = namedtuple("MockModelInfoData", [
            "provider", "model", "input", "output", "coding_arena_elo",
            "structured_output", "base_url", "api_key",
            "max_tokens", "max_completion_tokens",
            "reasoning_type", "max_reasoning_tokens"
        ])

        openai_model_data = [
            MockModelInfoData(
                provider='OpenAI', model='gpt-5-nano', input=0.02, output=0.03,
                coding_arena_elo=1500, structured_output=True, base_url="",
                api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="",
                reasoning_type='none', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in openai_model_data])
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)

        # Run llm_invoke directly
        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch('pdd.llm_invoke.litellm.completion', side_effect=capture_completion):
                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001, "input_tokens": 10, "output_tokens": 5}):
                    response = llm_invoke(
                        prompt="Return a test object",
                        input_json={"query": "test"},
                        strength=0.5,
                        temperature=0.1,
                        output_pydantic=CustomTestModel,
                        verbose=False,
                    )

        # Verify schema was captured
        assert len(captured_schemas) > 0, "No schema was captured from llm_invoke call"

        # THE BUG CHECK
        schema_info = captured_schemas[0]
        assert schema_info.get("additionalProperties") == False, (
            f"BUG DETECTED (Issue #295): Schema for {schema_info.get('name')} is missing "
            f"'additionalProperties: false'.\n"
            f"This causes OpenAI strict mode to fail.\n"
            f"Schema: {schema_info.get('schema')}"
        )
