"""
E2E Test for OpenAI strict mode: ALL properties must be in 'required' array

This test verifies that when using structured output with OpenAI models,
ALL properties in the JSON schema are included in the 'required' array,
not just those without default values.

The bug: Pydantic's model_json_schema() only includes fields WITHOUT defaults
in the 'required' array. OpenAI strict mode now requires ALL properties to be
listed in 'required', causing this error:
    "Invalid schema for response_format 'ExtractedCode': In context=(),
     'required' is required to be supplied and to be an array including
     every key in properties. Missing 'focus'."

This test should FAIL on buggy code and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from pydantic import BaseModel, Field


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestOpenAIRequiredArraySchema:
    """
    Tests for OpenAI strict mode requirement: ALL properties must be in 'required'.
    """

    def test_pydantic_raw_schema_excludes_optional_fields_from_required(self, monkeypatch):
        """
        Documents that Pydantic's model_json_schema() excludes fields with defaults
        from the 'required' array. This is expected Pydantic behavior.

        The ExtractedCode model has:
        - focus: str = Field(default="", ...)        # Has default - excluded from required
        - explanation: str = Field(default="", ...)  # Has default - excluded from required
        - extracted_code: str = Field(...)           # No default - included in required

        This test verifies the Pydantic behavior that necessitates our fix in llm_invoke.
        """
        from pdd.postprocess import ExtractedCode

        # Get the schema as Pydantic generates it (without our fix)
        schema = ExtractedCode.model_json_schema()

        # Check what properties exist
        properties = set(schema.get('properties', {}).keys())
        required = set(schema.get('required', []))

        print(f"\nProperties in schema: {properties}")
        print(f"Properties in required: {required}")

        # Verify Pydantic's behavior: only non-default fields are in required
        assert 'extracted_code' in required, "extracted_code should be in required (no default)"
        assert 'focus' not in required, "focus should NOT be in required (has default) - this is why we need the fix"
        assert 'explanation' not in required, "explanation should NOT be in required (has default) - this is why we need the fix"

        # Verify all properties exist
        assert properties == {'focus', 'explanation', 'extracted_code'}

    def test_llm_invoke_fixes_required_array_for_openai(self, monkeypatch):
        """
        Test that llm_invoke patches the schema to include all properties in 'required'
        before sending to OpenAI.
        """
        from pdd.llm_invoke import llm_invoke
        import pandas as pd
        from collections import namedtuple

        # Force local execution
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")

        # Custom model with a field that has a default (will be excluded from required by Pydantic)
        class TestModelWithDefaults(BaseModel):
            required_field: str = Field(description="This has no default")
            optional_field: str = Field(default="default_value", description="This has a default")

        # Track captured schemas
        captured_schemas = []

        def capture_completion(*args, **kwargs):
            response_format = kwargs.get("response_format")
            if response_format and response_format.get("type") == "json_schema":
                json_schema = response_format.get("json_schema", {})
                schema = json_schema.get("schema", {})
                captured_schemas.append({
                    "name": json_schema.get("name"),
                    "properties": set(schema.get("properties", {}).keys()),
                    "required": set(schema.get("required", [])),
                    "schema": schema,
                })

            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = '{"required_field": "test", "optional_field": "value"}'
            mock_response.choices[0].finish_reason = "stop"
            mock_response.model = "gpt-4o"
            mock_response.usage = MagicMock()
            mock_response.usage.prompt_tokens = 10
            mock_response.usage.completion_tokens = 5
            mock_response.usage.total_tokens = 15
            return mock_response

        # Mock model data for OpenAI
        MockModelInfoData = namedtuple("MockModelInfoData", [
            "provider", "model", "input", "output", "coding_arena_elo",
            "structured_output", "base_url", "api_key",
            "max_tokens", "max_completion_tokens",
            "reasoning_type", "max_reasoning_tokens"
        ])

        mock_data = [
            MockModelInfoData(
                provider='OpenAI', model='gpt-4o', input=0.02, output=0.03,
                coding_arena_elo=1500, structured_output=True, base_url="",
                api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="",
                reasoning_type='none', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in mock_data])
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch('pdd.llm_invoke.litellm.completion', side_effect=capture_completion):
                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001, "input_tokens": 10, "output_tokens": 5}):
                    try:
                        llm_invoke(
                            prompt="Return a test object",
                            input_json={"query": "test"},
                            strength=0.5,
                            temperature=0.1,
                            output_pydantic=TestModelWithDefaults,
                            verbose=False,
                        )
                    except Exception as e:
                        # We might get an error due to mocking, but we still captured the schema
                        print(f"Note: llm_invoke raised {type(e).__name__}: {e}")

        # Verify schema was captured
        assert len(captured_schemas) > 0, "No schema was captured from llm_invoke call"

        schema_info = captured_schemas[0]
        properties = schema_info["properties"]
        required = schema_info["required"]

        print(f"\nCaptured schema for {schema_info['name']}:")
        print(f"  Properties: {properties}")
        print(f"  Required: {required}")

        # THE BUG CHECK: All properties must be in required
        assert properties == required, (
            f"BUG DETECTED: llm_invoke did not fix the 'required' array.\n"
            f"Properties: {properties}\n"
            f"Required: {required}\n"
            f"Missing: {properties - required}\n\n"
            f"The schema sent to OpenAI must have ALL properties in 'required'."
        )
