"""
Test that the diff-analysis schema in prompts.py includes all fields
that the prompt template asks the LLM to return.

Issue: The prompt template (prompt_code_diff_LLM.prompt) instructs the LLM
to return fields like `canRegenerate`, `regenerationRisk`, and `hiddenKnowledge`,
but the JSON schema in prompts.py didn't include these fields. When the LLM
returns these fields, validation fails with:

    "Additional properties are not allowed ('canRegenerate', 'hiddenKnowledge',
    'regenerationRisk' were unexpected)"

This test ensures the schema properties match what the prompt template requests.
"""

import pytest
import re
from pathlib import Path


class TestDiffAnalysisSchemaCompleteness:
    """Tests that diff-analysis schema includes all prompt-requested fields."""

    @pytest.fixture
    def prompt_template_path(self):
        """Path to the prompt template."""
        return Path(__file__).parent.parent / "prompts" / "prompt_code_diff_LLM.prompt"

    @pytest.fixture
    def prompt_template_content(self, prompt_template_path):
        """Load the prompt template content."""
        return prompt_template_path.read_text()

    def test_schema_includes_canRegenerate(self):
        """Schema must include canRegenerate field that prompt template requests."""
        # Import here to get fresh module state
        from pdd.server.routes import prompts
        import importlib
        importlib.reload(prompts)

        # Get the schema by inspecting the module
        # We check the DiffAnalysisResult Pydantic model which defines expected fields
        from pdd.server.routes.prompts import DiffAnalysisResult

        # The Pydantic model has the field
        assert hasattr(DiffAnalysisResult.model_fields, 'canRegenerate') or \
               'canRegenerate' in DiffAnalysisResult.model_fields, \
            "DiffAnalysisResult model should have canRegenerate field"

    def test_schema_includes_regenerationRisk(self):
        """Schema must include regenerationRisk field that prompt template requests."""
        from pdd.server.routes.prompts import DiffAnalysisResult

        assert 'regenerationRisk' in DiffAnalysisResult.model_fields, \
            "DiffAnalysisResult model should have regenerationRisk field"

    def test_schema_includes_hiddenKnowledge(self):
        """Schema must include hiddenKnowledge field that prompt template requests."""
        from pdd.server.routes.prompts import DiffAnalysisResult

        assert 'hiddenKnowledge' in DiffAnalysisResult.model_fields, \
            "DiffAnalysisResult model should have hiddenKnowledge field"

    def test_output_schema_dict_matches_pydantic_model(self):
        """
        The output_schema dict passed to llm_invoke must include all fields
        from the prompt template that the Pydantic model expects.

        This is the key test - it verifies the schema dict has:
        - canRegenerate
        - regenerationRisk
        - hiddenKnowledge

        Without these, OpenAI will reject responses containing them due to
        additionalProperties: false.
        """
        # We need to check the actual schema dict built in the endpoint
        # Since it's built inside a function, we'll verify by checking
        # what fields the prompt template asks for

        prompt_path = Path(__file__).parent.parent / "prompts" / "prompt_code_diff_LLM.prompt"
        prompt_content = prompt_path.read_text()

        # The prompt template asks for these fields (check the numbered list)
        required_by_prompt = []

        # Look for field definitions in the prompt
        if '"canRegenerate"' in prompt_content:
            required_by_prompt.append('canRegenerate')
        if '"regenerationRisk"' in prompt_content:
            required_by_prompt.append('regenerationRisk')
        if '"hiddenKnowledge"' in prompt_content:
            required_by_prompt.append('hiddenKnowledge')

        # Now verify these are in the schema dict
        # We'll read the prompts.py source and check if these fields are defined
        prompts_path = Path(__file__).parent.parent / "pdd" / "server" / "routes" / "prompts.py"
        prompts_source = prompts_path.read_text()

        # Find the output_schema definition for diff-analysis endpoint
        # Look for the schema dict that's passed to llm_invoke
        missing_fields = []

        for field in required_by_prompt:
            # Check if the field is in the output_schema properties
            # Pattern: "fieldName": { in the output_schema section
            if f'"{field}"' not in prompts_source or \
               f'"{field}":' not in prompts_source:
                # More specific check - look in the output_schema section
                # This is a simplified check
                schema_section = prompts_source[prompts_source.find('output_schema = {'):prompts_source.find('result = llm_invoke(')]
                if f'"{field}"' not in schema_section:
                    missing_fields.append(field)

        assert not missing_fields, (
            f"BUG: output_schema in prompts.py is missing fields that prompt template requests: {missing_fields}\n"
            f"The prompt template asks the LLM to return these fields, but they're not in the schema.\n"
            f"When additionalProperties: false is set, OpenAI will reject responses with these fields.\n"
            f"Error: 'Additional properties are not allowed ({', '.join(missing_fields)} were unexpected)'"
        )

    def test_prompt_template_and_schema_field_alignment(self):
        """
        Comprehensive test: extract all fields from prompt template and verify
        each one exists in the output_schema.
        """
        prompt_path = Path(__file__).parent.parent / "prompts" / "prompt_code_diff_LLM.prompt"
        prompt_content = prompt_path.read_text()

        # Extract field names from the prompt template's JSON structure description
        # Looking for patterns like: 1. "fieldName": ...
        field_pattern = r'^\d+\.\s*"(\w+)":'
        fields_in_prompt = re.findall(field_pattern, prompt_content, re.MULTILINE)

        # Also look for fields defined with quotes in the response format section
        quoted_fields = re.findall(r'"(\w+)":\s*(?:integer|boolean|string|array|object|\{)', prompt_content)

        all_prompt_fields = set(fields_in_prompt + quoted_fields)

        # Read the schema from prompts.py
        prompts_path = Path(__file__).parent.parent / "pdd" / "server" / "routes" / "prompts.py"
        prompts_source = prompts_path.read_text()

        # Find output_schema section (for diff-analysis endpoint)
        # Look between "output_schema = {" and the next "result = llm_invoke"
        schema_start = prompts_source.find('output_schema = {')
        if schema_start == -1:
            pytest.skip("Could not find output_schema in prompts.py")

        schema_end = prompts_source.find('result = llm_invoke(', schema_start)
        schema_section = prompts_source[schema_start:schema_end]

        # Check which prompt fields are missing from schema
        missing = []
        for field in all_prompt_fields:
            if f'"{field}"' not in schema_section:
                missing.append(field)

        # These are the critical fields we know must be present
        critical_fields = {'canRegenerate', 'regenerationRisk', 'hiddenKnowledge'}
        critical_missing = critical_fields.intersection(set(missing))

        assert not critical_missing, (
            f"SCHEMA MISMATCH: These fields are requested by prompt template but missing from output_schema:\n"
            f"  {critical_missing}\n\n"
            f"This causes OpenAI to reject LLM responses with:\n"
            f"  'Additional properties are not allowed'\n\n"
            f"Fix: Add these fields to output_schema in prompts.py"
        )
