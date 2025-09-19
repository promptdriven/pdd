# To run this test:
# Option 1: From project root: pytest tests/test_think_tool.py
# Option 2: From project root: python -m pytest tests/test_think_tool.py

"""
Test Plan for edit_file_tool/think_tool.py
------------------------------------------

Objective:
Ensure the ThinkTool class provides a correctly formatted, Anthropic-compatible
tool definition and a reliable, no-op implementation.

Test Strategy:

1.  **`get_definition()` Method Tests**:
    -   `test_get_definition_returns_dict`: Verify the method returns a dictionary.
    -   `test_get_definition_has_correct_top_level_keys`: Check for the presence and correctness of the required top-level keys: 'name', 'description', and 'input_schema'.
    -   `test_get_definition_name_is_correct`: Assert the 'name' key is exactly "think". This is critical for API integration.
    -   `test_get_definition_description_is_meaningful`: Ensure the description is a non-empty string and contains key phrases like "private scratchpad" to confirm its intent is clearly communicated.
    -   `test_get_definition_input_schema_structure`: Validate the structure of the 'input_schema' dictionary, ensuring it has 'type', 'properties', and 'required' keys.
    -   `test_get_definition_input_schema_properties`: Drill down into 'properties' to confirm it defines the 'thought' parameter correctly (as a string with a description).
    -   `test_get_definition_input_schema_required_field`: Verify that the 'required' list correctly specifies 'thought' as the single required parameter.

2.  **`use()` Method Tests**:
    -   `test_use_returns_correct_static_output`: Confirm that a standard call to `use()` returns the exact expected dictionary: `{"output": "OK, I have noted that."}`.
    -   `test_use_is_a_no_op_for_various_strings`: Use `pytest.mark.parametrize` to test that the function's output is invariant to the string input. This demonstrates its no-op nature. Test cases will include:
        - An empty string.
        - A very long string.
        - A string with various special characters.
        - A multi-line string.
        - A string with unicode characters.
    -   `test_use_handles_non_string_input_gracefully`: Although type-hinted for a string, test that passing non-string inputs (like None, int, list) does not cause an exception, as the implementation ignores the input. This verifies robustness.
"""

import pytest
from typing import Any

from edit_file_tool.think_tool import ThinkTool


class TestThinkToolDefinition:
    """Tests for the ThinkTool.get_definition() method."""

    def test_get_definition_returns_dict(self) -> None:
        """Tests that get_definition returns a dictionary."""
        definition = ThinkTool.get_definition()
        assert isinstance(definition, dict)

    def test_get_definition_has_correct_top_level_keys(self) -> None:
        """Tests that the tool definition has the required top-level keys."""
        definition = ThinkTool.get_definition()
        # Using set for order-independent comparison of keys
        assert set(definition.keys()) == {"name", "description", "input_schema"}

    def test_get_definition_name_is_correct(self) -> None:
        """Tests that the tool's name is exactly 'think'."""
        definition = ThinkTool.get_definition()
        assert definition["name"] == "think"

    def test_get_definition_description_is_informative(self) -> None:
        """Tests that the tool's description is a non-empty string and contains key phrases."""
        definition = ThinkTool.get_definition()
        description = definition["description"]
        assert isinstance(description, str)
        assert len(description) > 0
        assert "private scratchpad" in description
        assert "user will not see" in description

    def test_get_definition_input_schema_is_correctly_structured(self) -> None:
        """Tests the overall structure of the input_schema."""
        definition = ThinkTool.get_definition()
        schema = definition["input_schema"]
        assert isinstance(schema, dict)
        assert schema.get("type") == "object"
        assert "properties" in schema
        assert "required" in schema

    def test_get_definition_input_schema_properties_are_correct(self) -> None:
        """Tests the 'properties' part of the input_schema."""
        schema = ThinkTool.get_definition()["input_schema"]
        properties = schema.get("properties", {})
        assert isinstance(properties, dict)
        assert list(properties.keys()) == ["thought"]

        thought_property = properties["thought"]
        assert thought_property.get("type") == "string"
        assert isinstance(thought_property.get("description"), str)
        assert len(thought_property.get("description", "")) > 0

    def test_get_definition_input_schema_required_is_correct(self) -> None:
        """Tests the 'required' part of the input_schema."""
        schema = ThinkTool.get_definition()["input_schema"]
        required = schema.get("required", [])
        assert isinstance(required, list)
        assert required == ["thought"]


class TestThinkToolUse:
    """Tests for the ThinkTool.use() method."""

    @pytest.mark.parametrize(
        "thought_input",
        [
            "This is a standard thought.",
            "",  # Empty string
            "a" * 10000,  # Very long string
            "!@#$%^&*()_+-=[]{};':\",./<>?`~",  # Special characters
            "A thought\nwith multiple\nlines.",  # Multi-line string
            "你好世界",  # Unicode characters
        ],
        ids=[
            "standard",
            "empty_string",
            "long_string",
            "special_chars",
            "multi_line",
            "unicode",
        ],
    )
    def test_use_returns_correct_output_for_any_string(self, thought_input: str) -> None:
        """
        Tests that the use() method returns the expected confirmation dict
        regardless of the string input, confirming it's a no-op.
        """
        result = ThinkTool.use(thought=thought_input)
        expected_output = {"output": "OK, I have noted that."}
        assert result == expected_output

    @pytest.mark.parametrize(
        "non_string_input",
        [
            None,
            123,
            123.45,
            True,
            ["a", "b"],
            {"key": "value"},
        ],
        ids=[
            "None",
            "integer",
            "float",
            "boolean",
            "list",
            "dict",
        ],
    )
    def test_use_handles_non_string_input_gracefully(self, non_string_input: Any) -> None:
        """
        Tests that use() is robust and does not raise an error even when
        called with non-string inputs, as it ignores the parameter.
        """
        try:
            result = ThinkTool.use(thought=non_string_input)
            expected_output = {"output": "OK, I have noted that."}
            assert result == expected_output
        except Exception as e:
            pytest.fail(f"ThinkTool.use() raised an unexpected exception for non-string input: {e}")