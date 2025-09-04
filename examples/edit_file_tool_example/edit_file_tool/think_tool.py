# edit_file_tool/think_tool.py

"""Defines the 'think' tool for the Claude model.

This module provides the schema and a no-op implementation for the 'think'
tool. The purpose of this tool is to serve as a private "scratchpad" for the
language model. It allows the model to externalize its reasoning, planning,
and reflection on complex tasks without cluttering the main conversation
history. This reduces token usage and helps the model structure its approach
for more accurate and complex file edits.
"""

from typing import Any, Dict


class ThinkTool:
    """Encapsulates the definition and no-op implementation of the 'think' tool.

    This tool provides a private scratchpad for the Claude model to externalize
    its reasoning process, improving token efficiency and planning for complex
    tasks. The tool's value lies not in its client-side execution, which is a
    no-op, but in providing a structured way for the model to reason that the
    Anthropic backend can process efficiently.
    """

    @staticmethod
    def get_definition() -> Dict[str, Any]:
        """Returns the Anthropic-compatible tool definition for the 'think' tool.

        The schema defines the tool's name, its purpose, and the expected input
        format, which is a single string parameter named 'thought'.

        Returns:
            A dictionary representing the tool's JSON schema.
        """
        return {
            "name": "think",
            "description": (
                "A tool for the model to think step-by-step, plan, and record "
                "notes. This is a private scratchpad. The user will not see "
                "the output of this tool."
            ),
            "input_schema": {
                "type": "object",
                "properties": {
                    "thought": {
                        "type": "string",
                        "description": (
                            "The thought process, reflection, or plan to be "
                            "noted."
                        ),
                    }
                },
                "required": ["thought"],
            },
        }

    @staticmethod
    def use(thought: str) -> Dict[str, str]:
        """Executes the 'think' tool.

        This is a no-op that returns a simple confirmation. The tool's primary
        purpose is to provide a structured way for the model to perform
        cognitive offloading, not to execute any client-side logic.

        Args:
            thought: The string content of the model's thought process. This
                     argument is received but not used.

        Returns:
            A dictionary with an 'output' key confirming the thought was noted.
        """
        # The 'thought' parameter is intentionally ignored. The value is in the
        # model using the tool, not in the client doing anything with the content.
        return {"output": "OK, I have noted that."}



# tests/test_think_tool.py

"""Unit tests for the ThinkTool class in the think_tool module."""

import unittest
from typing import Any, Dict

# Assuming the project structure allows this import path
# If running from the project root, this should work.
# You might need to adjust sys.path for your test runner.
from edit_file_tool.think_tool import ThinkTool


class TestThinkTool(unittest.TestCase):
    """Tests the functionality of the ThinkTool class."""

    def test_get_definition_returns_dict(self) -> None:
        """Tests that get_definition returns a dictionary."""
        definition = ThinkTool.get_definition()
        self.assertIsInstance(definition, dict)

    def test_get_definition_has_correct_top_level_keys(self) -> None:
        """Tests that the tool definition has the required top-level keys."""
        definition = ThinkTool.get_definition()
        self.assertIn("name", definition)
        self.assertIn("description", definition)
        self.assertIn("input_schema", definition)

    def test_get_definition_name_is_correct(self) -> None:
        """Tests that the tool's name is exactly 'think'."""
        definition = ThinkTool.get_definition()
        self.assertEqual(definition["name"], "think")

    def test_get_definition_description_is_informative(self) -> None:
        """Tests that the tool's description is a non-empty string."""
        definition = ThinkTool.get_definition()
        self.assertIsInstance(definition["description"], str)
        self.assertIn("private scratchpad", definition["description"])
        self.assertIn("user will not see", definition["description"])

    def test_get_definition_input_schema_is_correct(self) -> None:
        """Tests the structure and content of the input_schema."""
        definition = ThinkTool.get_definition()
        schema: Dict[str, Any] = definition["input_schema"]

        self.assertEqual(schema["type"], "object")
        self.assertIn("properties", schema)
        self.assertIn("required", schema)

        properties = schema["properties"]
        self.assertIn("thought", properties)
        self.assertEqual(properties["thought"]["type"], "string")
        self.assertIsInstance(properties["thought"]["description"], str)
        self.assertTrue(len(properties["thought"]["description"]) > 0)

        required = schema["required"]
        self.assertEqual(required, ["thought"])

    def test_use_returns_correct_output(self) -> None:
        """Tests that the use() method returns the expected confirmation dict."""
        test_thought = "This is a detailed plan to refactor the codebase."
        result = ThinkTool.use(thought=test_thought)
        expected_output = {"output": "OK, I have noted that."}
        self.assertEqual(result, expected_output)

    def test_use_is_a_no_op_and_handles_any_string(self) -> None:
        """Tests that use() is a no-op and robust to different inputs."""
        try:
            # Test with an empty string
            result_empty = ThinkTool.use(thought="")
            self.assertEqual(result_empty, {"output": "OK, I have noted that."})

            # Test with a very long string
            long_thought = "a" * 10000
            result_long = ThinkTool.use(thought=long_thought)
            self.assertEqual(result_long, {"output": "OK, I have noted that."})

            # Test with special characters
            special_thought = "!@#$%^&*()_+-=[]{};':\",./<>?`~"
            result_special = ThinkTool.use(thought=special_thought)
            self.assertEqual(result_special, {"output": "OK, I have noted that."})
        except Exception as e:
            self.fail(f"ThinkTool.use() raised an unexpected exception: {e}")


if __name__ == "__main__":
    unittest.main()