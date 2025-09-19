# edit_file_tool/instruction_parser.py

import asyncio
import json
from typing import Any, Dict, List, Optional

import anthropic
from anthropic.types import Message, TextBlock

class InstructionParserError(Exception):
    """Custom exception for errors during instruction parsing."""
    pass

class InstructionParser:
    """
    Parses natural language instructions into structured tool calls for file editing.

    This class uses a Claude LLM to translate a user's free-form text instruction
    into a machine-readable list of commands for the `text_editor_20250124` tool.
    It is designed to handle single or multiple edit requests within a single
    instruction and to correctly interpret positional language for insertions.

    Attributes:
        _client (anthropic.AsyncAnthropic): The asynchronous Anthropic API client.
        _model (str): The name of the Claude model to use for parsing.
        _system_prompt (str): A pre-generated system prompt to guide the LLM.
    """

    _MAX_CONTENT_BYTES = 100 * 1024  # 100KB limit for file content context

    def __init__(self, client: anthropic.AsyncAnthropic, model: str = "claude-3-7-sonnet-20250219"):
        """
        Initializes the parser with an Anthropic client and model name.

        Args:
            client: An initialized asynchronous Anthropic client.
            model: The model identifier string for the Claude API.
        """
        self._client: anthropic.AsyncAnthropic = client
        self._model: str = model
        self._system_prompt: str = self._create_system_prompt()

    async def parse(self, instruction: str, file_path: str, file_content: str) -> List[Dict[str, Any]]:
        """
        Parses a natural language instruction into a list of structured tool calls.

        This method constructs a detailed prompt including the user's instruction
        and the relevant file content, then calls the Claude API to generate the
        corresponding tool call JSON. It handles response validation and error cases.

        Args:
            instruction: The natural language instruction from the user.
            file_path: The path to the file to be edited.
            file_content: The content of the file for context.

        Returns:
            A list of dictionaries, where each dictionary represents a tool call
            conforming to the `text_editor_20250124` format.

        Raises:
            InstructionParserError: If the instruction cannot be parsed, the LLM
                                    returns a malformed response, or an API error
                                    occurs.
        """
        # Truncate content if it's too large to manage token count
        if len(file_content.encode('utf-8')) > self._MAX_CONTENT_BYTES:
            file_content = file_content[:self._MAX_CONTENT_BYTES] + "\n... (file truncated for brevity) ..."

        # Add 1-based line numbers to content for easier LLM reasoning
        lines = file_content.splitlines()
        numbered_content = "\n".join(f"{i+1}: {line}" for i, line in enumerate(lines))

        user_message = f"""
User instruction: "{instruction}"

File to edit: `{file_path}`

File content with 1-based line numbers for context:
```
{numbered_content}
```

Based on the user instruction and the file content, generate the corresponding JSON array of tool calls.
"""
        try:
            response: Message = await self._client.messages.create(
                model=self._model,
                max_tokens=4096,
                temperature=0.0,  # Use low temperature for predictable, structured output
                system=self._system_prompt,
                messages=[
                    {"role": "user", "content": user_message}
                ]
            )
        except anthropic.APIError as e:
            raise InstructionParserError(f"Anthropic API call failed: {e}")

        if not response.content or not isinstance(response.content[0], TextBlock):
            raise InstructionParserError("LLM response was empty or not in the expected text format.")

        response_text = response.content[0].text.strip()

        # The model might wrap the JSON in a markdown code block, so we extract it.
        if response_text.startswith("```json"):
            response_text = response_text[7:].strip()
        elif response_text.startswith("```"):
            response_text = response_text[3:].strip()
        
        if response_text.endswith("```"):
            response_text = response_text[:-3].strip()

        try:
            parsed_json = json.loads(response_text)
        except json.JSONDecodeError:
            raise InstructionParserError(
                f"Failed to decode LLM response as JSON. Raw response:\n---\n{response_text}\n---"
            )

        # Validate the structure of the parsed JSON
        if not isinstance(parsed_json, list):
            raise InstructionParserError(
                f"Expected a JSON list, but got {type(parsed_json).__name__}. "
                f"Content: {parsed_json}"
            )

        if not all(isinstance(item, dict) for item in parsed_json):
            raise InstructionParserError(
                "All items in the JSON list must be dictionaries (tool calls)."
            )
        
        # As a robustness measure, ensure the path is present in all generated commands.
        for command in parsed_json:
            if 'path' not in command:
                command['path'] = file_path

        return parsed_json

    def _create_system_prompt(self) -> str:
        """
        Creates the system prompt to guide the LLM in parsing instructions.

        This prompt defines the LLM's role, the required output format (a JSON array),
        and the precise schema for each supported tool command. It places special
        emphasis on the correct calculation for the 0-indexed `insert_line` parameter.

        Returns:
            A string containing the system prompt.
        """
        return """
You are an expert system that translates natural language instructions for file editing into a structured JSON array of tool calls. Your sole purpose is to generate this JSON output based on the user's request and the provided file context.

Your response MUST be a valid JSON array `[...]` containing one or more tool call objects. Do NOT add any explanatory text, comments, or markdown formatting before or after the JSON array.

The user will provide an instruction, a file path, and the content of that file (with 1-based line numbers for context). You must use this information to construct the correct tool calls.

Here are the available tool commands and their parameters:

1.  **`str_replace`**: Replaces a specific, unique string in the file.
    -   `command` (string): "str_replace"
    -   `path` (string): The path to the file (e.g., "my_project/main.py").
    -   `old_str` (string): The exact string to be replaced, including all whitespace and indentation. It must be unique in the file.
    -   `new_str` (string): The new string to insert.

2.  **`insert`**: Inserts a new string at a specific line.
    -   `command` (string): "insert"
    -   `path` (string): The path to the file.
    -   `insert_line` (integer): A 0-indexed integer specifying the line number for the insertion.
    -   `new_str` (string): The new string to insert.

3.  **`create`**: Creates a new file with specified content.
    -   `command` (string): "create"
    -   `path` (string): The path of the new file to create.
    -   `file_text` (string): The initial content for the new file.

4.  **`view`**: Views the content of a file or directory. (Less common for edit instructions, but available).
    -   `command` (string): "view"
    -   `path` (string): The path to the file or directory to view.

**CRITICAL RULES FOR `insert_line`:**
-   The `insert_line` parameter is **0-indexed**. The file content provided to you has 1-based line numbers for your convenience. You MUST convert correctly.
-   To insert **BEFORE** 1-based line `N`, use `insert_line: N-1`.
-   To insert **AFTER** 1-based line `N`, use `insert_line: N`.
-   To insert at the very beginning of the file, use `insert_line: 0`.

**MULTI-STEP EDITS:**
If the user's instruction contains multiple distinct edits (e.g., "change variable X and add a comment Y"), you must generate a JSON array with multiple tool call objects, one for each action, in the order they should be performed.

**EXAMPLE:**
User Instruction: "In `main.py`, change the variable `max_retries` to 5 on line 23 and add a comment '# Entry point' before the main function on line 50."
File Content Snippet:
...
23: max_retries = 10
...
49:
50: def main():
...

Your Output:
[
  {
    "command": "str_replace",
    "path": "main.py",
    "old_str": "max_retries = 10",
    "new_str": "max_retries = 5"
  },
  {
    "command": "insert",
    "path": "main.py",
    "insert_line": 49,
    "new_str": "# Entry point"
  }
]

If an instruction is too ambiguous to create a confident tool call, return an empty JSON array `[]`.
"""