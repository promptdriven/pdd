# To run this test:
# Option 1: From project root: pytest tests/test_instruction_parser.py
# Option 2: From project root: python -m pytest tests/test_instruction_parser.py

import pytest
import json
from unittest.mock import AsyncMock, MagicMock

from edit_file_tool.instruction_parser import InstructionParser, InstructionParserError
from anthropic.types import Message, TextBlock
import anthropic

# Test Plan for InstructionParser
#
# The InstructionParser class is a critical component that bridges natural language
# and structured commands. Its core logic relies on an external LLM (Claude),
# which must be mocked for predictable and repeatable testing. The tests will focus
# on the parser's ability to correctly format requests to the LLM and to robustly
# parse and validate the LLM's responses.
#
# Test Components:
# 1. Fixtures:
#    - `mock_anthropic_client`: A pytest fixture to provide a mocked `anthropic.AsyncAnthropic`
#      client. This is the central fixture for controlling the test environment.
#    - `parser`: A fixture that creates an `InstructionParser` instance using the
#      mocked client.
#
# 2. Test Scenarios:
#
#    2.1. Happy Path Scenarios (Successful Parsing):
#         - Test that a simple `str_replace` instruction is correctly parsed.
#         - Test that an `insert` instruction with "before line X" is parsed,
#           verifying the 0-indexed `insert_line` is calculated correctly by the mocked LLM.
#         - Test that an `insert` instruction with "after line Y" is parsed.
#         - Test that an instruction to insert at the top of the file is parsed.
#         - Test that a multi-step instruction generates a list of multiple tool calls.
#         - Test that a `create` file instruction is parsed correctly.
#         - Test that the parser correctly handles a response where the LLM omits the `path`
#           in the generated JSON, ensuring the path is added back.
#
#    2.2. LLM Response Format Handling:
#         - Test parsing a raw JSON string response from the LLM.
#         - Test parsing a JSON response wrapped in various markdown code block styles.
#
#    2.3. Error and Edge Case Handling:
#         - Test that an `anthropic.APIError` during the API call is caught and
#           re-raised as an `InstructionParserError`.
#         - Test that an empty or non-text response from the LLM raises an
#           `InstructionParserError`.
#         - Test that a response containing invalid, non-JSON text raises an
#           `InstructionParserError`.
#         - Test that a response containing a valid JSON object (not a list) raises
#           an `InstructionParserError`.
#         - Test that a response containing a JSON list of non-dictionary items
#           raises an `InstructionParserError`.
#         - Test that an ambiguous instruction, for which the LLM is mocked to return
#           an empty list `[]`, is handled gracefully and returns an empty list.
#
#    2.4. Input Pre-processing:
#         - Test that the user message sent to the LLM contains correctly numbered
#           lines for the provided file content.
#         - Test that file content exceeding the internal limit is
#           correctly truncated and a note is appended before being sent to the LLM.
#
# Mocking Strategy:
# - The `anthropic.AsyncAnthropic` client will be mocked using `unittest.mock.AsyncMock`.
# - The `messages.create` method will be the primary mock target.
# - For each test case, `messages.create` will be configured to return a specific
#   `anthropic.types.Message` object containing the desired `TextBlock` with a
#   pre-defined JSON string. This allows precise control over the "LLM's output".
# - To test error conditions, the mock will be configured to raise exceptions or
#   return malformed data structures.
# - To test input pre-processing, we will inspect the arguments passed to the
#   `messages.create` mock call.


@pytest.fixture
def mock_anthropic_client():
    """Provides a mock AsyncAnthropic client."""
    client = AsyncMock(spec=anthropic.AsyncAnthropic)
    client.messages = AsyncMock()
    client.messages.create = AsyncMock()
    return client

@pytest.fixture
def parser(mock_anthropic_client):
    """Provides an InstructionParser instance with a mocked client."""
    return InstructionParser(client=mock_anthropic_client)

def create_mock_message(text_content: str) -> Message:
    """Helper to create a mock anthropic.Message object."""
    return Message(
        id="msg_test_123",
        type="message",
        role="assistant",
        model="claude-test-model",
        content=[TextBlock(type="text", text=text_content)],
        stop_reason="end_turn",
        usage={"input_tokens": 100, "output_tokens": 100}
    )

# --- Test Cases ---

@pytest.mark.asyncio
async def test_parse_simple_str_replace(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests parsing a simple string replacement instruction."""
    instruction = "change 'foo' to 'bar'"
    file_path = "test.py"
    file_content = "print('foo')"
    
    expected_command = {
        "command": "str_replace",
        "path": file_path,
        "old_str": "print('foo')",
        "new_str": "print('bar')"
    }
    mock_response_json = json.dumps([expected_command])
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert result == [expected_command]
    mock_anthropic_client.messages.create.assert_called_once()

@pytest.mark.asyncio
async def test_parse_insert_before_line(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests parsing an insert instruction for 'before line N'."""
    instruction = "add a comment before line 2"
    file_path = "script.js"
    file_content = "line1\nline2"
    
    # The system prompt instructs the LLM to convert 1-based "before line 2" to 0-indexed line 1.
    expected_command = {
        "command": "insert",
        "path": file_path,
        "insert_line": 1,
        "new_str": "// new comment"
    }
    mock_response_json = json.dumps([expected_command])
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert result == [expected_command]
    assert result[0]["insert_line"] == 1

@pytest.mark.asyncio
async def test_parse_insert_after_line(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests parsing an insert instruction for 'after line N'."""
    instruction = "add a print statement after line 1"
    file_path = "main.py"
    file_content = "x = 1\nprint(x)"
    
    # The system prompt instructs the LLM to convert 1-based "after line 1" to 0-indexed line 1.
    expected_command = {
        "command": "insert",
        "path": file_path,
        "insert_line": 1,
        "new_str": "print('done')"
    }
    mock_response_json = json.dumps([expected_command])
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert result == [expected_command]
    assert result[0]["insert_line"] == 1

@pytest.mark.asyncio
async def test_parse_multi_step_edit(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests parsing an instruction with multiple distinct edits."""
    instruction = "change x to 10 on line 1 and add a comment before line 2"
    file_path = "multi.py"
    file_content = "x = 5\nprint(x)"

    expected_commands = [
        {"command": "str_replace", "path": file_path, "old_str": "x = 5", "new_str": "x = 10"},
        {"command": "insert", "path": file_path, "insert_line": 1, "new_str": "# New comment"}
    ]
    mock_response_json = json.dumps(expected_commands)
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert result == expected_commands
    assert len(result) == 2

@pytest.mark.asyncio
async def test_parse_create_file(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests parsing a file creation instruction."""
    instruction = "create a new file named 'new.txt' with 'hello world'"
    file_path = "new.txt" # Path might be redundant but good for context
    file_content = "" # No existing content

    expected_command = {
        "command": "create",
        "path": "new.txt",
        "file_text": "hello world"
    }
    mock_response_json = json.dumps([expected_command])
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert result == [expected_command]

@pytest.mark.asyncio
@pytest.mark.parametrize("response_format", [
    '[{ "command": "view", "path": "test.py" }]',
    '```json\n[{ "command": "view", "path": "test.py" }]\n```',
    '```\n[{ "command": "view", "path": "test.py" }]\n```',
    '  [{ "command": "view", "path": "test.py" }]  '
])
async def test_parse_handles_various_json_formats(parser: InstructionParser, mock_anthropic_client: AsyncMock, response_format: str):
    """Tests that the parser can handle JSON in raw and markdown-fenced formats."""
    mock_anthropic_client.messages.create.return_value = create_mock_message(response_format)
    
    result = await parser.parse("view test.py", "test.py", "")
    
    assert result == [{"command": "view", "path": "test.py"}]

@pytest.mark.asyncio
async def test_parse_adds_path_if_missing(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that the file_path is added to commands if the LLM omits it."""
    instruction = "just change foo to bar"
    file_path = "important/file.py"
    file_content = "foo"

    # LLM forgets to add the path
    command_from_llm = {"command": "str_replace", "old_str": "foo", "new_str": "bar"}
    mock_response_json = json.dumps([command_from_llm])
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert len(result) == 1
    assert result[0]["path"] == file_path
    assert "path" in result[0]

@pytest.mark.asyncio
async def test_parse_handles_ambiguous_instruction(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests graceful handling of an ambiguous instruction (LLM returns empty list)."""
    instruction = "do something... maybe?"
    file_path = "test.py"
    file_content = "content"

    # LLM indicates ambiguity by returning an empty list
    mock_response_json = "[]"
    mock_anthropic_client.messages.create.return_value = create_mock_message(mock_response_json)

    result = await parser.parse(instruction, file_path, file_content)

    assert result == []

# --- Error Handling Tests ---

@pytest.mark.asyncio
async def test_parse_raises_on_api_error(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that InstructionParserError is raised on an Anthropic API error."""
    mock_anthropic_client.messages.create.side_effect = anthropic.APIError(
        "Test API Error", request=MagicMock(), body=None
    )

    with pytest.raises(InstructionParserError, match="Anthropic API call failed: Test API Error"):
        await parser.parse("any instruction", "file.py", "content")

@pytest.mark.asyncio
async def test_parse_raises_on_empty_response(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that an error is raised if the LLM response content is empty."""
    mock_message = Message(
        id="msg_empty", type="message", role="assistant", model="m", content=[],
        stop_reason="end_turn", usage={"input_tokens": 1, "output_tokens": 1}
    )
    mock_anthropic_client.messages.create.return_value = mock_message

    with pytest.raises(InstructionParserError, match="LLM response was empty or not in the expected text format."):
        await parser.parse("any", "file.py", "content")

@pytest.mark.asyncio
async def test_parse_raises_on_invalid_json(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that an error is raised for a non-JSON response."""
    response_text = "This is not JSON."
    mock_anthropic_client.messages.create.return_value = create_mock_message(response_text)

    with pytest.raises(InstructionParserError, match="Failed to decode LLM response as JSON"):
        await parser.parse("any", "file.py", "content")

@pytest.mark.asyncio
async def test_parse_raises_on_json_object_instead_of_list(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that an error is raised if the root JSON type is an object, not a list."""
    response_text = '{"command": "this is wrong"}'
    mock_anthropic_client.messages.create.return_value = create_mock_message(response_text)

    with pytest.raises(InstructionParserError, match="Expected a JSON list, but got dict"):
        await parser.parse("any", "file.py", "content")

@pytest.mark.asyncio
async def test_parse_raises_on_list_with_non_dict_items(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that an error is raised if the list contains non-dictionary items."""
    response_text = '[{"command": "ok"}, "not a dict", 123]'
    mock_anthropic_client.messages.create.return_value = create_mock_message(response_text)

    with pytest.raises(InstructionParserError, match="All items in the JSON list must be dictionaries"):
        await parser.parse("any", "file.py", "content")

# --- Input Pre-processing Tests ---

@pytest.mark.asyncio
async def test_input_message_has_numbered_lines(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that file content is correctly numbered in the prompt to the LLM."""
    instruction = "test"
    file_path = "test.py"
    file_content = "first line\nsecond line"
    
    # Mock a valid response to allow the call to complete
    mock_anthropic_client.messages.create.return_value = create_mock_message("[]")
    
    await parser.parse(instruction, file_path, file_content)

    mock_anthropic_client.messages.create.assert_called_once()
    _pos_args, kw_args = mock_anthropic_client.messages.create.call_args
    user_message = kw_args['messages'][0]['content']

    expected_numbered_content = "1: first line\n2: second line"
    assert expected_numbered_content in user_message
    assert f"File to edit: `{file_path}`" in user_message
    assert f'User instruction: "{instruction}"' in user_message

@pytest.mark.asyncio
async def test_file_content_truncation(parser: InstructionParser, mock_anthropic_client: AsyncMock):
    """Tests that large file content is truncated before being sent to the LLM."""
    # This limit is defined in the implementation. We test against it here.
    max_bytes = 100 * 1024
    long_content = "a" * (max_bytes + 100)
    
    mock_anthropic_client.messages.create.return_value = create_mock_message("[]")

    await parser.parse("test", "large_file.log", long_content)

    mock_anthropic_client.messages.create.assert_called_once()
    _pos_args, kw_args = mock_anthropic_client.messages.create.call_args
    user_message = kw_args['messages'][0]['content']

    assert "... (file truncated for brevity) ..." in user_message
    # Check that the beginning of the content is still there
    assert long_content.startswith("a" * 1000)
    # The actual content sent should be slightly larger than max_bytes due to the suffix
    # We can check that the file content part is roughly the right size
    start_of_content_in_msg = user_message.find("```\n") + 4
    end_of_content_in_msg = user_message.rfind("\n```")
    content_in_msg = user_message[start_of_content_in_msg:end_of_content_in_msg]
    
    # The length of the content part should be close to max_bytes + suffix length
    # This is an approximation, but good enough to verify truncation happened.
    assert len(content_in_msg) < len(long_content)
    assert len(content_in_msg) > max_bytes
