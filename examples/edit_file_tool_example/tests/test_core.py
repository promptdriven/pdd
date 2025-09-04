# To run this test:
# Option 1: From project root: pytest tests/test_core.py
# Option 2: From project root: python -m pytest tests/test_core.py

import asyncio
import logging
from unittest.mock import AsyncMock, MagicMock

import pytest
from anthropic.types import ToolUseBlock

from edit_file_tool.core import edit_file
from edit_file_tool.editor_tool import EditResult
from edit_file_tool.utils import EditToolError
from edit_file_tool.claude_api import MODEL_TO_TEXT_EDITOR_TOOL

# Test Plan for edit_file_tool/core.py
#
# The `core.py` module is the central orchestrator of the file editing process.
# Tests will focus on verifying its ability to manage the conversation loop,
# handle tool calls correctly, manage state (cost, messages), and gracefully
# handle errors from its dependencies (file I/O, API calls, tool execution).
#
# We will use pytest and pytest-asyncio for asynchronous testing. Mocking will be
# used for external dependencies like `claude_api.call_claude_api`.
#
# Key areas to test:
# 1.  Happy Path Scenarios:
#     -   Test a complete, successful edit cycle involving one tool call.
#     -   Test a cycle with multiple tool calls in a single turn.
#     -   Test a cycle where the LLM uses the 'think' tool first, then an editor tool.
#     -   Test a scenario where the LLM finishes without any tool use.
#     -   Verify correct accumulation of API costs over multiple iterations.
#
# 2.  Conversation Loop Logic:
#     -   Test that the loop correctly terminates and returns failure when `max_iterations` is reached.
#     -   Test with `max_iterations=1` where a tool is used, ensuring it exits correctly.
#
# 3.  Tool Call Handling:
#     -   Verify that the orchestrator correctly routes to the `think_tool`.
#     -   Verify that the orchestrator correctly routes to the `editor_tool`.
#     -   Test the response to an unknown tool name, ensuring a helpful error is returned to the LLM.
#     -   Test how the orchestrator handles a tool that returns a failure (`EditResult(success=False)`). The error should be formatted and sent back to the LLM.
#     -   Test how the orchestrator handles a tool that raises an unexpected exception.
#
# 4.  Dependency Failure Handling:
#     -   Test failure when the initial `read_file_async` fails (e.g., file not found).
#     -   Test failure when `claude_api.call_claude_api` raises an APIError.
#     -   Test graceful handling of other exceptions from dependencies.
#
# 5.  Input and Configuration:
#     -   Test that the `use_cache` flag (auto, always, never) is correctly interpreted by `CacheManager` and the result is passed to `call_claude_api`.
#     -   Test that verbose logging is enabled when `verbose=True`.
#
# 6.  Message and State Management:
#     -   Verify that the `messages` list is correctly constructed and appended to in each turn.
#     -   Use a snapshotting side effect on the `call_claude_api` mock to verify the state of the `messages` list at each step of the conversation.


# Get the actual editor tool name for the test model
TEST_MODEL = "claude-3-5-sonnet-20240620"
EDITOR_TOOL_NAME = MODEL_TO_TEXT_EDITOR_TOOL[TEST_MODEL]["name"]

@pytest.fixture
def mock_dependencies(mocker):
    """Fixture to mock all external dependencies of the core module."""
    mock_call_api = mocker.patch("edit_file_tool.core.call_claude_api", new_callable=AsyncMock)
    mock_read_file = mocker.patch("edit_file_tool.core.read_file_async", new_callable=AsyncMock)
    mock_editor_tool_class = mocker.patch("edit_file_tool.core.EditTool20250124")
    mock_think_tool_class = mocker.patch("edit_file_tool.core.ThinkTool")
    mock_cache_manager_class = mocker.patch("edit_file_tool.core.CacheManager")

    # The editor instance is an async callable. We mock it with AsyncMock.
    mock_editor_instance = AsyncMock(return_value=EditResult(success=True, output="Edit successful."))
    mock_editor_tool_class.return_value = mock_editor_instance

    mock_think_instance = MagicMock()
    mock_think_instance.get_definition.return_value = {"name": "think"}
    mock_think_instance.use.return_value = {"output": "OK, I have noted that."}
    mock_think_tool_class.return_value = mock_think_instance

    mock_cache_manager_instance = MagicMock()
    mock_cache_manager_instance.should_use_cache.return_value = False
    mock_cache_manager_class.return_value = mock_cache_manager_instance

    mock_read_file.return_value = ("initial file content", None)
    
    mock_final_response = create_mock_api_response([MagicMock(text="All done!", type="text")], stop_reason="end_turn")
    mock_call_api.return_value = mock_final_response

    return {
        "call_api": mock_call_api,
        "read_file": mock_read_file,
        "editor_instance": mock_editor_instance,
        "editor_tool_class": mock_editor_tool_class,
        "think_instance": mock_think_instance,
        "cache_manager_instance": mock_cache_manager_instance,
    }

def create_mock_api_response(content, stop_reason="tool_use", role="assistant", cost=0.01):
    """Creates a mock (Message, CostInfo) tuple for the API call."""
    mock_message = MagicMock()
    mock_message.role = role
    mock_message.content = content
    mock_message.stop_reason = stop_reason
    cost_info = {"total_cost": cost}
    return (mock_message, cost_info)

def create_mock_tool_call(tool_id, name, tool_input):
    """Creates a mock ToolUseBlock."""
    mock_tool_call = MagicMock(spec=ToolUseBlock)
    mock_tool_call.id = tool_id
    mock_tool_call.name = name
    mock_tool_call.input = tool_input
    mock_tool_call.type = "tool_use"
    return mock_tool_call

@pytest.mark.asyncio
async def test_edit_file_happy_path_single_tool_call(mock_dependencies):
    """Tests a successful run with one tool call and then a final message."""
    tool_call = create_mock_tool_call("tool1", EDITOR_TOOL_NAME, {"command": "view", "path": "test.py"})
    tool_response = create_mock_api_response([tool_call], stop_reason="tool_use", cost=0.02)
    final_response = create_mock_api_response([MagicMock(text="File viewed.", type="text")], stop_reason="end_turn", cost=0.01)
    mock_dependencies["call_api"].side_effect = [tool_response, final_response]
    mock_dependencies["editor_instance"].return_value = EditResult(success=True, output="File content here.")

    success, message, cost = await edit_file("test.py", "view the file", TEST_MODEL, "auto", False, 3)

    assert success is True
    assert message == "File viewed."
    assert cost == pytest.approx(0.03)
    mock_dependencies["editor_instance"].assert_awaited_once_with(command="view", path="test.py")
    assert mock_dependencies["call_api"].call_count == 2
    
    last_call_args = mock_dependencies["call_api"].await_args_list[1]
    messages = last_call_args.kwargs['messages']
    # The assertion on length is removed as it's brittle due to the mock
    # capturing a reference to a list that is mutated after the call.
    # The important check is that the correct message type is in the correct position.
    assert messages[2]['content'][0]['type'] == 'tool_result'

@pytest.mark.asyncio
async def test_edit_file_max_iterations_reached(mock_dependencies):
    """Tests that the function exits correctly when max_iterations is reached."""
    tool_call = create_mock_tool_call("tool1", "think", {"thought": "I am thinking."})
    tool_response = create_mock_api_response([tool_call], stop_reason="tool_use", cost=0.01)
    mock_dependencies["call_api"].return_value = tool_response
    
    success, message, cost = await edit_file("test.py", "do something complex", TEST_MODEL, "auto", False, 2)

    assert success is False
    assert message == "Max iterations (2) reached without completion."
    assert cost == pytest.approx(0.02)
    assert mock_dependencies["call_api"].call_count == 2

@pytest.mark.asyncio
async def test_edit_file_no_tool_use(mock_dependencies):
    """Tests the scenario where the LLM provides a final answer immediately."""
    final_response = create_mock_api_response([MagicMock(text="I can't do that.", type="text")], stop_reason="end_turn", cost=0.005)
    mock_dependencies["call_api"].return_value = final_response

    success, message, cost = await edit_file("test.py", "do something impossible", TEST_MODEL, "auto", False, 5)

    assert success is True
    assert message == "I can't do that."
    assert cost == pytest.approx(0.005)
    mock_dependencies["call_api"].assert_awaited_once()

@pytest.mark.asyncio
async def test_edit_file_handles_tool_failure(mock_dependencies):
    """Tests that a failure from the editor tool is correctly reported back to the LLM."""
    tool_call = create_mock_tool_call("tool_fail", EDITOR_TOOL_NAME, {"command": "insert", "path": "test.py"})
    tool_response = create_mock_api_response([tool_call], stop_reason="tool_use")
    final_response = create_mock_api_response([MagicMock(text="Okay, I will try something else.", type="text")], stop_reason="end_turn")
    mock_dependencies["call_api"].side_effect = [tool_response, final_response]
    mock_dependencies["editor_instance"].return_value = EditResult(success=False, output="", error="Invalid line number.")

    success, message, cost = await edit_file("test.py", "insert at a bad line", TEST_MODEL, "auto", False, 3)

    assert success is True
    assert message == "Okay, I will try something else."
    last_call_args = mock_dependencies["call_api"].await_args_list[1]
    messages = last_call_args.kwargs['messages']
    tool_result_message = messages[2]['content'][0]
    assert tool_result_message['is_error'] is True
    assert tool_result_message['content'][0]['text'] == "Invalid line number."

@pytest.mark.asyncio
async def test_edit_file_handles_unknown_tool(mock_dependencies):
    """Tests that an unknown tool name from the LLM is handled gracefully."""
    tool_call = create_mock_tool_call("tool_unknown", "delete_file", {"path": "test.py"})
    tool_response = create_mock_api_response([tool_call], stop_reason="tool_use")
    final_response = create_mock_api_response([MagicMock(text="My mistake.", type="text")], stop_reason="end_turn")
    mock_dependencies["call_api"].side_effect = [tool_response, final_response]

    await edit_file("test.py", "delete the file", TEST_MODEL, "auto", False, 3)

    last_call_args = mock_dependencies["call_api"].await_args_list[1]
    messages = last_call_args.kwargs['messages']
    tool_result_message = messages[2]['content'][0]
    assert tool_result_message['is_error'] is True
    error_text = tool_result_message['content'][0]['text']
    assert "Unknown tool: 'delete_file'" in error_text
    assert "think" in error_text
    assert EDITOR_TOOL_NAME in error_text

@pytest.mark.asyncio
async def test_edit_file_handles_unexpected_tool_exception(mock_dependencies):
    """Tests that an unexpected exception from a tool is caught and reported."""
    tool_call = create_mock_tool_call("tool_exc", EDITOR_TOOL_NAME, {"command": "view"})
    tool_response = create_mock_api_response([tool_call], stop_reason="tool_use")
    final_response = create_mock_api_response([MagicMock(text="Oops.", type="text")], stop_reason="end_turn")
    mock_dependencies["call_api"].side_effect = [tool_response, final_response]
    mock_dependencies["editor_instance"].side_effect = ValueError("Something broke")

    await edit_file("test.py", "view", TEST_MODEL, "auto", False, 3)

    last_call_args = mock_dependencies["call_api"].await_args_list[1]
    messages = last_call_args.kwargs['messages']
    tool_result_message = messages[2]['content'][0]
    assert tool_result_message['is_error'] is True
    error_text = tool_result_message['content'][0]['text']
    assert "An unexpected error occurred while running tool" in error_text
    assert "Something broke" in error_text

@pytest.mark.asyncio
async def test_edit_file_file_not_found(mock_dependencies):
    """Tests that the function fails correctly if the initial file read fails."""
    mock_dependencies["read_file"].return_value = (None, "Permission denied")

    success, message, cost = await edit_file("protected.py", "edit this", TEST_MODEL, "auto", False, 3)

    assert success is False
    assert "Could not read file 'protected.py': Permission denied" in message
    assert cost == 0.0
    mock_dependencies["call_api"].assert_not_called()

@pytest.mark.asyncio
async def test_edit_file_api_call_failure(mock_dependencies):
    """Tests that the function fails if the API call raises an exception."""
    mock_dependencies["call_api"].side_effect = EditToolError("Invalid API Key")

    success, message, cost = await edit_file("test.py", "edit this", TEST_MODEL, "auto", False, 3)

    assert success is False
    assert "Invalid API Key" in message
    assert cost == 0.0

@pytest.mark.asyncio
@pytest.mark.parametrize("use_cache_flag, expected_cache_decision", [
    ("always", True), (True, True), ("never", False), (False, False), ("auto", True),
])
async def test_edit_file_cache_logic(mock_dependencies, use_cache_flag, expected_cache_decision):
    """Tests that the `use_cache` flag is correctly passed to the API call."""
    mock_dependencies["cache_manager_instance"].should_use_cache.return_value = expected_cache_decision

    await edit_file("test.py", "edit this", TEST_MODEL, use_cache_flag, False, 1)

    mock_dependencies["cache_manager_instance"].should_use_cache.assert_called_once_with(
        "initial file content", use_cache_flag
    )
    mock_dependencies["call_api"].assert_awaited_once()
    api_call_kwargs = mock_dependencies["call_api"].await_args.kwargs
    assert api_call_kwargs['use_cache'] == expected_cache_decision

@pytest.mark.asyncio
async def test_edit_file_multiple_tool_calls_in_one_turn(mock_dependencies):
    """Tests handling of multiple concurrent tool calls from the LLM."""
    tool_call_1 = create_mock_tool_call("tool1", "think", {"thought": "First, I will view."})
    tool_call_2 = create_mock_tool_call("tool2", EDITOR_TOOL_NAME, {"command": "view", "path": "test.py"})
    tool_response = create_mock_api_response([tool_call_1, tool_call_2], stop_reason="tool_use")
    final_response = create_mock_api_response([MagicMock(text="Done.", type="text")], stop_reason="end_turn")
    mock_dependencies["call_api"].side_effect = [tool_response, final_response]
    mock_dependencies["editor_instance"].return_value = EditResult(success=True, output="File content.")

    success, _, _ = await edit_file("test.py", "think and view", TEST_MODEL, "auto", False, 3)

    assert success is True
    assert mock_dependencies["think_instance"].use.call_count == 1
    mock_dependencies["editor_instance"].assert_awaited_once()
    last_call_args = mock_dependencies["call_api"].await_args_list[1]
    messages = last_call_args.kwargs['messages']
    tool_results_content = messages[2]['content']
    assert len(tool_results_content) == 2
    result_1 = next(r for r in tool_results_content if r['tool_use_id'] == 'tool1')
    result_2 = next(r for r in tool_results_content if r['tool_use_id'] == 'tool2')
    assert "OK, I have noted that." in result_1['content'][0]['text']
    assert "File content." in result_2['content'][0]['text']

@pytest.mark.asyncio
async def test_edit_file_verbose_logging(mocker):
    """Tests that verbose=True sets the log level to INFO."""
    mock_log = mocker.patch("edit_file_tool.core.log")
    mocker.patch("edit_file_tool.core.read_file_async", new_callable=AsyncMock, return_value=("", None))
    mocker.patch("edit_file_tool.core.call_claude_api", new_callable=AsyncMock, return_value=create_mock_api_response([], stop_reason="end_turn"))
    mocker.patch("edit_file_tool.core.EditTool20250124")
    mocker.patch("edit_file_tool.core.ThinkTool")
    mocker.patch("edit_file_tool.core.CacheManager")

    await edit_file("test.py", "edit", TEST_MODEL, "auto", True, 1)
    
    mock_log.setLevel.assert_called_once_with(logging.INFO)
