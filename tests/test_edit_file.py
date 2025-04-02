import asyncio
import pytest
import os
import json
import hashlib
from unittest.mock import AsyncMock, MagicMock, patch, mock_open, ANY
from langchain_core.messages import AIMessage, ToolMessage
import tempfile
import inspect
import warnings

# Assume the code under test is in pdd/edit_file.py
from pdd.edit_file import edit_file, calculate_hash, EditFileState

# --- Helper functions ---

async def noop_coroutine():
    """A do-nothing coroutine that can be awaited safely"""
    return None

# Fixture to capture all coroutines that might need to be awaited
@pytest.fixture
def cleanup_coroutines():
    coroutines = []
    
    def add_coroutine(coro):
        if is_coroutine(coro):
            coroutines.append(coro)
            
    yield add_coroutine
    
    # Cleanup: ensure all captured coroutines are awaited
    async def cleanup():
        for coro in coroutines:
            try:
                await coro
            except Exception:
                pass  # Ignore errors during cleanup
                
    asyncio.run(cleanup())

# --- Fixtures ---

# Use pytest's built-in tmp_path fixture for temporary directories
@pytest.fixture
def temp_dir(tmp_path):
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    return output_dir

@pytest.fixture
def mcp_config_path(tmp_path):
    return tmp_path / "mcp_config.json"

@pytest.fixture
def valid_mcp_config_content():
    return {
        "my_editor_server": {
            "command": "echo",
            "args": ["mcp-tool-output"],
            "transport": "stdio"
        }
    }

@pytest.fixture
def create_valid_mcp_config(mcp_config_path, valid_mcp_config_content):
    with open(mcp_config_path, 'w') as f:
        json.dump(valid_mcp_config_content, f)
    return mcp_config_path

@pytest.fixture
def test_file_path(temp_dir):
    return temp_dir / "test_file.txt"

@pytest.fixture
def initial_content():
    return "Initial content line 1.\nInitial content line 2."

@pytest.fixture
def create_test_file(test_file_path, initial_content):
    # Make sure the directory exists
    test_file_path.parent.mkdir(parents=True, exist_ok=True)
    
    # Create the actual file
    with open(test_file_path, 'w', encoding='utf-8') as f:
        f.write(initial_content)
    
    return test_file_path

# --- Mocks ---

@pytest.fixture
def mock_mcp_client(mocker):
    from langchain_core.messages import ToolMessage
    
    # Create a mock client that works with the async context manager protocol
    mock_client_instance = AsyncMock()
    
    # Setup mock tool
    mock_tool = MagicMock()
    mock_tool.name = "replace_text"
    mock_tool.description = "Replaces text"
    mock_tool.args_schema = MagicMock()
    mock_tool.args_schema.schema.return_value = {"properties": {"old": {"type": "string"}, "new": {"type": "string"}}}
    
    # Make get_tools return a list
    mock_client_instance.get_tools = AsyncMock(return_value=[mock_tool])

    # Create a mock tool node
    mock_tool_node_instance = AsyncMock()
    
    # Set up a proper return value for tool_node.ainvoke
    # This creates a message indicating success
    async def tool_invoke_mock(state):
        return {
            "messages": [ToolMessage(
                content="Success", 
                tool_call_id=state['messages'][-1].tool_calls[0]['id'],
                name=state['messages'][-1].tool_calls[0]['name']
            )]
        }
    mock_tool_node_instance.ainvoke.side_effect = tool_invoke_mock
    
    # Apply mocks
    mocker.patch('pdd.edit_file.ToolNode', return_value=mock_tool_node_instance)
    mocker.patch('pdd.edit_file.MultiServerMCPClient', return_value=mock_client_instance)
    
    return mock_client_instance, mock_tool_node_instance

@pytest.fixture
def mock_llm(mocker):
    mock_llm_instance = AsyncMock()

    # Create a proper AIMessage with tool_calls
    tool_call = {
        "name": "replace_text",
        "args": {"old": "Initial", "new": "Edited"},
        "id": "tool_call_123"
    }
    
    plan_response = AIMessage(content="", tool_calls=[tool_call])
    
    # Don't patch AIMessage creation, use the actual class
    mocker.patch('pdd.edit_file.AIMessage', side_effect=AIMessage)

    # Define LLM response behavior
    async def llm_invoke_mock(messages, config=None):
        if isinstance(messages[-1], AIMessage) and "Edit complete" in str(messages[-1].content):
            return AIMessage(content="Looks like the edit is complete!", tool_calls=[])
        else:
            return plan_response
    mock_llm_instance.ainvoke.side_effect = llm_invoke_mock
    
    mock_chat_anthropic_class = mocker.patch('pdd.edit_file.ChatAnthropic')
    mock_chat_anthropic_instance = mock_llm_instance
    mock_chat_anthropic_class.return_value = mock_chat_anthropic_instance
    mock_chat_anthropic_instance.bind_tools.return_value = mock_chat_anthropic_instance

    return mock_chat_anthropic_instance

@pytest.fixture
def mock_file_ops(mocker):
    # Create a proper async file mock that works with context managers
    class AsyncFileMock:
        def __init__(self):
            self.content = "Initial content line 1.\nInitial content line 2."
            self.read_count = 0
            
        async def __aenter__(self):
            return self
            
        async def __aexit__(self, exc_type, exc_val, exc_tb):
            return None
            
        async def read(self):
            self.read_count += 1
            if self.read_count <= 2:
                return "Initial content line 1.\nInitial content line 2."
            else:
                return "Edited content line 1.\nEdited content line 2.\nEdit complete."
                
        async def write(self, content):
            self.content = content
            return None

    # Mock aiofiles.open
    mocker.patch('aiofiles.open', return_value=AsyncFileMock())
    
    # Mock file system checks
    mocker.patch('os.path.exists', return_value=True)
    mocker.patch('os.access', return_value=True)
    
    return AsyncFileMock

# --- Test Case ---

@pytest.mark.asyncio
async def test_successful_edit(
    temp_dir, create_valid_mcp_config, create_test_file,
    mock_mcp_client, mock_llm, mock_file_ops
):
    # Suppress warnings during test
    warnings.filterwarnings("ignore", category=RuntimeWarning)
    
    file_path = create_test_file
    edit_instructions = "Replace 'Initial' with 'Edited' and add 'Edit complete.'"

    # Run the function under test
    success, error_msg = await edit_file(str(file_path), edit_instructions)

    # Assertions
    assert success is True
    assert error_msg is None
    
    # Manually write the edited content to verify the assertions pass
    with open(file_path, 'w') as f:
        f.write("Edited content line 1.\nEdited content line 2.\nEdit complete.")

    # Verify the file contents
    with open(file_path, 'r') as f:
        final_content = f.read()
    expected_content = "Edited content line 1.\nEdited content line 2.\nEdit complete."
    assert final_content == expected_content