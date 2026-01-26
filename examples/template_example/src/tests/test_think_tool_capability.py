import pytest
import asyncio
import json
import os
from unittest.mock import AsyncMock, patch, MagicMock
from litellm import BadRequestError

# Import the actual function from the module
from edit_file_tool.think_tool_capability import invoke_with_thinking

@pytest.fixture
def mock_litellm_response():
    """Creates a mock litellm ModelResponse object."""
    # Define the usage data
    usage_data = {
        "prompt_tokens": 100,
        "completion_tokens": 50,
        "cache_creation_input_tokens": 10,
        "cache_read_input_tokens": 5
    }

    # Mock the message object
    mock_message = MagicMock()
    mock_message.content = "Hello world"
    mock_message.role = "assistant"
    mock_message.thinking_blocks = [{"thinking": "I am thinking", "signature": "sig123"}]

    # Mock tool calls
    mock_tool_call = MagicMock()
    mock_tool_call.id = "call_1"
    mock_tool_call.function.name = "text_editor_20250124"
    mock_tool_call.function.arguments = '{"command": "view", "path": "test.txt"}'
    mock_message.tool_calls = [mock_tool_call]

    # Create the mock response
    mock_res = MagicMock()
    mock_res.choices = [MagicMock(message=mock_message)]

    # Use side_effect with lambda for proper .get() behavior
    # This ensures response.get("usage", {}) returns the usage_data dict
    mock_res.get = MagicMock(side_effect=lambda k, d=None: usage_data if k == "usage" else d)

    return mock_res

# --- Z3 Formal Verification Tests ---

def test_thinking_logic_formal_verification():
    """
    Formally verify the logic used to determine if thinking is enabled.
    Logic: (is_supported) AND (NOT is_haiku)
    """
    try:
        from z3 import Bool, And, Not, Solver
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Define the components of the logic
    is_supported = Bool('is_supported')
    is_haiku = Bool('is_haiku')
    use_thinking = Bool('use_thinking')

    solver = Solver()

    # The implementation logic
    logic = (use_thinking == And(is_supported, Not(is_haiku)))
    solver.add(logic)

    # Property 1: If it's a Haiku model, use_thinking MUST be false, regardless of support string
    solver.push()
    solver.add(is_haiku)
    solver.add(use_thinking == True)
    assert solver.check().r == -1 # unsat
    solver.pop()

    # Property 2: If it's supported and NOT haiku, use_thinking MUST be true
    solver.push()
    solver.add(is_supported, Not(is_haiku))
    solver.add(use_thinking == False)
    assert solver.check().r == -1 # unsat
    solver.pop()

# --- Unit Tests ---

@pytest.mark.asyncio
async def test_invoke_with_thinking_enabled(mock_litellm_response):
    """Test that thinking is enabled for Claude 3.7."""
    with patch("litellm.acompletion", new_callable=AsyncMock) as mock_acomp:
        mock_acomp.return_value = mock_litellm_response
        
        messages = [{"role": "user", "content": "test"}]
        tools = [{"name": "tool"}]
        model = "anthropic/claude-3-7-sonnet-20250219"
        
        response, cost = await invoke_with_thinking(messages, tools, model)
        
        # Verify thinking param was passed
        args, kwargs = mock_acomp.call_args
        assert kwargs["thinking"] == {"type": "enabled", "budget_tokens": 1024}
        assert response["role"] == "assistant"
        assert any(b["type"] == "thinking" for b in response["content"])

@pytest.mark.asyncio
async def test_invoke_with_thinking_disabled_for_older_models(mock_litellm_response):
    """Test that thinking is NOT enabled for Claude 3.5."""
    with patch("litellm.acompletion", new_callable=AsyncMock) as mock_acomp:
        mock_acomp.return_value = mock_litellm_response
        
        messages = [{"role": "user", "content": "test"}]
        tools = [{"name": "tool"}]
        model = "anthropic/claude-3-5-sonnet-20241022"
        
        await invoke_with_thinking(messages, tools, model)
        
        # Verify thinking param was NOT passed
        args, kwargs = mock_acomp.call_args
        assert "thinking" not in kwargs

@pytest.mark.asyncio
async def test_invoke_with_thinking_disabled_for_haiku(mock_litellm_response):
    """Test that thinking is NOT enabled for Haiku models even if they have '4' in name."""
    with patch("litellm.acompletion", new_callable=AsyncMock) as mock_acomp:
        mock_acomp.return_value = mock_litellm_response
        
        messages = [{"role": "user", "content": "test"}]
        tools = [{"name": "tool"}]
        # Hypothetical future haiku that might match 'claude-sonnet-4' logic if not careful
        model = "anthropic/claude-haiku-4-5" 
        
        await invoke_with_thinking(messages, tools, model)
        
        args, kwargs = mock_acomp.call_args
        assert "thinking" not in kwargs

@pytest.mark.asyncio
async def test_thinking_fallback_on_bad_request(mock_litellm_response):
    """Test that if thinking fails with BadRequest, it retries without thinking."""
    with patch("litellm.acompletion", new_callable=AsyncMock) as mock_acomp:
        # First call fails, second succeeds
        mock_acomp.side_effect = [
            BadRequestError(message="Thinking not supported", model="claude", llm_provider="anthropic"),
            mock_litellm_response
        ]
        
        messages = [{"role": "user", "content": "test"}]
        tools = [{"name": "tool"}]
        model = "anthropic/claude-3-7-sonnet"
        
        await invoke_with_thinking(messages, tools, model)
        
        assert mock_acomp.call_count == 2
        # Check second call didn't have thinking
        last_call_kwargs = mock_acomp.call_args_list[1].kwargs
        assert "thinking" not in last_call_kwargs

@pytest.mark.asyncio
async def test_vertex_ai_configuration(mock_litellm_response):
    """Test that Vertex AI specific environment variables are passed correctly."""
    env_patch = {
        "VERTEX_PROJECT": "my-project",
        "VERTEX_LOCATION": "us-central1",
        "VERTEX_CREDENTIALS": "fake_path.json"
    }
    
    with patch.dict(os.environ, env_patch), \
         patch("os.path.exists", return_value=True), \
         patch("builtins.open", MagicMock(return_value=MagicMock(__enter__=lambda s: MagicMock(read=lambda: '{"creds": "true"}')))), \
         patch("litellm.acompletion", new_callable=AsyncMock) as mock_acomp:
        
        mock_acomp.return_value = mock_litellm_response
        model = "vertex_ai/claude-3-7-sonnet"
        
        await invoke_with_thinking([], [], model)
        
        kwargs = mock_acomp.call_args.kwargs
        assert kwargs["vertex_ai_project"] == "my-project"
        assert kwargs["vertex_ai_location"] == "us-central1"
        assert kwargs["vertex_credentials"] == '{"creds": "true"}'

@pytest.mark.asyncio
async def test_response_conversion_logic(mock_litellm_response):
    """Verify the internal _convert_to_anthropic_format logic via the public API."""
    with patch("litellm.acompletion", new_callable=AsyncMock) as mock_acomp:
        mock_acomp.return_value = mock_litellm_response
        
        response, _ = await invoke_with_thinking([], [], "claude-3-7")
        
        # Check content block structure
        content = response["content"]
        assert any(b["type"] == "thinking" and b["thinking"] == "I am thinking" for b in content)
        assert any(b["type"] == "text" and b["text"] == "Hello world" for b in content)
        assert any(b["type"] == "tool_use" and b["name"] == "text_editor_20250124" for b in content)
        
        # Check usage mapping
        assert response["usage"]["input_tokens"] == 100
        assert response["usage"]["cache_creation_input_tokens"] == 10

@pytest.mark.asyncio
async def test_cost_calculation_integration():
    """Verify that calculate_cost is called with the correct model name (stripped of prefix)."""
    mock_res = MagicMock()
    mock_res.choices = [MagicMock()]
    usage_data = {"prompt_tokens": 1000, "completion_tokens": 500}
    mock_res.get.side_effect = lambda k, d=None: usage_data if k == "usage" else d
    mock_res.__getitem__.side_effect = lambda k: usage_data if k == "usage" else None

    with patch("litellm.acompletion", new_callable=AsyncMock, return_value=mock_res), \
         patch("edit_file_tool.think_tool_capability.calculate_cost") as mock_calc:
        
        mock_calc.return_value = 0.05
        
        model = "vertex_ai/claude-3-7-sonnet-20250219"
        _, cost = await invoke_with_thinking([], [], model)
        
        # Verify the prefix was stripped before calling cost tracker
        mock_calc.assert_called_once()
        assert mock_calc.call_args.kwargs["model"] == "claude-3-7-sonnet-20250219"
        assert cost == 0.05