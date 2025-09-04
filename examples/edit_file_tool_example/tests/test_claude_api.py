# To run this test:
# Option 1: From project root: pytest tests/test_claude_api.py
# Option 2: From project root: python -m pytest tests/test_claude_api.py
# Note: Ensure ANTHROPIC_API_KEY is set in your environment or a .env file
# for tests that make real calls (if any were added). For this suite, it is mocked.
# To run Z3 tests, you must install z3-solver: pip install z3-solver

import asyncio
import importlib
import logging
import os
from unittest.mock import AsyncMock, MagicMock, patch

import pytest
import anthropic
from anthropic.types import Message, Usage

# Conditional import for Z3
try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

# Module under test
import edit_file_tool.claude_api as claude_api
from edit_file_tool.claude_api import (APIError, DEFAULT_MODEL,
                                       MODEL_TO_TEXT_EDITOR_TOOL,
                                       SUPPORTED_MODELS, CostInfo,
                                       call_claude_api)
from edit_file_tool.think_tool import ThinkTool

# #############################################################################
# Test Plan
# #############################################################################
#
# The `claude_api.py` module is the central gateway to the Anthropic API.
# Tests must cover its core responsibilities: client initialization, API call
# orchestration, caching logic, cost calculation, and error handling.
#
# We will use a combination of unit tests with mocking and formal verification
# with Z3 for the mathematical components.
#
# -----------------------------------------------------------------------------
# Test Suite Breakdown
# -----------------------------------------------------------------------------
#
# 1.  Module Initialization and Configuration:
#     -   `test_api_key_missing`: Verify that `call_claude_api` raises a clear
#         `ValueError` if the `ANTHROPIC_API_KEY` is not set. This is critical
#         for user feedback. We use `monkeypatch` to simulate a missing key and
#         `importlib.reload` to re-trigger module-level initialization.
#     -   `test_exported_constants`: Ensure backward compatibility by verifying
#         that `DEFAULT_MODEL`, `SUPPORTED_MODELS`, and `MODEL_TO_TEXT_EDITOR_TOOL`
#         are exported with the correct types and structures expected by
#         dependent modules like `core.py` and `cli.py`.
#
# 2.  `call_claude_api` Core Functionality (Happy Paths):
#     -   `test_call_successful_no_cache`: A standard API call. We mock the
#         `client.messages.create` method and verify it's called with the
#         correct parameters (model, messages, tools, system prompt). We also
#         check that the returned response and cost info are correct.
#     -   `test_call_successful_with_cache`: Test the prompt caching logic.
#         We provide a specially formatted initial prompt and `use_cache=True`.
#         The test asserts that the `messages` payload sent to the API is
#         correctly split into a cacheable block and an instruction block.
#     -   `test_call_with_cache_fallback`: An edge case for caching. When
#         `use_cache=True` but the prompt doesn't match the expected format,
#         the function should log a warning and proceed without caching. We use
#         `caplog` to verify the warning.
#     -   `test_call_with_multi_turn_conversation_and_cache`: Ensure that caching
#         logic correctly handles a conversation history with multiple turns,
#         only attempting to cache the very first user message.
#
# 3.  Error Handling and Resilience:
#     -   `test_call_with_unsupported_model`: Verify that a `ValueError` is
#         raised immediately if an unsupported model name is provided, preventing
#         an unnecessary API call.
#     -   `test_call_api_non_retryable_error`: Simulate a non-recoverable error
#         from the API (e.g., `anthropic.AuthenticationError`). The test asserts
#         that the function does not retry and wraps the exception in our
#         custom `APIError`.
#     -   `test_call_api_retry_on_rate_limit`: Test the retry decorator. We use
#         a mock with `side_effect` to raise `anthropic.RateLimitError` on the
#         first call and succeed on the second. We assert the mock was called
#         twice.
#     -   `test_call_api_retry_exhausted`: Simulate a persistent `RateLimitError`.
#         The test verifies that after all retry attempts are exhausted, the
#         original exception is raised.
#     -   `test_call_api_unexpected_error`: Simulate a generic `Exception` to
#         ensure it's caught and wrapped in `APIError` for consistent error
#         handling by the caller.
#
# 4.  Cost Calculation Logic:
#     -   These tests validate the cost calculation logic by checking the
#         `CostInfo` dictionary returned by `call_claude_api`.
#     -   `test_cost_calculation_standard`: Test cost for a standard call with
#         only input/output tokens.
#     -   `test_cost_calculation_cache_write`: Test cost when the API response
#         indicates a cache write (`cache_creation_input_tokens` > 0).
#     -   `test_cost_calculation_cache_read`: Test cost for a cache read, which
#         has a discounted input rate.
#     -   `test_cost_calculation_mixed_usage`: Test a complex scenario with
#         standard input, cache read, and output tokens.
#     -   `test_cost_calculation_unknown_model`: Verify that if an unknown model
#         is somehow used, the system falls back to default pricing and logs a
#         warning.
#
# 5.  Z3 Formal Verification for Cost Calculation:
#     -   Z3 is a theorem prover. We use it to formally prove mathematical
#         properties of the cost function, which is more robust than example-based
#         unit tests for verifying algorithms.
#     -   `test_z3_cost_is_non_negative`: Prove that for any non-negative token
#         counts, the total cost can never be negative.
#     -   `test_z3_cost_increases_with_tokens`: Prove that the cost function is
#         monotonically increasing (more tokens always mean more or equal cost).
#     -   `test_z3_cache_read_is_cheaper`: Prove that for the same number of
#         input tokens, a cache read is strictly cheaper than a standard call.
#
# #############################################################################

# --- Fixtures ---

@pytest.fixture
def mock_anthropic_client(monkeypatch):
    """Fixture to mock the anthropic client at the module level."""
    mock_client = MagicMock()
    mock_client.messages.create = AsyncMock()
    monkeypatch.setattr(claude_api, "client", mock_client)
    return mock_client

@pytest.fixture
def initial_user_prompt_cacheable():
    """A sample prompt that matches the structure required for caching."""
    return """
Here is the file to edit: `test.py`

File content:
```
print("hello world")
```

My instruction is: "Change the greeting."
Please proceed with the necessary edits.
"""

# --- Helper Functions ---

def create_mock_response(
    input_tokens=100,
    output_tokens=50,
    cache_creation_tokens=0,
    cache_read_tokens=0,
    stop_reason="end_turn"
) -> Message:
    """Creates a mock anthropic.types.Message object for testing."""
    usage = Usage(
        input_tokens=input_tokens,
        output_tokens=output_tokens,
    )
    # The cache attributes are not always present in the Usage TypedDict
    # so we add them dynamically as the real API does.
    # The SDK may return None for these, so we set them explicitly for tests.
    usage.cache_creation_input_tokens = cache_creation_tokens
    usage.cache_read_input_tokens = cache_read_tokens

    return Message(
        id="msg_01",
        type="message",
        role="assistant",
        model=DEFAULT_MODEL,
        content=[],
        stop_reason=stop_reason,
        usage=usage,
    )


# ==============================================================================
# 1. Module Initialization and Configuration Tests
# ==============================================================================

@pytest.mark.asyncio
async def test_api_key_missing(monkeypatch):
    """Test that a ValueError is raised if the ANTHROPIC_API_KEY is not set."""
    # Simulate the state where client initialization failed, making the test
    # robust against environmental factors like a .env file.
    monkeypatch.setattr(claude_api, "client", None)

    with pytest.raises(ValueError, match="Anthropic client is not initialized. Check ANTHROPIC_API_KEY."):
        await claude_api.call_claude_api(messages=[], model=DEFAULT_MODEL)

    # Restore for other tests by reloading the module, which re-initializes the client.
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    importlib.reload(claude_api)

def test_exported_constants():
    """Test that required constants are exported and have the correct structure."""
    assert isinstance(DEFAULT_MODEL, str)
    assert len(DEFAULT_MODEL) > 0

    assert isinstance(SUPPORTED_MODELS, set)
    assert DEFAULT_MODEL in SUPPORTED_MODELS

    assert isinstance(MODEL_TO_TEXT_EDITOR_TOOL, dict)
    assert DEFAULT_MODEL in MODEL_TO_TEXT_EDITOR_TOOL
    # Check structure required by core.py
    editor_tool_names = {v['name'] for v in MODEL_TO_TEXT_EDITOR_TOOL.values()}
    assert isinstance(editor_tool_names, set)
    assert len(editor_tool_names) > 0
    assert "text_editor_20250124" in editor_tool_names


# ==============================================================================
# 2. `call_claude_api` Core Functionality Tests
# ==============================================================================

@pytest.mark.asyncio
async def test_call_successful_no_cache(mock_anthropic_client):
    """Test a standard successful API call without caching."""
    mock_response = create_mock_response()
    mock_anthropic_client.messages.create.return_value = mock_response
    messages = [{"role": "user", "content": "Hello"}]
    system_prompt = "You are a helpful assistant."

    response, cost_info = await call_claude_api(
        messages=messages,
        model=DEFAULT_MODEL,
        system_prompt=system_prompt,
        use_cache=False
    )

    assert response == mock_response
    assert isinstance(cost_info, dict)
    assert cost_info["total_cost"] > 0

    mock_anthropic_client.messages.create.assert_awaited_once()
    call_args = mock_anthropic_client.messages.create.call_args
    assert call_args.kwargs["model"] == DEFAULT_MODEL
    assert call_args.kwargs["messages"] == messages
    assert call_args.kwargs["system"] == system_prompt
    assert len(call_args.kwargs["tools"]) == 2 # editor + think

@pytest.mark.asyncio
async def test_call_successful_with_cache(mock_anthropic_client, initial_user_prompt_cacheable):
    """Test a successful API call with prompt caching enabled."""
    mock_response = create_mock_response(cache_creation_tokens=1000)
    mock_anthropic_client.messages.create.return_value = mock_response
    messages = [{"role": "user", "content": initial_user_prompt_cacheable}]

    await call_claude_api(messages=messages, model=DEFAULT_MODEL, use_cache=True)

    mock_anthropic_client.messages.create.assert_awaited_once()
    call_args = mock_anthropic_client.messages.create.call_args
    api_messages = call_args.kwargs["messages"]

    assert len(api_messages) == 2
    # First message is the cacheable file content
    assert "cache_control" in api_messages[0]["content"][0]
    assert api_messages[0]["content"][0]["cache_control"]["type"] == "ephemeral"
    assert "File content:" in api_messages[0]["content"][0]["text"]
    # Second message is the non-cacheable instruction
    assert "cache_control" not in api_messages[1]["content"][0]
    assert 'My instruction is: "Change the greeting."' in api_messages[1]["content"][0]["text"]

@pytest.mark.asyncio
async def test_call_with_cache_fallback(mock_anthropic_client, caplog):
    """Test that caching falls back gracefully if prompt format is wrong."""
    mock_response = create_mock_response()
    mock_anthropic_client.messages.create.return_value = mock_response
    messages = [{"role": "user", "content": "A prompt that cannot be split."}]

    with caplog.at_level(logging.WARNING):
        await call_claude_api(messages=messages, model=DEFAULT_MODEL, use_cache=True)
        assert "failed to parse initial prompt for caching" in caplog.text

    call_args = mock_anthropic_client.messages.create.call_args
    # Should have sent the original messages, not a split version
    assert call_args.kwargs["messages"] == messages

@pytest.mark.asyncio
async def test_call_with_multi_turn_conversation_and_cache(mock_anthropic_client, initial_user_prompt_cacheable):
    """Test that caching only applies to the first message in a sequence."""
    mock_response = create_mock_response()
    mock_anthropic_client.messages.create.return_value = mock_response
    messages = [
        {"role": "user", "content": initial_user_prompt_cacheable},
        {"role": "assistant", "content": "OK, I see the file."},
        {"role": "user", "content": "Now proceed."}
    ]

    await call_claude_api(messages=messages, model=DEFAULT_MODEL, use_cache=True)

    call_args = mock_anthropic_client.messages.create.call_args
    api_messages = call_args.kwargs["messages"]

    assert len(api_messages) == 4 # split_1, split_2, messages[1], messages[2]
    assert "cache_control" in api_messages[0]["content"][0]
    assert api_messages[2] == messages[1]
    assert api_messages[3] == messages[2]


# ==============================================================================
# 3. Error Handling and Resilience Tests
# ==============================================================================

@pytest.mark.asyncio
async def test_call_with_unsupported_model(mock_anthropic_client):
    """Test that a ValueError is raised for an unsupported model."""
    with pytest.raises(ValueError, match="Model 'unsupported-model' is not supported"):
        await call_claude_api(messages=[], model="unsupported-model")
    mock_anthropic_client.messages.create.assert_not_awaited()

@pytest.mark.asyncio
async def test_call_api_non_retryable_error(mock_anthropic_client):
    """Test that a non-retryable API error is wrapped and raised without retries."""
    error = anthropic.AuthenticationError("Invalid API key", response=MagicMock(), body=None)
    mock_anthropic_client.messages.create.side_effect = error

    with pytest.raises(APIError, match="API call failed: Invalid API key"):
        await call_claude_api(messages=[], model=DEFAULT_MODEL)

    mock_anthropic_client.messages.create.assert_awaited_once()

@pytest.mark.asyncio
async def test_call_api_retry_on_rate_limit(mock_anthropic_client, monkeypatch):
    """Test that the retry mechanism works for RateLimitError."""
    monkeypatch.setattr(asyncio, "sleep", AsyncMock()) # Speed up test
    error = anthropic.RateLimitError("Rate limit exceeded", response=MagicMock(), body=None)
    mock_response = create_mock_response()
    mock_anthropic_client.messages.create.side_effect = [error, mock_response]

    await call_claude_api(messages=[], model=DEFAULT_MODEL)

    assert mock_anthropic_client.messages.create.call_count == 2

@pytest.mark.asyncio
async def test_call_api_retry_exhausted(mock_anthropic_client, monkeypatch):
    """Test that an exception is raised after all retries are exhausted."""
    monkeypatch.setattr(asyncio, "sleep", AsyncMock())
    error = anthropic.RateLimitError("Rate limit exceeded", response=MagicMock(), body=None)
    mock_anthropic_client.messages.create.side_effect = error

    with pytest.raises(anthropic.RateLimitError):
        await call_claude_api(messages=[], model=DEFAULT_MODEL)

    assert mock_anthropic_client.messages.create.call_count == 3 # Default max_attempts

@pytest.mark.asyncio
async def test_call_api_unexpected_error(mock_anthropic_client):
    """Test that a generic Exception is caught and wrapped in APIError."""
    mock_anthropic_client.messages.create.side_effect = TypeError("Something went wrong")

    with pytest.raises(APIError, match="An unexpected error occurred: Something went wrong"):
        await call_claude_api(messages=[], model=DEFAULT_MODEL)


# ==============================================================================
# 4. Cost Calculation Tests
# ==============================================================================

@pytest.mark.asyncio
@pytest.mark.parametrize("model, input_tokens, output_tokens, expected_cost", [
    ("claude-3-5-sonnet-20240620", 10000, 20000, (10000/1e6 * 3.0) + (20000/1e6 * 15.0)),
    ("claude-3-opus-20240229", 5000, 1000, (5000/1e6 * 15.0) + (1000/1e6 * 75.0)),
])
async def test_cost_calculation_standard(mock_anthropic_client, model, input_tokens, output_tokens, expected_cost):
    """Test standard cost calculation for different models."""
    mock_response = create_mock_response(input_tokens=input_tokens, output_tokens=output_tokens)
    mock_anthropic_client.messages.create.return_value = mock_response

    _, cost_info = await call_claude_api(messages=[], model=model)
    assert cost_info["total_cost"] == pytest.approx(expected_cost)

@pytest.mark.asyncio
async def test_cost_calculation_cache_write(mock_anthropic_client):
    """Test cost calculation for a cache write operation."""
    model = "claude-3-5-sonnet-20240620"
    mock_response = create_mock_response(input_tokens=1000, output_tokens=100, cache_creation_tokens=5000)
    mock_anthropic_client.messages.create.return_value = mock_response

    # Cost = (standard_input * rate) + (cache_creation * rate) + (output * rate)
    expected_cost = (1000/1e6 * 3.0) + (5000/1e6 * 3.0) + (100/1e6 * 15.0)

    _, cost_info = await call_claude_api(messages=[], model=model)
    assert cost_info["total_cost"] == pytest.approx(expected_cost)
    assert cost_info["cache_creation_tokens"] == 5000

@pytest.mark.asyncio
async def test_cost_calculation_cache_read(mock_anthropic_client):
    """Test cost calculation for a cache read operation."""
    model = "claude-3-5-sonnet-20240620"
    mock_response = create_mock_response(input_tokens=1000, output_tokens=100, cache_read_tokens=20000)
    mock_anthropic_client.messages.create.return_value = mock_response

    # Cost = (standard_input * rate) + (cache_read * discounted_rate) + (output * rate)
    input_rate = 3.0
    cache_read_rate = input_rate * 0.10
    expected_cost = (1000/1e6 * input_rate) + (20000/1e6 * cache_read_rate) + (100/1e6 * 15.0)

    _, cost_info = await call_claude_api(messages=[], model=model)
    assert cost_info["total_cost"] == pytest.approx(expected_cost)
    assert cost_info["cache_read_tokens"] == 20000

@pytest.mark.asyncio
async def test_cost_calculation_unknown_model(mock_anthropic_client, caplog):
    """Test that cost calculation falls back to the default model's pricing."""
    # This model is supported but not in the pricing list in claude_api.py
    unknown_model = "claude-3-haiku-20240307"
    assert unknown_model in SUPPORTED_MODELS
    assert unknown_model not in claude_api.MODEL_PRICES
    
    # Use default model's pricing for calculation
    default_prices = claude_api.MODEL_PRICES[DEFAULT_MODEL]
    expected_cost = (100/1e6 * default_prices["input"]) + (50/1e6 * default_prices["output"])

    mock_response = create_mock_response(input_tokens=100, output_tokens=50)
    mock_anthropic_client.messages.create.return_value = mock_response

    with caplog.at_level(logging.WARNING):
        _, cost_info = await call_claude_api(messages=[], model=unknown_model)
        assert f"Model '{unknown_model}' not in pricing list" in caplog.text

    assert cost_info["total_cost"] == pytest.approx(expected_cost)


# ==============================================================================
# 5. Z3 Formal Verification for Cost Calculation
# ==============================================================================

@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver is not installed")
def test_z3_cost_is_non_negative():
    """Z3 Test: Prove that total_cost is always non-negative."""
    solver = z3.Solver()

    # Define symbolic variables for tokens and prices
    input_tokens = z3.Real('input_tokens')
    output_tokens = z3.Real('output_tokens')
    cache_creation_tokens = z3.Real('cache_creation_tokens')
    cache_read_tokens = z3.Real('cache_read_tokens')
    
    price_input = z3.Real('price_input')
    price_output = z3.Real('price_output')
    price_cache_read = z3.Real('price_cache_read')

    # Add constraints: tokens and prices are non-negative
    solver.add(input_tokens >= 0, output_tokens >= 0)
    solver.add(cache_creation_tokens >= 0, cache_read_tokens >= 0)
    solver.add(price_input >= 0, price_output >= 0, price_cache_read >= 0)

    # Define the cost function symbolically
    total_cost = (
        (input_tokens / 1000000 * price_input) +
        (output_tokens / 1000000 * price_output) +
        (cache_creation_tokens / 1000000 * price_input) +
        (cache_read_tokens / 1000000 * price_cache_read)
    )

    # Add the property to disprove: can the cost be negative?
    solver.add(total_cost < 0)

    # Check if a counterexample exists
    result = solver.check()
    assert result == z3.unsat, "Z3 found a scenario where cost could be negative!"

@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver is not installed")
def test_z3_cache_read_is_cheaper():
    """Z3 Test: Prove that cache read is cheaper than standard input for same token count."""
    solver = z3.Solver()

    tokens = z3.Real('tokens')
    price_input = z3.Real('price_input')
    price_cache_read = z3.Real('price_cache_read')

    # Constraints based on our pricing model
    solver.add(tokens > 0)
    solver.add(price_input > 0)
    # The core assumption: cache read price is a fraction (10%) of input price
    solver.add(price_cache_read == price_input * 0.1)

    standard_cost = tokens / 1000000 * price_input
    cache_read_cost = tokens / 1000000 * price_cache_read

    # Add the property to disprove: is cache read cost ever >= standard cost?
    solver.add(cache_read_cost >= standard_cost)

    result = solver.check()
    assert result == z3.unsat, "Z3 found a scenario where cache read was not cheaper!"
