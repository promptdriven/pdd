# Integration tests for llm_invoke - requires real API credentials
#
# Run with: pytest tests/test_llm_invoke_integration.py -v
# Skip with: pytest tests/test_llm_invoke_integration.py -v -m "not integration"
#
# These tests make REAL API calls and cost money. They are skipped by default
# unless VERTEX_CREDENTIALS is set in the environment.

import os
import pytest
from pydantic import BaseModel

from pdd.llm_invoke import llm_invoke


# Mark all tests in this file as integration tests
pytestmark = pytest.mark.integration


class SimpleOutput(BaseModel):
    """Simple Pydantic model for testing structured output."""
    answer: str
    confidence: int


def has_vertex_credentials() -> bool:
    """Check if Vertex AI credentials are available."""
    creds_path = os.environ.get('VERTEX_CREDENTIALS', '')
    if not creds_path:
        return False
    # Check if it's a file path that exists, or if it looks like JSON
    if os.path.isfile(creds_path):
        return True
    # Could be inline JSON or ADC - assume available if set
    return bool(creds_path)


@pytest.mark.skipif(
    not has_vertex_credentials(),
    reason="VERTEX_CREDENTIALS not set - skipping integration test"
)
def test_vertex_ai_claude_opus_structured_output_integration():
    """Integration test: Verify Claude Opus on Vertex AI works with structured output.

    This test validates that the LiteLLM upgrade (>=1.81.0) fixes the beta headers
    issue (#17755) for Vertex AI Claude models.

    Before the fix: Vertex AI rejected requests with anthropic-beta headers
    After the fix: Structured output works correctly

    This test makes a REAL API call and costs money.
    """
    from pdd.llm_invoke import _load_model_data
    from unittest.mock import patch

    # Filter to only include Vertex AI Claude Opus
    real_data = _load_model_data(None)
    opus_data = real_data[real_data['model'] == 'vertex_ai/claude-opus-4-5'].copy()

    if len(opus_data) == 0:
        pytest.skip("Vertex AI Claude Opus model not found in CSV")

    import uuid
    import litellm

    # Disable caching to force a fresh API call
    original_cache = litellm.cache
    litellm.cache = None

    try:
        # Use unique prompt to avoid any caching
        unique_id = str(uuid.uuid4())[:8]
        with patch('pdd.llm_invoke._load_model_data', return_value=opus_data):
            response = llm_invoke(
                prompt=f"Test {unique_id}: What is 2 + 2? Respond with the answer and your confidence level (0-100).",
                input_json={"question": "2 + 2", "test_id": unique_id},
                strength=0.5,
                temperature=0.1,
                output_pydantic=SimpleOutput,
                verbose=True
            )
    finally:
        # Restore cache
        litellm.cache = original_cache

    # Verify we got a valid response
    assert 'result' in response, f"Expected 'result' in response, got: {response.keys()}"
    result = response['result']

    # Verify it's the correct Pydantic type
    assert isinstance(result, SimpleOutput), \
        f"Expected SimpleOutput, got {type(result)}: {result}"

    # Verify the answer is reasonable
    assert result.answer is not None, "Expected non-null answer"
    assert isinstance(result.confidence, int), \
        f"Expected int confidence, got {type(result.confidence)}"

    # Verify we used a Claude model (Opus or Sonnet on Vertex AI)
    model_used = response.get('model_name', '')
    assert 'claude' in model_used.lower() or 'vertex_ai' in model_used.lower(), \
        f"Expected Claude model on Vertex AI, got: {model_used}"

    print(f"\n✓ Integration test passed!")
    print(f"  Model: {model_used}")
    print(f"  Result: {result}")
    print(f"  Cost: ${response.get('cost', 'unknown')}")


@pytest.mark.skipif(
    not has_vertex_credentials(),
    reason="VERTEX_CREDENTIALS not set - skipping integration test"
)
def test_vertex_ai_deepseek_structured_output_integration():
    """Integration test: Verify DeepSeek on Vertex AI MaaS works with structured output.

    This test validates that after setting structured_output=True in the CSV,
    DeepSeek MaaS correctly returns structured output.

    This test makes a REAL API call and costs money.
    """
    # Use a model data filter to specifically target DeepSeek
    from pdd.llm_invoke import _load_model_data
    from unittest.mock import patch

    real_data = _load_model_data(None)
    deepseek_data = real_data[real_data['model'] == 'vertex_ai/deepseek-ai/deepseek-v3.2-maas'].copy()

    if len(deepseek_data) == 0:
        pytest.skip("DeepSeek MaaS model not found in CSV")

    with patch('pdd.llm_invoke._load_model_data', return_value=deepseek_data):
        response = llm_invoke(
            prompt="What is 2 + 2? Respond with the answer and your confidence level (0-100).",
            input_json={"question": "2 + 2"},
            strength=0.5,
            temperature=0.1,
            output_pydantic=SimpleOutput,
            verbose=True
        )

    # Verify we got a valid response
    assert 'result' in response, f"Expected 'result' in response, got: {response.keys()}"
    result = response['result']

    # Verify it's the correct Pydantic type
    assert isinstance(result, SimpleOutput), \
        f"Expected SimpleOutput, got {type(result)}: {result}"

    # Verify the answer is reasonable
    assert result.answer is not None, "Expected non-null answer"
    assert isinstance(result.confidence, int), \
        f"Expected int confidence, got {type(result.confidence)}"

    # Verify we used DeepSeek
    model_used = response.get('model_name', '')
    assert 'deepseek' in model_used.lower(), \
        f"Expected DeepSeek model, got: {model_used}"

    print(f"\n✓ Integration test passed!")
    print(f"  Model: {model_used}")
    print(f"  Result: {result}")
    print(f"  Cost: ${response.get('cost', 'unknown')}")
