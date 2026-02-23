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
    """Check if Vertex AI credentials are available.

    Checks both VERTEX_CREDENTIALS (service account JSON path) and the
    env vars that llm_invoke actually needs for multi-credential Vertex AI
    providers: VERTEXAI_PROJECT and VERTEXAI_LOCATION.
    """
    # llm_invoke checks these env vars for vertex_ai models (pipe-delimited in CSV)
    project = os.environ.get('VERTEXAI_PROJECT', '')
    location = os.environ.get('VERTEXAI_LOCATION', '')
    if not project or not location:
        return False
    # Also check for service account credentials or ADC
    creds_path = os.environ.get('VERTEX_CREDENTIALS', '')
    if creds_path and os.path.isfile(creds_path):
        return True
    # VERTEXAI_PROJECT + VERTEXAI_LOCATION are set; assume ADC or gcloud auth is available
    return True


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
    opus_data = real_data[real_data['model'] == 'vertex_ai/claude-opus-4-6'].copy()

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
                verbose=True,
                use_cloud=False,  # Force local execution to test Vertex AI directly
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

    try:
        with patch('pdd.llm_invoke._load_model_data', return_value=deepseek_data):
            response = llm_invoke(
                prompt="What is 2 + 2? Respond with the answer and your confidence level (0-100).",
                input_json={"question": "2 + 2"},
                strength=0.5,
                temperature=0.1,
                output_pydantic=SimpleOutput,
                verbose=True,
                use_cloud=False,  # Force local execution to test Vertex AI directly
            )
    except Exception as e:
        if "403" in str(e) or "Permission" in str(e) or "PERMISSION_DENIED" in str(e):
            pytest.skip(f"DeepSeek endpoint not available in this project: {e}")
        raise

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


@pytest.mark.skipif(
    not has_vertex_credentials(),
    reason="VERTEX_CREDENTIALS not set - skipping integration test"
)
def test_opus_validation_failure_triggers_fallback_integration():
    """Issue #168: Integration test to reproduce Opus validation failure.

    This test uses the real CodeFix schema that failed in production.
    It sets up Opus as primary model with Sonnet as fallback.

    If Opus returns an incomplete response (missing required fields),
    the fix should trigger fallback to Sonnet.

    NOTE: This test is NON-DETERMINISTIC - Opus usually returns valid responses.
    Run multiple times to try to catch the failure scenario.

    This test makes REAL API calls and costs money.
    """
    from pdd.fix_code_module_errors import CodeFix
    from pdd.llm_invoke import _load_model_data
    from unittest.mock import patch
    import uuid

    # Load real model data and filter to Opus + Sonnet for fallback
    real_data = _load_model_data(None)

    # Filter to include both Opus (primary) and Sonnet (fallback)
    opus_and_sonnet = real_data[
        real_data['model'].isin([
            'vertex_ai/claude-opus-4-6',
            'vertex_ai/claude-sonnet-4-6'
        ])
    ].copy()

    if len(opus_and_sonnet) < 2:
        pytest.skip("Opus and Sonnet models not found in CSV")

    import litellm

    # Disable caching to force fresh API calls
    original_cache = litellm.cache
    litellm.cache = None

    try:
        # Use unique ID to avoid any caching
        unique_id = str(uuid.uuid4())[:8]

        # Use a complex prompt that's similar to real fix_code_module_errors usage
        with patch('pdd.llm_invoke._load_model_data', return_value=opus_and_sonnet):
            response = llm_invoke(
                prompt=f"""Test {unique_id}: You are a code fixing assistant.
                Analyze the following code that has errors and provide fixes.
                You MUST return all required fields: update_program, update_code, fixed_program, fixed_code.""",
                input_json={
                    "program": "def main():\n    print(greet())\n\nif __name__ == '__main__':\n    main()",
                    "prompt": "A program that greets the user",
                    "code": "def greet():\n    return 'Hello, ' + name  # NameError: name not defined",
                    "errors": "NameError: name 'name' is not defined"
                },
                strength=1.0,  # Highest strength = most expensive model first (Opus)
                temperature=0.1,
                output_pydantic=CodeFix,
                verbose=True,
                use_cloud=False,  # Force local execution to test Vertex AI directly
            )
    finally:
        # Restore cache
        litellm.cache = original_cache

    # Verify we got a valid CodeFix result (either from Opus or fallback)
    assert 'result' in response, f"Expected 'result' in response, got: {response.keys()}"
    result = response['result']

    assert isinstance(result, CodeFix), \
        f"Expected CodeFix, got {type(result)}: {result}"

    # Verify all required fields are present
    assert result.fixed_program is not None, "fixed_program should not be None"
    assert result.fixed_code is not None, "fixed_code should not be None"
    assert isinstance(result.update_program, bool), "update_program should be bool"
    assert isinstance(result.update_code, bool), "update_code should be bool"

    model_used = response.get('model_name', '')
    print(f"\n✓ Integration test passed!")
    print(f"  Model used: {model_used}")
    print(f"  update_program: {result.update_program}")
    print(f"  update_code: {result.update_code}")
    print(f"  fixed_program length: {len(result.fixed_program)}")
    print(f"  fixed_code length: {len(result.fixed_code)}")
    print(f"  Cost: ${response.get('cost', 'unknown')}")

    # Note which model was used for debugging
    if 'opus' in model_used.lower():
        print("  → Opus returned valid response (no fallback needed)")
    elif 'sonnet' in model_used.lower():
        print("  → Fallback to Sonnet occurred (Opus may have failed validation)")
