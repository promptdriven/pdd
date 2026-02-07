# tests/test_unfinished_prompt.py
import os
from pathlib import Path

import pytest
from unittest.mock import patch, Mock
from pdd.unfinished_prompt import unfinished_prompt, PromptAnalysis

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"

# Define a mock response for llm_invoke
mock_llm_response = {
    'result': {
        'reasoning': 'The prompt appears to be incomplete as it ends abruptly.',
        'is_finished': False
    },
    'cost': 0.012345,
    'model_name': 'mock-model'
}

@pytest.fixture
def mock_load_prompt_template_success():
    with patch('pdd.unfinished_prompt.load_prompt_template') as mock_load:
        mock_load.return_value = "Mock prompt template content."
        yield mock_load

@pytest.fixture
def mock_load_prompt_template_failure():
    with patch('pdd.unfinished_prompt.load_prompt_template') as mock_load:
        mock_load.return_value = None
        yield mock_load

@pytest.fixture
def mock_llm_invoke_success():
    with patch('pdd.unfinished_prompt.llm_invoke') as mock_invoke:
        # Create a PromptAnalysis instance for 'result'
        mock_prompt_analysis = PromptAnalysis(**mock_llm_response['result'])
        mock_response = {
            'result': mock_prompt_analysis,
            'cost': mock_llm_response['cost'],
            'model_name': mock_llm_response['model_name']
        }
        mock_invoke.return_value = mock_response
        yield mock_invoke

@pytest.fixture
def mock_llm_invoke_failure():
    with patch('pdd.unfinished_prompt.llm_invoke') as mock_invoke:
        mock_invoke.side_effect = Exception("LLM invocation failed.")
        yield mock_invoke


def test_unfinished_prompt_success(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.5,
        temperature=0.5,
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_empty_prompt(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="   ",
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "Prompt text must be a non-empty string" in str(exc_info.value)


def test_unfinished_prompt_non_string_prompt(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text=12345,  # Non-string input
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "Prompt text must be a non-empty string" in str(exc_info.value)


def test_unfinished_prompt_strength_below_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=-0.1,  # Invalid strength
            temperature=0.5,
            verbose=False
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_strength_above_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=1.1,  # Invalid strength
            temperature=0.5,
            verbose=False
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_temperature_below_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=-0.2,  # Invalid temperature
            verbose=False
        )
    assert "Temperature must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_temperature_above_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=1.5,  # Invalid temperature
            verbose=False
        )
    assert "Temperature must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_load_template_failure(
    mock_load_prompt_template_failure,
    mock_llm_invoke_success
):
    with pytest.raises(Exception) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "Failed to load prompt template" in str(exc_info.value)


def test_unfinished_prompt_llm_invoke_failure(
    mock_load_prompt_template_success,
    mock_llm_invoke_failure
):
    with pytest.raises(Exception) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "LLM invocation failed." in str(exc_info.value)


def test_unfinished_prompt_edge_strength_zero(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.0,  # Edge case
        temperature=0.5,
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_edge_strength_one(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=1.0,  # Edge case
        temperature=0.5,
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_edge_temperature_zero(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.5,
        temperature=0.0,  # Edge case
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_edge_temperature_one(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.5,
        temperature=1.0,  # Edge case
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']



def test_unfinished_prompt_marks_complete_python_as_finished(monkeypatch):
    """
    Failing test capturing the contract: a syntactically complete Python tail
    should be considered finished even if the LLM's raw judgment says otherwise.

    Current behavior (before fix): unfinished_prompt relies solely on the LLM
    and can return is_finished=False for complete code, causing loops.
    """
    # Ensure prompts are loadable
    repo_root = Path(__file__).resolve().parents[1]
    monkeypatch.setenv("PDD_PATH", str(repo_root / "pdd"))

    from pdd.unfinished_prompt import unfinished_prompt
    import pdd.unfinished_prompt as up_mod

    # Syntactically complete Python snippet (tail)
    sample = "def add(a, b):\n    return a + b\n"

    # Force model to claim 'unfinished' (simulating the problematic behavior)
    def llm_stub(*, prompt, input_json, strength, temperature, time, verbose=False, output_pydantic=None):
        # Construct the pydantic result with is_finished=False
        result = up_mod.PromptAnalysis(reasoning="stub", is_finished=False)
        return {"result": result, "cost": 0.0, "model_name": "mock"}

    monkeypatch.setattr(up_mod, "llm_invoke", llm_stub, raising=False)

    # Act
    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        verbose=False,
    )

    # Assert desired contract (expected to FAIL until multi-language prompt improvements or AST fallback)
    assert is_finished is True, (
        f"Expected syntactically complete Python to be finished; "
        f"got {is_finished}. Reason: {reasoning}"
    )


@pytest.mark.skipif(
    os.getenv("PDD_RUN_LLM_TESTS") != "1" and not RUN_ALL_TESTS_ENABLED,
    reason=(
        "Integration test requires live LLM access; set PDD_RUN_LLM_TESTS=1 "
        "or use --run-all / PDD_RUN_ALL_TESTS=1 to run."
    ),
)
def test_unfinished_prompt_llm_marks_complete_python_as_finished_integration():
    """
    Integration-style check using the actual prompt + llm_invoke.

    Skipped by default to keep unit tests deterministic and offline.
    Run with PDD_RUN_LLM_TESTS=1 (or pass --run-all / set PDD_RUN_ALL_TESTS=1,
    along with valid LLM credentials) to verify the model+preset prompt judge
    syntactically complete Python as finished.
    """
    # Arrange
    repo_root = Path(__file__).resolve().parents[1]
    os.environ.setdefault("PDD_PATH", str(repo_root / "pdd"))

    from pdd.unfinished_prompt import unfinished_prompt

    sample = "def add(a, b):\n    return a + b\n"

    # Act
    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        verbose=False,
    )

    # Assert (note: this will reflect real behavior of the prompt+model)
    assert is_finished is True, (
        f"Expected syntactically complete Python to be finished; got {is_finished}. "
        f"Reason: {reasoning}"
    )

 


@pytest.mark.skipif(
    os.getenv("PDD_RUN_LLM_TESTS") != "1" and not RUN_ALL_TESTS_ENABLED,
    reason=(
        "Integration test requires live LLM access; set PDD_RUN_LLM_TESTS=1 "
        "or use --run-all / PDD_RUN_ALL_TESTS=1 to run."
    ),
)
def test_unfinished_prompt_marks_tail_with_closing_fence_as_finished():
    """
    Integration test: a logically complete Python tail that ends with a closing
    code fence (```\n) should be treated as finished. Reproduces the scenario
    where continue_generation inspects a tail containing fence artifacts.
    """
    # Ensure prompts resolve from the package prompts dir
    repo_root = Path(__file__).resolve().parents[1]
    os.environ.setdefault("PDD_PATH", str(repo_root / "pdd"))

    from pdd.unfinished_prompt import unfinished_prompt

    # Tail fragment: valid concluding line followed by closing fence
    sample_tail = "    return a + b\n```\n"

    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample_tail,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        language="python",
        verbose=False,
    )

    assert is_finished is True, (
        f"Expected tail with closing fence to be considered finished; got {is_finished}. "
        f"Reason: {reasoning}"
    )


@pytest.mark.skipif(
    os.getenv("PDD_RUN_LLM_TESTS") != "1" and not RUN_ALL_TESTS_ENABLED,
    reason=(
        "Integration test requires live LLM access; set PDD_RUN_LLM_TESTS=1 "
        "or use --run-all / PDD_RUN_ALL_TESTS=1 to run."
    ),
)
def test_unfinished_prompt_marks_mid_block_tail_without_dangling_as_finished():
    """
    Integration test: a simple, self-contained statement should be
    considered finished by the LLM.
    """
    repo_root = Path(__file__).resolve().parents[1]
    os.environ.setdefault("PDD_PATH", str(repo_root / "pdd"))

    from pdd.unfinished_prompt import unfinished_prompt

    # Self-contained statement that is unambiguously complete
    sample_tail = "x = 42\n"

    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample_tail,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        language="python",
        verbose=False,
    )

    assert is_finished is True, (
        f"Expected simple assignment to be considered finished; got {is_finished}. "
        f"Reason: {reasoning}"
    )


# --- Tests for malformed LLM response handling ---
# These tests verify that unfinished_prompt handles cases where llm_invoke
# returns a string instead of a PromptAnalysis object (due to JSON parsing failure).


def test_unfinished_prompt_llm_returns_string_should_raise_typeerror(
    mock_load_prompt_template_success
):
    """Test that when llm_invoke returns a string instead of PromptAnalysis,
    unfinished_prompt raises a clear TypeError (not AttributeError).

    This test will FAIL until the fix is implemented (TDD red phase).

    Current buggy behavior: raises AttributeError "'str' object has no attribute 'reasoning'"
    Expected behavior after fix: raises TypeError with descriptive message like
    "Expected PromptAnalysis, got str"
    """
    with patch('pdd.unfinished_prompt.llm_invoke') as mock_invoke:
        # Simulate the bug: llm_invoke returns a string instead of PromptAnalysis
        # This happens when JSON parsing fails in the Responses API path
        malformed_json_string = '{"reasoning":"incomplete" "is_finished": false}'
        mock_invoke.return_value = {
            'result': malformed_json_string,  # String instead of PromptAnalysis!
            'cost': 0.001,
            'model_name': 'gpt-5-nano'
        }

        # EXPECTED BEHAVIOR AFTER FIX:
        # Should raise TypeError with a clear message, NOT AttributeError
        with pytest.raises(TypeError) as exc_info:
            unfinished_prompt(
                prompt_text="Write a function that",
                strength=0.5,
                temperature=0.5,
                verbose=False
            )

        # The error message should clearly indicate the type mismatch
        error_message = str(exc_info.value)
        assert 'PromptAnalysis' in error_message or 'expected' in error_message.lower(), \
            f"TypeError should have descriptive message about expected type. Got: {error_message}"


def test_unfinished_prompt_llm_returns_none_result(
    mock_load_prompt_template_success
):
    """Test that when llm_invoke returns None as result, it's handled gracefully."""
    with patch('pdd.unfinished_prompt.llm_invoke') as mock_invoke:
        mock_invoke.return_value = {
            'result': None,
            'cost': 0.001,
            'model_name': 'gpt-5-nano'
        }

        with pytest.raises((AttributeError, TypeError, Exception)) as exc_info:
            unfinished_prompt(
                prompt_text="Write a function that",
                strength=0.5,
                temperature=0.5,
                verbose=False
            )

        # Should raise some kind of error, not silently fail
        assert exc_info.value is not None


# --- TDD tests for fence stripping and indented code handling ---


def test_fence_stripped_before_syntactic_check(
    mock_load_prompt_template_success,
    mock_llm_invoke_success,
):
    """Code fence should be stripped; indented return inside fence should be
    caught by the syntactic check, not the LLM."""
    sample = "    return a + b\n```\n"
    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        language="python",
        verbose=False,
    )
    assert is_finished is True, f"Expected finished, got {is_finished}. Reason: {reasoning}"
    assert model == "syntactic_check", (
        f"Should be caught by ast.parse syntactic check, not LLM. Got model: {model}"
    )


def test_indented_python_tail_without_fence_is_finished(
    mock_load_prompt_template_success,
    mock_llm_invoke_success,
):
    """An indented return statement (function body fragment) should parse as
    finished via the syntactic check."""
    sample = "    return a + b\n"
    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        language="python",
        verbose=False,
    )
    assert is_finished is True, f"Expected finished, got {is_finished}. Reason: {reasoning}"
    assert model == "syntactic_check", (
        f"Should be caught by ast.parse syntactic check, not LLM. Got model: {model}"
    )


def test_fence_stripping_does_not_affect_incomplete_code(
    mock_load_prompt_template_success,
    mock_llm_invoke_success,
):
    """Incomplete code with a fence should still fall through to the LLM."""
    sample = "    for i in range(10):\n```\n"
    reasoning, is_finished, cost, model = unfinished_prompt(
        prompt_text=sample,
        strength=0.5,
        temperature=0.0,
        time=0.0,
        language="python",
        verbose=False,
    )
    # ast.parse should fail (missing loop body even when wrapped), falls through to LLM
    assert model != "syntactic_check", (
        f"Incomplete code should NOT be caught by syntactic check. Got model: {model}"
    )
