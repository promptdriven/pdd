import os
import pytest
from unittest.mock import patch, MagicMock
from typing import List

# Import the function to be tested
from pdd.auto_include import auto_include

@pytest.fixture
def mock_environment():
    """Fixture to set up and tear down environment variables."""
    with patch.dict(os.environ, {"PDD_PATH": "/fake/path"}, clear=True):
        yield

@pytest.fixture
def mock_load_prompt_template():
    """Fixture to mock the load_prompt_template function."""
    with patch("pdd.auto_include.load_prompt_template") as mock_load:
        mock_load.side_effect = lambda filename: f"Template content for {filename}"
        yield mock_load

@pytest.fixture
def mock_llm_selector():
    """Fixture to mock the llm_selector function."""
    with patch("pdd.auto_include.llm_selector") as mock_selector:
        # Mocking llm_selector to return a mock LLM and other parameters
        mock_llm = MagicMock()
        mock_llm.invoke.return_value = "LLM output"
        token_counter = MagicMock(side_effect=lambda x: len(x))
        input_cost = 0.05
        output_cost = 0.07
        model_name = "mock-model"
        mock_selector.return_value = (mock_llm, token_counter, input_cost, output_cost, model_name)
        yield mock_selector

@pytest.fixture
def mock_console_print():
    """Fixture to mock the console.print function."""
    with patch("pdd.auto_include.console.print") as mock_print:
        yield mock_print

def test_auto_include_success(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with valid inputs.
    """
    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = 0.7

    output_prompt, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        available_includes=available_includes,
        strength=strength,
        temperature=temperature
    )

    # Assertions
    assert isinstance(output_prompt, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert model_name == "mock-model"
    expected_total_cost = (
        (len(f"Template content for auto_include_LLM.prompt") / 1_000_000) * 0.05 +
        (len("LLM output") / 1_000_000) * 0.07 +
        (len(f"Template content for extract_auto_include_LLM.prompt") / 1_000_000) * 0.05 +
        (len("LLM output") / 1_000_000) * 0.07
    )
    assert total_cost == expected_total_cost
    assert output_prompt == f"LLM output\n{input_prompt}"

def test_missing_pdd_path():
    """
    Test the auto_include function when PDD_PATH environment variable is missing.
    """
    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = 0.7

    with patch.dict(os.environ, {}, clear=True):
        with pytest.raises(ValueError, match="PDD_PATH environment variable not set"):
            auto_include(
                input_prompt=input_prompt,
                available_includes=available_includes,
                strength=strength,
                temperature=temperature
            )

def test_load_prompt_file_not_found(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function when prompt files are missing.
    """
    # Configure the mock to raise FileNotFoundError for missing prompt files
    mock_load_prompt_template.side_effect = FileNotFoundError("Prompt file not found: /fake/path/prompts/missing.prompt")

    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = 0.7

    with pytest.raises(FileNotFoundError, match="Prompt file not found: .*missing.prompt"):
        auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=strength,
            temperature=temperature
        )

def test_invalid_strength(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with invalid strength values.
    """
    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 1.5  # Invalid strength
    temperature = 0.7

    # Assuming llm_selector raises a ValueError for invalid strength
    mock_llm_selector.side_effect = ValueError("Strength must be between 0 and 1")

    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=strength,
            temperature=temperature
        )

def test_empty_available_includes(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with an empty available_includes list.
    """
    input_prompt = "This is a test prompt."
    available_includes: List[str] = []
    strength = 0.5
    temperature = 0.7

    output_prompt, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        available_includes=available_includes,
        strength=strength,
        temperature=temperature
    )

    # Assertions
    assert isinstance(output_prompt, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert model_name == "mock-model"
    assert output_prompt == f"LLM output\n{input_prompt}"

def test_empty_input_prompt(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with an empty input_prompt.
    """
    input_prompt = ""
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = 0.7

    output_prompt, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        available_includes=available_includes,
        strength=strength,
        temperature=temperature
    )

    # Assertions
    assert isinstance(output_prompt, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert model_name == "mock-model"
    assert output_prompt == f"LLM output\n"

def test_llm_selector_exception(mock_environment, mock_load_prompt_template):
    """
    Test the auto_include function when llm_selector raises an exception.
    """
    with patch("pdd.auto_include.llm_selector") as mock_selector:
        mock_selector.side_effect = Exception("LLM selector failure")

        input_prompt = "This is a test prompt."
        available_includes = ["include1.py", "include2.py"]
        strength = 0.5
        temperature = 0.7

        with patch("pdd.auto_include.console.print") as mock_print:
            with pytest.raises(Exception, match="LLM selector failure"):
                auto_include(
                    input_prompt=input_prompt,
                    available_includes=available_includes,
                    strength=strength,
                    temperature=temperature
                )
            mock_print.assert_called_with("[bold red]Error in auto_include:[/] LLM selector failure")

def test_invalid_temperature(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with invalid temperature values.
    """
    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = -0.1  # Invalid temperature

    # Assuming llm_selector raises a ValueError for invalid temperature
    with patch("pdd.auto_include.llm_selector") as mock_selector:
        mock_selector.side_effect = ValueError("Temperature must be non-negative")

        with pytest.raises(ValueError, match="Temperature must be non-negative"):
            auto_include(
                input_prompt=input_prompt,
                available_includes=available_includes,
                strength=strength,
                temperature=temperature
            )

def test_parse_extracted_includes_failure(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function when parsing extracted includes fails.
    """
    # Mock the first LLM invoke to return invalid JSON
    mock_llm = mock_llm_selector.return_value[0]
    mock_llm.invoke.return_value = "Invalid JSON"

    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = 0.7

    with pytest.raises(Exception, match="JSON parse error"):
        auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=strength,
            temperature=temperature
        )

def test_total_cost_calculation(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function to ensure total_cost is calculated correctly.
    """
    input_prompt = "Test prompt for total cost calculation."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.8
    temperature = 0.6

    # Configure the token_counter to return specific numbers
    with patch.object(mock_llm_selector.return_value[1], '__call__', side_effect=lambda x: 1000):
        output_prompt, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=strength,
            temperature=temperature
        )
    
    # Expected total cost:
    # (1000 / 1_000_000) * 0.05 + (1000 / 1_000_000) * 0.07 +
    # (1000 / 1_000_000) * 0.05 + (1000 / 1_000_000) * 0.07
    expected_total_cost = (1000 / 1_000_000) * (0.05 + 0.07 + 0.05 + 0.07)
    assert total_cost == pytest.approx(expected_total_cost)

def test_missing_string_of_includes(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function when 'string_of_includes' key is missing in extracted_result.
    """
    # Mock the extraction to return a dict without 'string_of_includes'
    mock_llm = mock_llm_selector.return_value[0]
    mock_llm.invoke.return_value = '{"unexpected_key": "value"}'

    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", "include2.py"]
    strength = 0.5
    temperature = 0.7

    with pytest.raises(KeyError, match="'string_of_includes'"):
        auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=strength,
            temperature=temperature
        )

def test_non_string_available_includes(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with non-string items in available_includes list.
    """
    input_prompt = "This is a test prompt."
    available_includes = ["include1.py", 123, None]  # Invalid items
    strength = 0.5
    temperature = 0.7

    # Assuming the function handles non-string includes by converting them to strings
    output_prompt, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        available_includes=available_includes,
        strength=strength,
        temperature=temperature
    )

    # Assertions
    assert output_prompt == f"LLM output\n{input_prompt}"

def test_large_input_prompt(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with a large input_prompt.
    """
    input_prompt = "A" * 10_000  # Large input
    available_includes = ["include1.py", "include2.py"]
    strength = 0.9
    temperature = 0.8

    output_prompt, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        available_includes=available_includes,
        strength=strength,
        temperature=temperature
    )

    # Assertions
    assert isinstance(output_prompt, str)
    assert len(output_prompt) == len("LLM output\n") + len(input_prompt)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)

def test_special_characters_in_input_prompt(mock_environment, mock_load_prompt_template, mock_llm_selector, mock_console_print):
    """
    Test the auto_include function with special characters in input_prompt.
    """
    input_prompt = "!@#$%^&*()_+-=[]{}|;':\",.<>/?`~"
    available_includes = ["include1.py", "include2.py"]
    strength = 0.3
    temperature = 0.4

    output_prompt, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        available_includes=available_includes,
        strength=strength,
        temperature=temperature
    )

    # Assertions
    assert output_prompt == f"LLM output\n{input_prompt}"
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
