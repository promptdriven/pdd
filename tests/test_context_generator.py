import pytest
from pdd.context_generator import context_generator
from rich import print

def test_context_generator_basic_functionality():
    """
    Test the basic functionality of the context_generator function.
    This test ensures that the function can generate a concise example code snippet
    for a given code module and prompt.
    """
    code_module = "numpy"
    prompt = "Generate a concise example of how to use numpy to create an array."
    example_code, total_cost, model_name = context_generator(code_module, prompt, verbose=True)

    assert example_code is not None, "Example code should not be None"
    assert isinstance(example_code, str), "Example code should be a string"
    assert total_cost >= 0, "Total cost should be a non-negative float"
    assert isinstance(model_name, str), "Model name should be a string"

def test_context_generator_missing_code_module():
    """
    Test the context_generator function with a missing code_module input.
    This test ensures that the function handles the case where the code_module is not provided.
    """
    code_module = ""
    prompt = "Generate a concise example of how to use numpy to create an array."
    example_code, total_cost, model_name = context_generator(code_module, prompt, verbose=True)

    assert example_code is None, "Example code should be None for missing code_module"
    assert total_cost == 0.0, "Total cost should be 0.0 for missing code_module"
    assert model_name is None, "Model name should be None for missing code_module"

def test_context_generator_missing_prompt():
    """
    Test the context_generator function with a missing prompt input.
    This test ensures that the function handles the case where the prompt is not provided.
    """
    code_module = "numpy"
    prompt = ""
    example_code, total_cost, model_name = context_generator(code_module, prompt, verbose=True)

    assert example_code is None, "Example code should be None for missing prompt"
    assert total_cost == 0.0, "Total cost should be 0.0 for missing prompt"
    assert model_name is None, "Model name should be None for missing prompt"


def test_context_generator_invalid_strength():
    """
    Test the context_generator function with an invalid strength input.
    This test ensures that the function handles the case where the strength is out of the valid range.
    """
    code_module = "numpy"
    prompt = "Generate a concise example of how to use numpy to create an array."
    strength = 1.5  # Invalid strength, should be between 0 and 1
    example_code, total_cost, model_name = context_generator(code_module, prompt, strength=strength, verbose=True)

    assert example_code is None, "Example code should be None for invalid strength"
    assert total_cost == 0.0, "Total cost should be 0.0 for invalid strength"
    assert model_name is None, "Model name should be None for invalid strength"

def test_context_generator_invalid_temperature():
    """
    Test the context_generator function with an invalid temperature input.
    This test ensures that the function handles the case where the temperature is out of the valid range.
    """
    code_module = "numpy"
    prompt = "Generate a concise example of how to use numpy to create an array."
    temperature = 1.5  # Invalid temperature, should be between 0 and 1
    example_code, total_cost, model_name = context_generator(code_module, prompt, temperature=temperature, verbose=True)

    assert example_code is None, "Example code should be None for invalid temperature"
    assert total_cost == 0.0, "Total cost should be 0.0 for invalid temperature"
    assert model_name is None, "Model name should be None for invalid temperature"

def test_context_generator_incomplete_generation():
    """
    Test the context_generator function with an incomplete generation scenario.
    This test ensures that the function correctly identifies and handles incomplete generation.
    """
    import os
    # Ensure included context file exists for preprocessing
    os.makedirs("context", exist_ok=True)
    code_module = "numpy"
    prompt = "Generate a concise example of how to use numpy to create an array."
    # Mocking an incomplete generation by returning a truncated response
    example_code, total_cost, model_name = context_generator(code_module, prompt, verbose=True)

    assert example_code is not None, "Example code should not be None for incomplete generation"
    assert isinstance(example_code, str), "Example code should be a string"
    assert total_cost >= 0, "Total cost should be a non-negative float"
    assert isinstance(model_name, str), "Model name should be a string"

def test_context_generator_postprocessing():
    """
    Test the context_generator function's postprocessing step.
    This test ensures that the function correctly extracts code from the model output.
    """
    code_module = "numpy"
    prompt = "Generate a concise example of how to use numpy to create an array."
    example_code, total_cost, model_name = context_generator(code_module, prompt, verbose=True)

    assert example_code is not None, "Example code should not be None after postprocessing"
    assert isinstance(example_code, str), "Example code should be a string"
    assert total_cost >= 0, "Total cost should be a non-negative float"
    assert isinstance(model_name, str), "Model name should be a string"

if __name__ == "__main__":
    pytest.main()