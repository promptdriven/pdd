import pytest
from unittest.mock import patch
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


def test_context_generator_with_file_paths():
    """Test that context_generator accepts and uses file path parameters."""
    mock_code = "def hello():\n    print('hello')"
    mock_prompt = "Write a hello function"
    
    with patch('pdd.context_generator.load_prompt_template') as mock_load, \
         patch('pdd.context_generator.preprocess') as mock_preprocess, \
         patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
         patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
         patch('pdd.context_generator.continue_generation') as mock_continue, \
         patch('pdd.context_generator.postprocess') as mock_postprocess:
        
        # Mock the prompt template
        mock_load.return_value = """
        % File path information:
        % - The source module file is located at: <source_file_path>{source_file_path}</source_file_path>
        % - The example file will be saved at: <example_file_path>{example_file_path}</example_file_path>
        % - The module name (without extension) is: <module_name>{module_name}</module_name>
        % - IMPORT INSTRUCTIONS: Import directly from the module name, e.g., "from {module_name} import function_name"
        """
        
        # Mock preprocessing
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        # Mock LLM response
        mock_llm_invoke.return_value = {
            'result': 'from hello import hello\n\nhello()',
            'cost': 0.01,
            'model_name': 'test-model'
        }
        
        # Mock unfinished prompt detection
        mock_unfinished.return_value = (None, True, 0.0, None)
        
        # Mock postprocessing
        mock_postprocess.return_value = ('from hello import hello\n\nhello()', 0.0, 'test-model')
        
        # Call with file path parameters
        result = context_generator(
            code_module=mock_code,
            prompt=mock_prompt,
            language="python",
            source_file_path="/path/to/source/hello.py",
            example_file_path="/path/to/examples/hello_example.py",
            module_name="hello"
        )
        
        # Verify the result
        assert result is not None, "Context generator should return a result"
        assert len(result) == 3, "Result should contain (code, cost, model_name)"
        
        # Verify that the prompt template was called with file path parameters
        mock_llm_invoke.assert_called_once()
        call_args = mock_llm_invoke.call_args[1]['input_json']
        assert 'source_file_path' in call_args, "source_file_path should be passed to LLM"
        assert 'example_file_path' in call_args, "example_file_path should be passed to LLM"
        assert 'module_name' in call_args, "module_name should be passed to LLM"
        assert call_args['source_file_path'] == "/path/to/source/hello.py"
        assert call_args['example_file_path'] == "/path/to/examples/hello_example.py"
        assert call_args['module_name'] == "hello"


def test_context_generator_prompt_template_includes_import_instructions():
    """Test that the prompt template includes import instructions for correct import generation."""
    mock_code = "def hello():\n    print('hello')"
    mock_prompt = "Write a hello function"
    
    with patch('pdd.context_generator.load_prompt_template') as mock_load, \
         patch('pdd.context_generator.preprocess') as mock_preprocess, \
         patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
         patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
         patch('pdd.context_generator.continue_generation') as mock_continue, \
         patch('pdd.context_generator.postprocess') as mock_postprocess:
        
        # Mock the enhanced prompt template
        mock_load.return_value = """
        % IMPORT INSTRUCTIONS: Use the appropriate import mechanism for the target language
        %   - For Python: Use direct imports from the module name
        %   - For JavaScript: Use require() or ES6 import syntax with relative paths
        %   - For C++: Use appropriate header inclusion
        %   - For Java: Use proper import statements
        %   - For other languages: Use the standard import/inclusion mechanism
        %   - Avoid package-style imports unless the file is actually in a package structure
        %   - Import the specific functions/classes that are defined in the code module
        """
        
        # Mock other functions
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_llm_invoke.return_value = {'result': 'from hello import hello', 'cost': 0.01, 'model_name': 'test-model'}
        mock_unfinished.return_value = (None, True, 0.0, None)
        mock_postprocess.return_value = ('from hello import hello', 0.0, 'test-model')
        
        # Call context generator
        context_generator(mock_code, mock_prompt, language="python")
        
        # Verify that the prompt template was loaded
        mock_load.assert_called_once()
        
        # Verify that the template contains import instructions
        template_content = mock_load.return_value
        assert "IMPORT INSTRUCTIONS" in template_content, "Template should contain import instructions"
        assert "Python" in template_content, "Template should contain Python-specific instructions"
        assert "JavaScript" in template_content, "Template should contain JavaScript-specific instructions"


if __name__ == "__main__":
    pytest.main()