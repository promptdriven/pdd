import pytest
from unittest.mock import patch, mock_open
from context_generator import context_generator

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_content():
    return "Mock prompt content"

@pytest.fixture
def mock_llm_selector():
    return patch('context_generator.llm_selector', return_value=(None, 0.001, 0.002))

@pytest.fixture
def mock_preprocess():
    return patch('context_generator.preprocess', return_value="Processed prompt")

@pytest.fixture
def mock_postprocess():
    return patch('context_generator.postprocess', return_value=("Example code", 0.001))

@pytest.fixture
def mock_chain_invoke():
    return patch('langchain_core.prompts.PromptTemplate.from_template.return_value.__or__.return_value.__or__.return_value.invoke', return_value="Raw model output")

def test_context_generator_success(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain_invoke):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain_invoke:
            example_code, total_cost = context_generator("test_module", "test prompt")
    
    assert isinstance(example_code, str)
    assert isinstance(total_cost, float)
    assert example_code == "Example code"
    assert total_cost > 0

def test_context_generator_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        with pytest.raises(FileNotFoundError):
            context_generator("test_module", "test prompt")

def test_context_generator_environment_variable_not_set():
    with patch.dict('os.environ', clear=True):
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            context_generator("test_module", "test prompt")

def test_context_generator_model_invocation_error(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with mock_llm_selector, mock_preprocess:
            with patch('langchain_core.prompts.PromptTemplate.from_template.return_value.__or__.return_value.__or__.return_value.invoke', side_effect=Exception("Model error")):
                with pytest.raises(RuntimeError, match="Error during model invocation: Model error"):
                    context_generator("test_module", "test prompt")

def test_context_generator_custom_parameters(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain_invoke):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain_invoke:
            example_code, total_cost = context_generator("test_module", "test prompt", language="java", strength=0.7, temperature=0.5)
    
    assert isinstance(example_code, str)
    assert isinstance(total_cost, float)

@pytest.mark.parametrize("strength,temperature", [
    (0.1, 0),
    (0.9, 1),
    (0.5, 0.5),
])
def test_context_generator_different_model_params(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain_invoke, strength, temperature):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain_invoke:
            example_code, total_cost = context_generator("test_module", "test prompt", strength=strength, temperature=temperature)
    
    assert isinstance(example_code, str)
    assert isinstance(total_cost, float)