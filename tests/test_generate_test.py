import pytest
import os
from unittest.mock import patch, mock_open
from pdd.generate_test import generate_test
from rich.console import Console
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser

class MockPromptTemplate:
    def __init__(self, template):
        self.template = template

    def __or__(self, other):
        return self

    def invoke(self, *args, **kwargs):
        return self.template

@pytest.fixture
def mock_environment():
    with patch.dict(os.environ, {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_content():
    return "Mock prompt content"

@pytest.fixture
def mock_llm_selector():
    return (
        lambda *args: (
            lambda x: "Generated test content",
            lambda x: 100,
            0.001,
            0.002,
            "mock_model"
        )
    )

@pytest.fixture
def mock_preprocess():
    return lambda *args, **kwargs: "Preprocessed prompt"

@pytest.fixture
def mock_unfinished_prompt():
    return lambda *args: (None, True, 0.001, None)

@pytest.fixture
def mock_postprocess():
    return lambda *args: ("Postprocessed result", 0.001)

def test_generate_test_success(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_unfinished_prompt, mock_postprocess):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('pdd.generate_test.llm_selector', mock_llm_selector):
            with patch('pdd.generate_test.preprocess', mock_preprocess):
                with patch('pdd.generate_test.unfinished_prompt', mock_unfinished_prompt):
                    with patch('pdd.generate_test.postprocess', mock_postprocess):
                        with patch('pdd.generate_test.PromptTemplate.from_template') as mock_prompt_template:
                            mock_prompt_template.return_value = MockPromptTemplate("Mock template")
                            
                            result, cost, model = generate_test("Test prompt", "Test code", 0.5, 0.7, "python")
                            
                            assert isinstance(result, str)
                            assert result == "Postprocessed result"
                            assert isinstance(cost, float)
                            assert model == "mock_model"

def test_generate_test_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        with pytest.raises(FileNotFoundError):
            generate_test("Test prompt", "Test code", 0.5, 0.7, "python")

def test_generate_test_value_error():
    with patch.dict(os.environ, clear=True):
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            generate_test("Test prompt", "Test code", 0.5, 0.7, "python")

def test_generate_test_unexpected_error(mock_environment, mock_file_content):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('pdd.generate_test.llm_selector', side_effect=Exception("Unexpected error")):
            with pytest.raises(Exception, match="Unexpected error"):
                generate_test("Test prompt", "Test code", 0.5, 0.7, "python")

def test_generate_test_incomplete_generation(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('pdd.generate_test.llm_selector', mock_llm_selector):
            with patch('pdd.generate_test.preprocess', mock_preprocess):
                with patch('pdd.generate_test.unfinished_prompt', return_value=(None, False, 0.001, None)):
                    with patch('pdd.generate_test.continue_generation', return_value=("Continued result", 0.002, None)):
                        with patch('pdd.generate_test.PromptTemplate.from_template') as mock_prompt_template:
                            mock_prompt_template.return_value = MockPromptTemplate("Mock template")
                            
                            result, cost, model = generate_test("Test prompt", "Test code", 0.5, 0.7, "python")
                            
                            assert isinstance(result, str)
                            assert result == "Continued result"
                            assert isinstance(cost, float)
                            assert model == "mock_model"

def test_generate_test_input_validation():
    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        generate_test("Test prompt", "Test code", 1.5, 0.7, "python")
    with pytest.raises(ValueError, match="Temperature must be between 0 and 1"):
        generate_test("Test prompt", "Test code", 0.5, 1.5, "python")
    with pytest.raises(ValueError, match="Language cannot be empty"):
        generate_test("Test prompt", "Test code", 0.5, 0.7, "")