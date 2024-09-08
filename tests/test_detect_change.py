import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.detect_change import detect_change, custom_chain_executor
import json
from rich.console import Console

class MockPromptTemplate:
    def __init__(self, template):
        self.template = template

    def invoke(self, kwargs):
        return self.template.format(**kwargs)

class MockLLM:
    def __init__(self, output):
        self.output = output

    def invoke(self, prompt):
        return self.output

class MockOutputParser:
    def __init__(self, output):
        self.output = output

    def invoke(self, text):
        return self.output

@pytest.fixture
def mock_environment():
    """Mock the environment variable for PDD_PATH."""
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_contents():
    """Provide mock file contents for testing."""
    detect_change_prompt = "Mock detect_change_LLM prompt"
    extract_detect_change_prompt = "Mock extract_detect_change_LLM prompt"
    prompt_file_content = "Mock prompt file content"
    return detect_change_prompt, extract_detect_change_prompt, prompt_file_content

@pytest.fixture
def mock_llm_selector():
    """Mock the LLM selector function."""
    return (
        lambda x, y: (
            MockLLM("Mock LLM output"),
            lambda x: 100,
            0.00002,
            0.00002,
            "mock_model"
        )
    )

@pytest.fixture
def mock_preprocess():
    """Mock the preprocess function."""
    return lambda x, **kwargs: x

def test_detect_change_success(mock_environment, mock_file_contents, mock_llm_selector, mock_preprocess):
    """Test successful execution of detect_change function."""
    detect_change_prompt, extract_detect_change_prompt, prompt_file_content = mock_file_contents
    
    with patch('builtins.open', mock_open(read_data=prompt_file_content)):
        with patch('pdd.detect_change.llm_selector', mock_llm_selector):
            with patch('pdd.detect_change.preprocess', mock_preprocess):
                with patch('pdd.detect_change.PromptTemplate.from_template') as mock_prompt_template:
                    mock_prompt_template.return_value = MockPromptTemplate("Mock template output")
                    
                    with patch('pdd.detect_change.JsonOutputParser') as mock_json_parser:
                        mock_json_parser.return_value = MockOutputParser({"changes_list": [{"prompt_name": "test.prompt", "change_instructions": "Test instructions"}]})
                        
                        with patch('pdd.detect_change.custom_chain_executor', side_effect=[
                            "Mock LLM output",
                            {"changes_list": [{"prompt_name": "test.prompt", "change_instructions": "Test instructions"}]}
                        ]):
                            result, total_cost, model_name = detect_change(
                                prompt_files=["test.prompt"],
                                change_description="Test change",
                                strength=0.5,
                                temperature=0.7
                            )
    
    assert isinstance(result, list)
    assert len(result) == 1
    assert result[0]["prompt_name"] == "test.prompt"
    assert result[0]["change_instructions"] == "Test instructions"
    assert isinstance(total_cost, float)
    assert model_name == "mock_model"

def test_detect_change_file_not_found(mock_environment):
    """Test detect_change function when file is not found."""
    with patch('builtins.open', side_effect=FileNotFoundError):
        result, total_cost, model_name = detect_change(
            prompt_files=["nonexistent.prompt"],
            change_description="Test change",
            strength=0.5,
            temperature=0.7
        )
    
    assert result == []
    assert total_cost == 0.0
    assert model_name == ""

def test_detect_change_json_decode_error(mock_environment, mock_file_contents, mock_llm_selector, mock_preprocess):
    """Test detect_change function when JSON decode error occurs."""
    detect_change_prompt, extract_detect_change_prompt, prompt_file_content = mock_file_contents
    
    with patch('builtins.open', mock_open(read_data=prompt_file_content)):
        with patch('pdd.detect_change.llm_selector', mock_llm_selector):
            with patch('pdd.detect_change.preprocess', mock_preprocess):
                with patch('pdd.detect_change.PromptTemplate.from_template') as mock_prompt_template:
                    mock_prompt_template.return_value = MockPromptTemplate("Mock template output")
                    
                    with patch('pdd.detect_change.JsonOutputParser') as mock_json_parser:
                        mock_json_parser.return_value = MockOutputParser(json.JSONDecodeError("Test error", "", 0))
                        
                        with patch('pdd.detect_change.custom_chain_executor', side_effect=[
                            "Mock LLM output",
                            json.JSONDecodeError("Test error", "", 0)
                        ]):
                            result, total_cost, model_name = detect_change(
                                prompt_files=["test.prompt"],
                                change_description="Test change",
                                strength=0.5,
                                temperature=0.7
                            )
    
    assert result == []
    assert total_cost == 0.0
    assert model_name == ""

def test_detect_change_unexpected_error(mock_environment, mock_file_contents, mock_llm_selector, mock_preprocess):
    """Test detect_change function when an unexpected error occurs."""
    detect_change_prompt, extract_detect_change_prompt, prompt_file_content = mock_file_contents
    
    with patch('builtins.open', mock_open(read_data=prompt_file_content)):
        with patch('pdd.detect_change.llm_selector', mock_llm_selector):
            with patch('pdd.detect_change.preprocess', mock_preprocess):
                with patch('pdd.detect_change.PromptTemplate.from_template', side_effect=Exception("Unexpected error")):
                    result, total_cost, model_name = detect_change(
                        prompt_files=["test.prompt"],
                        change_description="Test change",
                        strength=0.5,
                        temperature=0.7
                    )
    
    assert result == []
    assert total_cost == 0.0
    assert model_name == ""
