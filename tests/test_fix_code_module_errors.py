import pytest
from unittest.mock import patch, mock_open
from pathlib import Path
from pdd.fix_code_module_errors import fix_code_module_errors

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_llm_selector():
    with patch('pdd.fix_code_module_errors.llm_selector') as mock:
        mock.return_value = (
            lambda x: "Fixed code",  # mock LLM
            lambda x: len(x),        # mock token counter
            0.01,                    # mock input cost
            0.02,                    # mock output cost
            "MockGPT-3.5"            # mock model name
        )
        yield mock

@pytest.fixture
def mock_postprocess():
    with patch('pdd.fix_code_module_errors.postprocess') as mock:
        mock.return_value = ("Fixed code", 0.001)
        yield mock

def test_fix_code_module_errors_success(mock_environment, mock_llm_selector, mock_postprocess):
    mock_prompt = "Mock prompt content"
    with patch("builtins.open", mock_open(read_data=mock_prompt)):
        fixed_code, total_cost, model_name = fix_code_module_errors(
            program="print('Hello')",
            prompt="Write a hello world program",
            code="print('Hello')",
            errors="NameError: name 'Hello' is not defined",
            strength=0.7
        )
    
    assert fixed_code == "Fixed code"
    assert isinstance(total_cost, float)
    assert model_name == "MockGPT-3.5"

def test_fix_code_module_errors_file_not_found(mock_environment):
    with patch("builtins.open", side_effect=FileNotFoundError()):
        with pytest.raises(FileNotFoundError):
            fix_code_module_errors(
                program="print('Hello')",
                prompt="Write a hello world program",
                code="print('Hello')",
                errors="NameError: name 'Hello' is not defined",
                strength=0.7
            )

def test_fix_code_module_errors_missing_env_var():
    with patch.dict('os.environ', clear=True):
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            fix_code_module_errors(
                program="print('Hello')",
                prompt="Write a hello world program",
                code="print('Hello')",
                errors="NameError: name 'Hello' is not defined",
                strength=0.7
            )

def test_fix_code_module_errors_unexpected_error(mock_environment, mock_llm_selector):
    with patch("builtins.open", mock_open(read_data="Mock prompt")):
        with patch('pdd.fix_code_module_errors.PromptTemplate', side_effect=Exception("Unexpected error")):
            with pytest.raises(Exception, match="Unexpected error"):
                fix_code_module_errors(
                    program="print('Hello')",
                    prompt="Write a hello world program",
                    code="print('Hello')",
                    errors="NameError: name 'Hello' is not defined",
                    strength=0.7
                )

def test_fix_code_module_errors_strength_range():
    with pytest.raises(ValueError):
        fix_code_module_errors(
            program="print('Hello')",
            prompt="Write a hello world program",
            code="print('Hello')",
            errors="NameError: name 'Hello' is not defined",
            strength=1.5
        )

    with pytest.raises(ValueError):
        fix_code_module_errors(
            program="print('Hello')",
            prompt="Write a hello world program",
            code="print('Hello')",
            errors="NameError: name 'Hello' is not defined",
            strength=-0.5
        )