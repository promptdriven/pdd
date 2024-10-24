import pytest
import os
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from pdd.fix_code_module_errors import fix_code_module_errors

# Test data
MOCK_PROGRAM = "def main(): print('hello')"
MOCK_PROMPT = "Write a hello world program"
MOCK_CODE = "def helper(): return 'world'"
MOCK_ERRORS = "NameError: name 'helper' is not defined"
MOCK_STRENGTH = 0.5
MOCK_TEMPERATURE = 0.0

# Mock prompt content
MOCK_FIX_PROMPT = "Fix this: {program} {prompt} {code} {errors}"
MOCK_EXTRACT_PROMPT = "Extract fixes: {program_code_fix} {program} {code} {format_instructions}"

# Mock LLM response
MOCK_FIX_RESULT = "Here's the analysis of the errors..."
MOCK_EXTRACT_RESULT = {
    "update_program": True,
    "update_code": True,
    "fixed_program": "def main(): result = helper()\nprint(result)",
    "fixed_code": "def helper(): return 'world'"
}

@pytest.fixture
def setup_environment():
    """Setup test environment variables and mocks"""
    os.environ['PDD_PATH'] = '/mock/path'
    yield
    del os.environ['PDD_PATH']

@pytest.fixture
def mock_llm_selector():
    """Mock the llm_selector function"""
    with patch('pdd.fix_code_module_errors.llm_selector') as mock:
        mock.return_value = (
            MagicMock(),  # llm
            lambda x: 100,  # token_counter
            0.001,  # input_cost
            0.002,  # output_cost
            "gpt-3.5-turbo"  # model_name
        )
        yield mock

def test_successful_fix(setup_environment, mock_llm_selector):
    """Test successful execution of fix_code_module_errors"""
    
    # Mock file operations
    mock_files = {
        '/mock/path/prompts/fix_code_module_errors_LLM.prompt': MOCK_FIX_PROMPT,
        '/mock/path/prompts/extract_program_code_fix_LLM.prompt': MOCK_EXTRACT_PROMPT
    }
    
    with patch('builtins.open', mock_open()) as mock_file:
        mock_file.side_effect = lambda file, *args, **kwargs: mock_open(read_data=mock_files[str(file)]).return_value
        
        # Mock chain invocations
        with patch('langchain_core.output_parsers.StrOutputParser') as mock_str_parser:
            mock_str_parser.return_value.invoke.return_value = MOCK_FIX_RESULT
            
            with patch('langchain_core.output_parsers.JsonOutputParser') as mock_json_parser:
                mock_json_parser.return_value.invoke.return_value = MOCK_EXTRACT_RESULT
                
                result = fix_code_module_errors(
                    MOCK_PROGRAM,
                    MOCK_PROMPT,
                    MOCK_CODE,
                    MOCK_ERRORS,
                    MOCK_STRENGTH,
                    MOCK_TEMPERATURE
                )
                
                assert isinstance(result, tuple)
                assert len(result) == 6
                update_program, update_code, fixed_program, fixed_code, total_cost, model_name = result
                
                assert update_program is True
                assert update_code is True
                assert fixed_program == MOCK_EXTRACT_RESULT["fixed_program"]
                assert fixed_code == MOCK_EXTRACT_RESULT["fixed_code"]
                assert isinstance(total_cost, float)
                assert model_name == "gpt-3.5-turbo"

def test_missing_pdd_path():
    """Test handling of missing PDD_PATH environment variable"""
    if 'PDD_PATH' in os.environ:
        del os.environ['PDD_PATH']
        
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            MOCK_PROGRAM,
            MOCK_PROMPT,
            MOCK_CODE,
            MOCK_ERRORS,
            MOCK_STRENGTH,
            MOCK_TEMPERATURE  # Corrected missing argument
        )
    assert str(exc_info.value) == "PDD_PATH environment variable not set"

def test_file_not_found(setup_environment):
    """Test handling of missing prompt files"""
    with pytest.raises(FileNotFoundError):
        fix_code_module_errors(
            MOCK_PROGRAM,
            MOCK_PROMPT,
            MOCK_CODE,
            MOCK_ERRORS,
            MOCK_STRENGTH
        )

def test_invalid_strength_value(setup_environment, mock_llm_selector):
    """Test handling of invalid strength value"""
    invalid_strength = 1.5
    
    with patch('builtins.open', mock_open(read_data="mock prompt")):
        with pytest.raises(ValueError):
            fix_code_module_errors(
                MOCK_PROGRAM,
                MOCK_PROMPT,
                MOCK_CODE,
                MOCK_ERRORS,
                invalid_strength
            )

def test_empty_inputs(setup_environment, mock_llm_selector):
    """Test handling of empty input strings"""
    with patch('builtins.open', mock_open(read_data="mock prompt")):
        with patch('langchain_core.output_parsers.StrOutputParser') as mock_str_parser:
            mock_str_parser.return_value.invoke.return_value = MOCK_FIX_RESULT
            
            with patch('langchain_core.output_parsers.JsonOutputParser') as mock_json_parser:
                mock_json_parser.return_value.invoke.return_value = MOCK_EXTRACT_RESULT
                
                result = fix_code_module_errors(
                    "",  # empty program
                    "",  # empty prompt
                    "",  # empty code
                    "",  # empty errors
                    MOCK_STRENGTH,
                    MOCK_TEMPERATURE
                )
                
                assert isinstance(result, tuple)
                assert len(result) == 6
