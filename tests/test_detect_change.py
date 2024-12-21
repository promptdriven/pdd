import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from pdd.detect_change import detect_change, ChangesList, ChangeInstruction

# Test data
MOCK_PROMPT_FILES = ["test1.prompt", "test2.prompt"]
MOCK_CHANGE_DESCRIPTION = "Update error handling in prompts"
MOCK_PROMPT_CONTENT = "This is a test prompt content"

@pytest.fixture
def mock_llm_responses():
    """Fixture to provide mock LLM responses."""
    detect_response = {
        'result': 'Analysis results',
        'cost': 0.05,
        'token_count': 100,
        'model_name': 'gpt-3.5-turbo'
    }
    
    changes_list = ChangesList(changes_list=[
        ChangeInstruction(
            prompt_name="test1.prompt",
            change_instructions="Add better error handling"
        )
    ])
    
    extract_response = {
        'result': changes_list,
        'cost': 0.03,
        'token_count': 50,
        'model_name': 'gpt-3.5-turbo'
    }
    
    return detect_response, extract_response

@pytest.fixture
def mock_templates():
    """Fixture to provide mock templates."""
    return "Mock detect template", "Mock extract template"

def test_successful_detection(mock_llm_responses, mock_templates):
    """Test successful detection of changes."""
    detect_response, extract_response = mock_llm_responses
    
    with patch('pdd.detect_change.load_prompt_template') as mock_load_template, \
         patch('pdd.detect_change.preprocess') as mock_preprocess, \
         patch('pdd.detect_change.llm_invoke') as mock_llm_invoke, \
         patch('builtins.open', mock_open(read_data=MOCK_PROMPT_CONTENT)):
        
        # Configure mocks
        mock_load_template.side_effect = mock_templates
        mock_preprocess.return_value = "Processed template"
        mock_llm_invoke.side_effect = [detect_response, extract_response]
        
        # Execute function
        changes_list, total_cost, model_name = detect_change(
            MOCK_PROMPT_FILES,
            MOCK_CHANGE_DESCRIPTION,
            strength=0.7,
            temperature=0.0,
            verbose=False
        )
        
        # Verify results
        assert len(changes_list) == 1
        assert changes_list[0]["prompt_name"] == "test1.prompt"
        assert changes_list[0]["change_instructions"] == "Add better error handling"
        assert total_cost == 0.08  # 0.05 + 0.03
        assert model_name == "gpt-3.5-turbo"

def test_missing_prompt_template():
    """Test handling of missing prompt template."""
    with patch('pdd.detect_change.load_prompt_template', return_value=None):
        with pytest.raises(ValueError, match="Failed to load detect_change_LLM prompt template"):
            detect_change(
                MOCK_PROMPT_FILES,
                MOCK_CHANGE_DESCRIPTION,
                strength=0.7,
                temperature=0.0
            )

def test_missing_prompt_files(mock_llm_responses, mock_templates):
    """Test handling of missing prompt files."""
    detect_response, extract_response = mock_llm_responses
    
    with patch('pdd.detect_change.load_prompt_template') as mock_load_template, \
         patch('pdd.detect_change.preprocess') as mock_preprocess, \
         patch('pdd.detect_change.llm_invoke') as mock_llm_invoke, \
         patch('builtins.open') as mock_file:
        
        # Configure mocks
        mock_load_template.side_effect = mock_templates
        mock_preprocess.return_value = "Processed template"
        mock_llm_invoke.side_effect = [detect_response, extract_response]
        mock_file.side_effect = FileNotFoundError()
        
        # Execute function with non-existent files
        changes_list, total_cost, model_name = detect_change(
            ["nonexistent.prompt"],
            MOCK_CHANGE_DESCRIPTION,
            strength=0.7,
            temperature=0.0,
            verbose=True
        )
        
        # Verify empty results due to missing files
        assert len(changes_list) == 1  # Still returns the mocked response
        assert total_cost == 0.08

def test_verbose_output(mock_llm_responses, mock_templates, capsys):
    """Test verbose output functionality."""
    detect_response, extract_response = mock_llm_responses
    
    with patch('pdd.detect_change.load_prompt_template') as mock_load_template, \
         patch('pdd.detect_change.preprocess') as mock_preprocess, \
         patch('pdd.detect_change.llm_invoke') as mock_llm_invoke, \
         patch('builtins.open', mock_open(read_data=MOCK_PROMPT_CONTENT)):
        
        # Configure mocks
        mock_load_template.side_effect = mock_templates
        mock_preprocess.return_value = "Processed template"
        mock_llm_invoke.side_effect = [detect_response, extract_response]
        
        # Execute function with verbose=True
        detect_change(
            MOCK_PROMPT_FILES,
            MOCK_CHANGE_DESCRIPTION,
            strength=0.7,
            temperature=0.0,
            verbose=True
        )
        
        # Capture and verify console output
        captured = capsys.readouterr()
        assert "Initial Analysis Results" in captured.out
        assert "Extraction Results" in captured.out
        assert "Detected Changes" in captured.out

def test_general_exception_handling():
    """Test general exception handling."""
    with patch('pdd.detect_change.load_prompt_template', side_effect=Exception("Unexpected error")):
        with pytest.raises(Exception, match="Unexpected error"):
            detect_change(
                MOCK_PROMPT_FILES,
                MOCK_CHANGE_DESCRIPTION,
                strength=0.7,
                temperature=0.0
            )