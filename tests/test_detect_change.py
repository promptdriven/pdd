import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from pdd.detect_change import detect_change, ChangesList, ChangeInstruction
from pdd import DEFAULT_STRENGTH, EXTRACTION_STRENGTH
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
            time=None,
            verbose=False
        )
        
        # Verify results
        assert len(changes_list) == 1
        assert changes_list[0]["prompt_name"] == "test1.prompt"
        assert changes_list[0]["change_instructions"] == "Add better error handling"
        assert total_cost == 0.08  # 0.05 + 0.03
        assert model_name == "gpt-3.5-turbo"

        # Verify arguments for the calls to llm_invoke
        assert mock_llm_invoke.call_count == 2

        # First call (detection)
        detection_call_kwargs = mock_llm_invoke.call_args_list[0].kwargs
        assert detection_call_kwargs['strength'] == 0.7 # Matches the input strength to detect_change
        assert detection_call_kwargs['temperature'] == 0.0 # Matches the input temperature to detect_change
        assert detection_call_kwargs['time'] is None # Check time parameter
        assert detection_call_kwargs['prompt'] == "Processed template" # Mocked preprocessed detect_template

        # Second call (extraction)
        extraction_call_kwargs = mock_llm_invoke.call_args_list[1].kwargs
        assert extraction_call_kwargs['strength'] == EXTRACTION_STRENGTH
        assert extraction_call_kwargs['temperature'] == 0.0
        assert extraction_call_kwargs['time'] is None # Check time parameter
        assert extraction_call_kwargs['prompt'] == mock_templates[1] # extract_template
        assert 'llm_output' in extraction_call_kwargs['input_json']
        assert extraction_call_kwargs['output_pydantic'] == ChangesList

def test_missing_prompt_template():
    """Test handling of missing prompt template."""
    with patch('pdd.detect_change.load_prompt_template', return_value=None):
        with pytest.raises(ValueError, match="Failed to load detect_change_LLM prompt template"):
            detect_change(
                MOCK_PROMPT_FILES,
                MOCK_CHANGE_DESCRIPTION,
                strength=0.7,
                temperature=0.0,
                time=None
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
            time=None,
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
            time=None,
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
                temperature=0.0,
                time=None
            )


# ---------------------------------------------------------------------------
# Scope addition: covers expansion item pdd/detect_change.py:123 identified
# by Step 6 but absent from Step 8's plan.
#
# Root cause (sibling of issue #1612 Bug 1): `changes_list =
# extract_response['result'].changes_list` at line 123 has no isinstance
# guard.  When llm_invoke returns None or a raw str as the extraction result
# (cache-bypass / truncation path), the attribute access raises AttributeError
# instead of handling the malformed response gracefully.
# ---------------------------------------------------------------------------


def test_extract_result_none_does_not_raise_attribute_error_issue_1612(mock_templates):
    """Scope addition: covers expansion item pdd/detect_change.py:123 identified
    by Step 6 but absent from Step 8's plan.

    When the extraction llm_invoke returns None as result, accessing
    extract_response['result'].changes_list raises
    AttributeError('NoneType object has no attribute changes_list').
    detect_change should handle this gracefully rather than propagating
    AttributeError to the caller.
    """
    detect_response = {
        'result': 'Analysis results',
        'cost': 0.05,
        'token_count': 100,
        'model_name': 'gpt-3.5-turbo',
    }
    # Extraction call returns None as the Pydantic result (cache-bypass path)
    extract_response_none = {
        'result': None,
        'cost': 0.03,
        'token_count': 50,
        'model_name': 'gpt-3.5-turbo',
    }

    with patch('pdd.detect_change.load_prompt_template') as mock_load_template, \
         patch('pdd.detect_change.preprocess') as mock_preprocess, \
         patch('pdd.detect_change.llm_invoke') as mock_llm_invoke:

        mock_load_template.side_effect = mock_templates
        mock_preprocess.return_value = "Processed template"
        mock_llm_invoke.side_effect = [detect_response, extract_response_none]

        # After the fix, detect_change must not propagate AttributeError.
        # The function should return a graceful fallback (e.g., empty list)
        # rather than crashing with:
        #   AttributeError: 'NoneType' object has no attribute 'changes_list'
        result_list, _cost, _model = detect_change(
            MOCK_PROMPT_FILES,
            MOCK_CHANGE_DESCRIPTION,
            strength=0.7,
            temperature=0.0,
        )
        assert isinstance(result_list, list)


def test_extract_result_raw_string_does_not_raise_attribute_error_issue_1612(mock_templates):
    """Scope addition: covers expansion item pdd/detect_change.py:123 identified
    by Step 6 but absent from Step 8's plan.

    When the extraction llm_invoke returns a raw string as result (as observed
    in production for the incremental generator sibling bug), accessing
    extract_response['result'].changes_list raises
    AttributeError('str object has no attribute changes_list').
    detect_change should handle this gracefully.
    """
    detect_response = {
        'result': 'Analysis results',
        'cost': 0.05,
        'token_count': 100,
        'model_name': 'gpt-3.5-turbo',
    }
    extract_response_str = {
        'result': "Cache bypass retry also returned None",
        'cost': 0.03,
        'token_count': 50,
        'model_name': 'gpt-3.5-turbo',
    }

    with patch('pdd.detect_change.load_prompt_template') as mock_load_template, \
         patch('pdd.detect_change.preprocess') as mock_preprocess, \
         patch('pdd.detect_change.llm_invoke') as mock_llm_invoke:

        mock_load_template.side_effect = mock_templates
        mock_preprocess.return_value = "Processed template"
        mock_llm_invoke.side_effect = [detect_response, extract_response_str]

        result_list, _cost, _model = detect_change(
            MOCK_PROMPT_FILES,
            MOCK_CHANGE_DESCRIPTION,
            strength=0.7,
            temperature=0.0,
        )
        assert isinstance(result_list, list)


def test_extract_result_raw_dict_does_not_raise_attribute_error_issue_1612(mock_templates):
    """Raw-dict variant of the #1612 guard: a cloud structured-output response
    that fails Pydantic validation leaves a plain ``dict`` in result['result'].
    The narrow None/str guard missed it; the robust isinstance(result,
    ChangesList) guard must return a graceful list, not crash on
    ``.changes_list``.
    """
    detect_response = {
        'result': 'Analysis results',
        'cost': 0.05,
        'token_count': 100,
        'model_name': 'gpt-3.5-turbo',
    }
    extract_response_dict = {
        'result': {'changes_list': []},  # raw dict, not ChangesList
        'cost': 0.03,
        'token_count': 50,
        'model_name': 'gpt-3.5-turbo',
    }

    with patch('pdd.detect_change.load_prompt_template') as mock_load_template, \
         patch('pdd.detect_change.preprocess') as mock_preprocess, \
         patch('pdd.detect_change.llm_invoke') as mock_llm_invoke:

        mock_load_template.side_effect = mock_templates
        mock_preprocess.return_value = "Processed template"
        mock_llm_invoke.side_effect = [detect_response, extract_response_dict]

        result_list, _cost, _model = detect_change(
            MOCK_PROMPT_FILES,
            MOCK_CHANGE_DESCRIPTION,
            strength=0.7,
            temperature=0.0,
        )
        assert isinstance(result_list, list)