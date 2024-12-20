import pytest
from pdd.conflicts_in_prompts import conflicts_in_prompts
from unittest.mock import patch, MagicMock

# Test data
VALID_PROMPT1 = "Write a formal business email in a serious tone."
VALID_PROMPT2 = "Write a casual, funny email with jokes."
MOCK_TEMPLATE = "Mock template content"
MOCK_LLM_RESPONSE = {
    'result': "Mock LLM output",
    'cost': 0.001,
    'model_name': "test-model"
}
MOCK_STRUCTURED_RESPONSE = {
    'result': MagicMock(
        changes_list=[
            MagicMock(
                dict=lambda: {
                    'prompt_name': 'prompt1',
                    'change_instructions': 'Make less formal'
                }
            )
        ]
    ),
    'cost': 0.002,
    'model_name': "test-model"
}

@pytest.fixture
def mock_dependencies():
    """Fixture to mock dependencies"""
    with patch('pdd.conflicts_in_prompts.load_prompt_template') as mock_load_template:
        with patch('pdd.conflicts_in_prompts.llm_invoke') as mock_llm_invoke:
            mock_load_template.return_value = MOCK_TEMPLATE
            mock_llm_invoke.side_effect = [MOCK_LLM_RESPONSE, MOCK_STRUCTURED_RESPONSE]
            yield {
                'load_template': mock_load_template,
                'llm_invoke': mock_llm_invoke
            }

def test_successful_conflict_analysis(mock_dependencies):
    """Test successful execution with valid inputs"""
    changes_list, total_cost, model_name = conflicts_in_prompts(
        VALID_PROMPT1,
        VALID_PROMPT2,
        strength=0.5,
        temperature=0,
        verbose=False
    )

    assert isinstance(changes_list, list)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert total_cost == 0.003  # Sum of both LLM calls
    assert model_name == "test-model"
    assert len(changes_list) == 1
    assert changes_list[0]['prompt_name'] == 'prompt1'

def test_empty_prompts():
    """Test handling of empty prompt inputs"""
    with pytest.raises(ValueError, match="Both prompts must be provided"):
        conflicts_in_prompts("", VALID_PROMPT2)
    
    with pytest.raises(ValueError, match="Both prompts must be provided"):
        conflicts_in_prompts(VALID_PROMPT1, "")

def test_invalid_strength():
    """Test handling of invalid strength parameter"""
    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        conflicts_in_prompts(VALID_PROMPT1, VALID_PROMPT2, strength=1.5)
    
    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        conflicts_in_prompts(VALID_PROMPT1, VALID_PROMPT2, strength=-0.1)

def test_invalid_temperature():
    """Test handling of invalid temperature parameter"""
    with pytest.raises(ValueError, match="Temperature must be between 0 and 1"):
        conflicts_in_prompts(VALID_PROMPT1, VALID_PROMPT2, temperature=1.5)
    
    with pytest.raises(ValueError, match="Temperature must be between 0 and 1"):
        conflicts_in_prompts(VALID_PROMPT1, VALID_PROMPT2, temperature=-0.1)

def test_template_loading_failure(mock_dependencies):
    """Test handling of template loading failure"""
    mock_dependencies['load_template'].return_value = None
    
    with pytest.raises(ValueError, match="Failed to load prompt templates"):
        conflicts_in_prompts(VALID_PROMPT1, VALID_PROMPT2)

def test_llm_invoke_failure(mock_dependencies):
    """Test handling of LLM invocation failure"""
    mock_dependencies['llm_invoke'].side_effect = Exception("LLM error")
    
    with pytest.raises(RuntimeError, match="Error in conflicts_in_prompts: LLM error"):
        conflicts_in_prompts(VALID_PROMPT1, VALID_PROMPT2)

def test_verbose_output(mock_dependencies, capsys):
    """Test verbose output functionality"""
    conflicts_in_prompts(
        VALID_PROMPT1,
        VALID_PROMPT2,
        verbose=True
    )
    
    captured = capsys.readouterr()
    assert "Analyzing prompts for conflicts" in captured.out
    assert "Extracting structured conflict information" in captured.out

def test_correct_llm_parameters(mock_dependencies):
    """Test that LLM is called with correct parameters"""
    strength = 0.5
    temperature = 0.3
    
    conflicts_in_prompts(
        VALID_PROMPT1,
        VALID_PROMPT2,
        strength=strength,
        temperature=temperature
    )
    
    # Check first LLM call
    first_call = mock_dependencies['llm_invoke'].call_args_list[0][1]
    assert first_call['strength'] == strength
    assert first_call['temperature'] == temperature
    
    # Check second LLM call
    second_call = mock_dependencies['llm_invoke'].call_args_list[1][1]
    assert second_call['strength'] == 0.89  # Fixed strength for second call
    assert second_call['temperature'] == temperature