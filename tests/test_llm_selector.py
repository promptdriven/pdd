import os
import pytest
import pandas as pd
from unittest.mock import patch, MagicMock
from llm_selector import llm_selector  # Replace with the actual module name

# Sample data to be used in the tests
sample_model_data = pd.DataFrame({
    'provider': ['OpenAI', 'OpenAI', 'Anthropic', 'Google'],
    'model': ['gpt-4o-mini', 'gpt-4o', 'claude-3-5-sonnet-20240620', 'gemini-1.5-pro'],
    'input': [0.15, 5, 3, 3.5],
    'output': [0.60, 15, 15, 7],
    'coding_arena_elo': [1281, 1295, 1300, 1264],
    'base_url': ['https://api.openai.com', 'https://api.openai.com', 'https://api.anthropic.com', 'https://api.google.com'],
    'api_key': ['OPENAI_API_KEY', 'OPENAI_API_KEY', 'ANTHROPIC_API_KEY', 'GOOGLE_API_KEY'],
    'counter': ['tiktoken', 'tiktoken', 'anthropic', 'tiktoken'],
    'encoder': ['o200k_base', 'o200k_base', 'claude-3-sonnet-20240229', 'o200k_base']
})

# Mocking the load_model_data function to return the sample data
def mock_load_model_data() -> pd.DataFrame:
    """Mock function to return predefined sample model data."""
    return sample_model_data

# Test cases
@pytest.mark.parametrize("strength, temperature, expected_model", [
    (0.0, 0.5, 'gpt-4o-mini'),  # Expecting the cheapest model
    (0.5, 0.5, 'gpt-4o-mini'),  # Expecting the base model
    (1.0, 0.5, 'claude-3-5-sonnet-20240620'),  # Expecting the highest ELO model
    (0.3, 0.5, 'gpt-4o-mini'),  # Expecting a model based on cost interpolation
    (0.7, 0.5, 'claude-3-5-sonnet-20240620'),  # Expecting a model based on ELO interpolation
])
@patch('llm_selector.load_model_data', side_effect=mock_load_model_data)  # Replace with the actual module name
@patch.dict(os.environ, {'PDD_MODEL_DEFAULT': 'gpt-4o-mini'})  # Mocking environment variable
def test_llm_selector(mock_load, strength: float, temperature: float, expected_model: str) -> None:
    """Test the llm_selector function to ensure it selects the correct model."""
    llm, token_counter, input_cost, output_cost = llm_selector(strength, temperature)
    
    # Check if the expected model is selected
    assert llm.model == expected_model, f"Expected {expected_model}, got {llm.model}"
    assert callable(token_counter), "Token counter should be callable"
    assert input_cost >= 0, "Input cost should be non-negative"
    assert output_cost >= 0, "Output cost should be non-negative"

# Run the tests
if __name__ == "__main__":
    pytest.main()
