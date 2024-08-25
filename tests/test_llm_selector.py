import os
import pytest
import pandas as pd
from unittest.mock import patch, MagicMock
from pdd.llm_selector import llm_selector
from io import StringIO

# Sample data for mocking the CSV file
sample_csv_data = """provider,model,input,output,coding_arena_elo,base_url,api_key,counter,encoder
OpenAI,gpt-4o-mini,0.15,0.60,1281,https://api.openai.com,OPENAI_API_KEY,tiktoken,o200k_base
OpenAI,gpt-4o,5,15,1295,https://api.openai.com,OPENAI_API_KEY,tiktoken,o200k_base
Anthropic,claude-3-5-sonnet-20240620,3,15,1300,https://api.anthropic.com,ANTHROPIC_API_KEY,anthropic,claude-3-sonnet-20240229
Google,gemini-1.5-pro,3.5,7,1264,https://api.google.com,GOOGLE_API_KEY,tiktoken,o200k_base
"""

@pytest.fixture
def mock_csv_reader(monkeypatch):
    original_read_csv = pd.read_csv
    
    def create_mock_read_csv(csv_data):
        def mock_read_csv(*args, **kwargs):
            return original_read_csv(StringIO(csv_data))
        return mock_read_csv

    def mock_csv(csv_data):
        monkeypatch.setattr(pd, 'read_csv', create_mock_read_csv(csv_data))

    return mock_csv

# Mocking the environment variables
@pytest.fixture
def mock_env(monkeypatch):
    monkeypatch.setenv('PDD_MODEL_DEFAULT', 'gpt-4o-mini')
    monkeypatch.setenv('PDD_PATH', '/mock/path')

# Test for strength < 0.5
def test_llm_selector_strength_below_base(mock_csv_reader, mock_env):
    mock_csv_reader(sample_csv_data)
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(0.3, 0.7)
    assert model_name == 'gpt-4o-mini'
    assert input_cost == 0.15
    assert output_cost == 0.60

# Test for strength = 0.5 (base model)
def test_llm_selector_strength_base(mock_csv_reader, mock_env):
    mock_csv_reader(sample_csv_data)
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(0.5, 0.7)
    assert model_name == 'gpt-4o-mini'
    assert input_cost == 0.15
    assert output_cost == 0.60

# Test for strength > 0.5
def test_llm_selector_strength_above_base(mock_csv_reader, mock_env):
    mock_csv_reader(sample_csv_data)
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(0.8, 0.7)
    assert model_name == 'gpt-4o'
    assert input_cost == 5
    assert output_cost == 15

# Test for handling FileNotFoundError
def test_llm_selector_file_not_found(mock_env, monkeypatch):
    def mock_read_csv(*args, **kwargs):
        raise FileNotFoundError("CSV file not found")
    
    monkeypatch.setattr(pd, 'read_csv', mock_read_csv)
    
    with pytest.raises(FileNotFoundError):
        llm_selector(0.5, 0.7)

# Test for base model not found
def test_llm_selector_base_model_not_found(mock_env, mock_csv_reader):
    csv_data = """provider,model,input,output,coding_arena_elo,base_url,api_key,counter,encoder
OpenAI,gpt-4o,5,15,1295,https://api.openai.com,OPENAI_API_KEY,tiktoken,o200k_base
Anthropic,claude-3-5-sonnet-20240620,3,15,1300,https://api.anthropic.com,ANTHROPIC_API_KEY,anthropic,claude-3-sonnet-20240229
"""
    mock_csv_reader(csv_data)
    
    with pytest.raises(ValueError):
        llm_selector(0.5, 0.7)

# Test for unsupported provider
def test_llm_selector_unsupported_provider(mock_env, mock_csv_reader):
    csv_data = """provider,model,input,output,coding_arena_elo,base_url,api_key,counter,encoder
Unsupported,unsupported-model,1,1,1000,https://api.unsupported.com,UNSUPPORTED_API_KEY,unsupported,unsupported_encoder
"""
    mock_csv_reader(csv_data)
    
    with pytest.raises(ValueError):
        llm_selector(0.5, 0.7)

# Run the tests
if __name__ == "__main__":
    pytest.main()