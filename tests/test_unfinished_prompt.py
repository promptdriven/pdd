import os
import pytest
from unittest.mock import patch, MagicMock
from pdd.unfinished_prompt import unfinished_prompt

# Test when everything works as expected
def test_unfinished_prompt_success():
    with patch('os.getenv', return_value='/mock/path'), \
         patch('builtins.open', new_callable=MagicMock) as mock_open, \
         patch('pdd.unfinished_prompt.llm_selector') as mock_llm_selector, \
         patch('pdd.unfinished_prompt.PromptTemplate.from_template') as mock_prompt_template, \
         patch('pdd.unfinished_prompt.JsonOutputParser') as mock_parser:

        # Mock the file read
        mock_open.return_value.__enter__.return_value.read.return_value = "mock template"

        # Mock the LLM selector
        mock_token_counter = MagicMock(side_effect=[100, 50])  # First call for input, second for output
        mock_llm_selector.return_value = (MagicMock(), mock_token_counter, 0.01, 0.02, "mock_model")

        # Mock the chain invocation
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = {'reasoning': 'Mock reasoning', 'is_finished': True}
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain

        reasoning, is_finished, total_cost, model_name = unfinished_prompt("This is a test prompt.")

        assert reasoning == 'Mock reasoning'
        assert is_finished is True
        # Correct calculation: (100 * 0.01 + 50 * 0.02) / 1,000,000 = 0.000002
        assert total_cost == pytest.approx(0.000002, 1e-9)
        assert model_name == "mock_model"

        # Additional assertions
        assert mock_token_counter.call_count == 2
        assert mock_token_counter.call_args_list[0][0][0] == "This is a test prompt."
        assert mock_token_counter.call_args_list[1][0][0] == '{"reasoning": "Mock reasoning", "is_finished": true}'

# Test when PDD_PATH environment variable is not set
def test_unfinished_prompt_no_pdd_path():
    with patch('os.getenv', return_value=None):
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            unfinished_prompt("This is a test prompt.")

# Test when the prompt file is not found
def test_unfinished_prompt_file_not_found():
    with patch('os.getenv', return_value='/mock/path'), \
         patch('builtins.open', side_effect=FileNotFoundError):
        with pytest.raises(FileNotFoundError, match="Prompt file not found at /mock/path/prompts/unfinished_prompt_LLM.prompt"):
            unfinished_prompt("This is a test prompt.")

# Test when there is an error selecting the LLM model
def test_unfinished_prompt_llm_selector_error():
    with patch('os.getenv', return_value='/mock/path'), \
         patch('builtins.open', new_callable=MagicMock) as mock_open, \
         patch('pdd.unfinished_prompt.llm_selector', side_effect=Exception("LLM selection error")):
        
        mock_open.return_value.__enter__.return_value.read.return_value = "mock template"
        
        with pytest.raises(RuntimeError, match="Error selecting LLM model: LLM selection error"):
            unfinished_prompt("This is a test prompt.")

# Test when there is an error during LLM invocation
def test_unfinished_prompt_llm_invocation_error():
    with patch('os.getenv', return_value='/mock/path'), \
         patch('builtins.open', new_callable=MagicMock) as mock_open, \
         patch('pdd.unfinished_prompt.llm_selector') as mock_llm_selector, \
         patch('pdd.unfinished_prompt.PromptTemplate.from_template') as mock_prompt_template:

        # Mock the file read
        mock_open.return_value.__enter__.return_value.read.return_value = "mock template"

        # Mock the LLM selector
        mock_token_counter = MagicMock(return_value=100)
        mock_llm_selector.return_value = (MagicMock(), mock_token_counter, 0.01, 0.02, "mock_model")

        # Mock the chain invocation to raise an exception
        mock_chain = MagicMock()
        mock_chain.invoke.side_effect = Exception("LLM invocation error")
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain

        with pytest.raises(RuntimeError, match="Error during LLM invocation: LLM invocation error"):
            unfinished_prompt("This is a test prompt.")

# Parameterized test for different token counts and costs
@pytest.mark.parametrize("input_tokens,output_tokens,input_cost,output_cost,expected_total_cost", [
    (100, 50, 0.01, 0.02, 0.000002),
    (1000, 500, 0.005, 0.01, 0.000010),
    (10000, 5000, 0.001, 0.002, 0.000020),
])
def test_unfinished_prompt_cost_calculation(input_tokens, output_tokens, input_cost, output_cost, expected_total_cost):
    with patch('os.getenv', return_value='/mock/path'), \
         patch('builtins.open', new_callable=MagicMock) as mock_open, \
         patch('pdd.unfinished_prompt.llm_selector') as mock_llm_selector, \
         patch('pdd.unfinished_prompt.PromptTemplate.from_template') as mock_prompt_template, \
         patch('pdd.unfinished_prompt.JsonOutputParser') as mock_parser:

        mock_open.return_value.__enter__.return_value.read.return_value = "mock template"
        mock_token_counter = MagicMock(side_effect=[input_tokens, output_tokens])
        mock_llm_selector.return_value = (MagicMock(), mock_token_counter, input_cost, output_cost, "mock_model")
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = {'reasoning': 'Mock reasoning', 'is_finished': True}
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain

        _, _, total_cost, _ = unfinished_prompt("This is a test prompt.")

        assert total_cost == pytest.approx(expected_total_cost, 1e-9)
