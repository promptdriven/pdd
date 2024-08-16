import pytest
from unittest.mock import patch, MagicMock
from llm_token_counter import llm_token_counter  # Replace with the actual module name

def test_llm_token_counter_tiktoken() -> None:
    """Test the tiktoken counter by mocking the get_encoding function."""
    with patch('tiktoken.get_encoding') as mock_get_encoding:
        mock_encoding = MagicMock()
        mock_encoding.encode.return_value = ['token1', 'token2']  # Simulate tokenization
        mock_get_encoding.return_value = mock_encoding
        
        token_counter = llm_token_counter('tiktoken', 'cl100k_base')
        assert token_counter("Sample text") == 2  # Expecting 2 tokens

def test_llm_token_counter_anthropic() -> None:
    """Test the anthropic counter by mocking the Anthropic client."""
    with patch('anthropic.Anthropic') as mock_anthropic:
        mock_client = MagicMock()
        mock_client.count_tokens.return_value = 5  # Simulate token count
        mock_anthropic.return_value = mock_client
        
        token_counter = llm_token_counter('anthropic')
        assert token_counter("Sample text") == 5  # Expecting 5 tokens

def test_llm_token_counter_autotokenizer() -> None:
    """Test the autotokenizer counter by mocking the AutoTokenizer."""
    with patch('transformers.AutoTokenizer.from_pretrained') as mock_from_pretrained:
        mock_tokenizer = MagicMock()
        mock_tokenizer.return_value = {'input_ids': [1, 2, 3]}  # Simulate tokenization
        mock_from_pretrained.return_value = mock_tokenizer
        
        token_counter = llm_token_counter('autotokenizer', 'deepseek-ai/deepseek-coder-7b-instruct-v1.5')
        assert token_counter("Sample text") == 3  # Expecting 3 tokens

def test_llm_token_counter_invalid_counter() -> None:
    """Ensure that an invalid counter raises a ValueError."""
    with pytest.raises(ValueError, match="Invalid counter specified. Choose from 'tiktoken', 'anthropic', or 'autotokenizer'."):
        llm_token_counter('invalid_counter')

def test_llm_token_counter_tiktoken_missing_encoder() -> None:
    """Ensure that calling llm_token_counter with tiktoken but without an encoder raises a ValueError."""
    with pytest.raises(ValueError, match="Encoder must be specified for tiktoken."):
        llm_token_counter('tiktoken')

def test_llm_token_counter_autotokenizer_missing_model() -> None:
    """Ensure that calling llm_token_counter with autotokenizer but without a model raises a ValueError."""
    with pytest.raises(ValueError, match="Model name must be specified for autotokenizer."):
        llm_token_counter('autotokenizer')

# To run the tests, use the command: pytest <name_of_this_file>.py