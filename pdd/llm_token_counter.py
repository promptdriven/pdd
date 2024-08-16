import tiktoken
import anthropic
from transformers import AutoTokenizer


def llm_token_counter(counter: str, encoder: str = None):
    """
    Returns a token counting function based on the specified counter method.

    :param counter: The name of the token counting method ('tiktoken', 'anthropic', 'autotokenizer').
    :param encoder: The encoder/model name, if applicable.
    :return: A function that counts tokens in a given text.
    :raises ValueError: If an invalid counter is specified or if encoder is required but not provided.
    """
    if counter == 'tiktoken':
        if encoder is None:
            raise ValueError("Encoder must be specified for tiktoken.")

        def token_counter_function(text: str) -> int:
            encoding = tiktoken.get_encoding(encoder)
            return len(encoding.encode(text))

        return token_counter_function

    elif counter == 'anthropic':
        client = anthropic.Anthropic()

        def token_counter_function(text: str) -> int:
            return client.count_tokens(text)

        return token_counter_function

    elif counter == 'autotokenizer':
        if encoder is None:
            raise ValueError("Model name must be specified for autotokenizer.")

        def token_counter_function(text: str) -> int:
            tokenizer = AutoTokenizer.from_pretrained(encoder, trust_remote_code=True)
            tokens = tokenizer(text)
            return len(tokens['input_ids'])

        return token_counter_function

    else:
        raise ValueError("Invalid counter specified. Choose from 'tiktoken', 'anthropic', or 'autotokenizer'.")

# Example usage:
# For tiktoken
# tiktoken_counter = llm_token_counter('tiktoken', 'cl100k_base')
# print(tiktoken_counter("Sample text for tiktoken."))

# For anthropic
# anthropic_counter = llm_token_counter('anthropic')
# print(anthropic_counter("Sample text for anthropic."))

# For autotokenizer
# autotokenizer_counter = llm_token_counter('autotokenizer', 'deepseek-ai/deepseek-coder-7b-instruct-v1.5')
# print(autotokenizer_counter("Sample text for autotokenizer."))
