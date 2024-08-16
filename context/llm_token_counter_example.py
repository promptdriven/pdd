import tiktoken
import anthropic
from transformers import AutoTokenizer
from llm_token_counter import llm_token_counter  # Replace 'your_module' with the actual module name

def main() -> None:
    """
    Main function to demonstrate token counting using different methods.
    """
    try:
        # Example usage for tiktoken
        tiktoken_encoder = tiktoken.get_encoding("o200k_base")
        tiktoken_counter = llm_token_counter('tiktoken', "o200k_base")
        sample_text_tiktoken = "Sample text for tiktoken."
        print(f"Tiktoken count: {tiktoken_counter(sample_text_tiktoken)}")  # Output: Number of tokens
    except Exception as e:
        print(f"Error with tiktoken: {e}")

    try:
        # Example usage for anthropic
        anthropic_counter = llm_token_counter('anthropic', "claude-3-sonnet-20240229")
        sample_text_anthropic = "Sample text for anthropic."
        print(f"Anthropic count: {anthropic_counter(sample_text_anthropic)}")  # Output: Number of tokens
    except Exception as e:
        print(f"Error with anthropic: {e}")

    try:
        # Example usage for autotokenizer
        autotokenizer_counter = llm_token_counter('autotokenizer', "deepseek-ai/deepseek-coder-7b-instruct-v1.5")
        sample_text_autotokenizer = "Sample text for autotokenizer."
        print(f"Autotokenizer count: {autotokenizer_counter(sample_text_autotokenizer)}")  # Output: Number of tokens
    except Exception as e:
        print(f"Error with autotokenizer: {e}")

if __name__ == "__main__":
    main()