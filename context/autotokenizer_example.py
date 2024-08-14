from transformers import AutoTokenizer

def count_tokens(text, model_name="deepseek-ai/deepseek-coder-7b-instruct-v1.5"):
    # Load the tokenizer for the specified model
    tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
    
    # Tokenize the input text
    tokens = tokenizer(text)
    
    # Return the number of tokens
    return len(tokens['input_ids'])

# Example usage
text = "Write a quick sort algorithm in Python."
token_count = count_tokens(text)
print(f"Number of tokens: {token_count}")