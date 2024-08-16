import anthropic

# Initialize the Anthropic client
client = anthropic.Anthropic()

# Text you want to count tokens for
text = "Sample text"

# Count tokens
# not accurate for 3.0 and above models
total_tokens = client.count_tokens(text)

print(f"Number of tokens: {total_tokens}")