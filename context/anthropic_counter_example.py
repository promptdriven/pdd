import anthropic

# Initialize the Anthropic client
client = anthropic.Anthropic()

# Text you want to count tokens for
text = "Sample text"

# Count tokens
total_tokens = client.count_tokens(text, model="claude-3-sonnet-20240229")

print(f"Number of tokens: {total_tokens}")