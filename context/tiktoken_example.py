encoding = tiktoken.get_encoding("cl100k_base")  # or another encoding name
token_count = len(encoding.encode(preprocessed_prompt))