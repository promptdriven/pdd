from litellm import completion

response = completion(
    model="vertex_ai/gemini-2.5-pro-preview-05-06",
    messages=[{"role": "user", "content": "Your prompt here"}]
)
print(response)
