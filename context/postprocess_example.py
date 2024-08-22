from postprocess import postprocess



# Example LLM output containing code
llm_output = """
Here is a simple Python function:
```python
def hello_world():
    print("Hello, world!")
```
You can use this function in your application.
"""

# Specify the programming language and model parameters
language = "python"
strength = 0.9  # Model strength
temperature = 0.5  # Model temperature

# Call the postprocess function
extracted_code, total_cost = postprocess(llm_output, language, strength, temperature)

# Print the results
print("Extracted Code:")
print(extracted_code)
print(f"Total Cost: ${total_cost:.6f}")