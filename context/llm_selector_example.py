# Here's a concise example of how to use the `llm_selector` function from the `pdd/llm_selector.py` module:

# ```python
import os
from pdd.llm_selector import llm_selector

# Set environment variables (for demonstration purposes)
os.environ['PDD_MODEL_DEFAULT'] = 'gpt-4o-mini'
os.environ['PDD_PATH'] = '/path/to/your/data'

# Call the llm_selector function with desired strength and temperature
strength = 0.3  # Adjust strength between 0 and 1
temperature = 0.7  # Set the desired temperature for the model

# Get the selected model and costs
llm, input_cost, output_cost = llm_selector(strength, temperature)

# Output the results
print(f"Selected LLM: {llm}, Input Cost: {input_cost}, Output Cost: {output_cost}")
# ```

# ### Explanation:
# 1. **Environment Variables**: Set the necessary environment variables for the model selection.
# 2. **Function Call**: Call `llm_selector` with specific `strength` and `temperature` values.
# 3. **Output**: Print the selected model and its associated costs. 

# Make sure to replace `'/path/to/your/data'` with the actual path where your `llm_model.csv` file is located.