# To implement the `llm_selector` function, we need to follow these steps:

# 1. Load the LLM model data from the CSV file.
# 2. Determine the base model based on the environment variable `$PDD_MODEL_DEFAULT` or default to "gpt-4o-mini".
# 3. Calculate the average cost of input and output tokens for each model.
# 4. Interpolate the model selection based on the `strength` parameter.
# 5. Instantiate the selected model with the specified `temperature`.

# Here's the complete implementation:

# ```python
import os
import pandas as pd
from langchain_openai import ChatOpenAI
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_anthropic import ChatAnthropic
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

def instantiate_llm(provider, model, temperature):
    if provider == 'OpenAI':
        return ChatOpenAI(model=model, temperature=temperature)
    elif provider == 'Google':
        return ChatGoogleGenerativeAI(model=model, temperature=temperature)
    elif provider == 'Anthropic':
        return ChatAnthropic(model=model, temperature=temperature)
    else:
        raise ValueError(f"Unknown provider: {provider}")

def llm_selector(strength, temperature):
    # Load environment variables
    base_model = os.getenv('PDD_MODEL_DEFAULT', 'gpt-4o-mini')
    pdd_path = os.getenv('PDD_PATH', os.getcwd())
    csv_path = os.path.join(pdd_path, 'data', 'llm_model.csv')
    
    # Load the CSV file
    df = pd.read_csv(csv_path)
    
    # Calculate average cost for each model
    df['average_cost'] = (df['input'] + df['output']) / 2
    
    # Get the base model details
    base_model_row = df[df['model'] == base_model].iloc[0]
    base_model_avg_cost = base_model_row['average_cost']
    base_model_elo = base_model_row['coding_arena_elo']
    
    if strength < 0.5:
        # Interpolate down based on cost
        cheapest_model_row = df.loc[df['average_cost'].idxmin()]
        target_cost = base_model_avg_cost - (base_model_avg_cost - cheapest_model_row['average_cost']) * (0.5 - strength) / 0.5
        selected_model_row = df[df['average_cost'] <= target_cost].sort_values(by='average_cost').iloc[0]
    elif strength > 0.5:
        # Interpolate up based on ELO
        highest_elo_model_row = df.loc[df['coding_arena_elo'].idxmax()]
        target_elo = base_model_elo + (highest_elo_model_row['coding_arena_elo'] - base_model_elo) * (strength - 0.5) / 0.5
        # Calculate the absolute difference between each row's elo and the target_elo
        df['elo_difference'] = abs(df['coding_arena_elo'] - target_elo)

        # Select the row with the smallest difference
        selected_model_row = df.loc[df['elo_difference'].idxmin()]

        # selected_model_row = df[df['coding_arena_elo'] >= target_elo].sort_values(by='coding_arena_elo', ascending=False).iloc[0]
    else:
        # Use base model
        selected_model_row = base_model_row
    
    # Instantiate the selected model
    # llm = ChatOpenAI(model=selected_model_row['model'], temperature=temperature)
    llm = instantiate_llm(selected_model_row['provider'], selected_model_row['model'], temperature)
    print("Selected model:", selected_model_row['model'])
    # Return the model and costs
    return llm, selected_model_row['input'], selected_model_row['output']

# Example usage
# llm, input_cost, output_cost = llm_selector(0.7, 0.7)
# print(f"Selected LLM: {llm}, Input Cost: {input_cost}, Output Cost: {output_cost}")
# ```

# ### Explanation:

# 1. **Environment Variables and CSV Loading**:
#    - The function reads the environment variables `$PDD_MODEL_DEFAULT` and `$PDD_PATH`.
#    - It loads the LLM model data from the CSV file located at `$PDD_PATH/data/llm_model.csv`.

# 2. **Base Model and Average Cost Calculation**:
#    - The base model is determined from the environment variable or defaults to "gpt-4o-mini".
#    - The average cost of input and output tokens is calculated for each model.

# 3. **Model Selection Based on Strength**:
#    - If `strength < 0.5`, the function interpolates downwards based on cost.
#    - If `strength > 0.5`, the function interpolates upwards based on ELO.
#    - If `strength == 0.5`, the base model is used.

# 4. **Model Instantiation**:
#    - The selected model is instantiated with the specified `temperature`.

# 5. **Return Values**:
#    - The function returns the instantiated LLM model and the costs per million input and output tokens.

# This implementation ensures that the appropriate model is selected based on the given `strength` and `temperature` parameters, following the specified rules.