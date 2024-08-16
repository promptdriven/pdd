import os
import pandas as pd
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_anthropic import ChatAnthropic
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from llm_token_counter import llm_token_counter  # Assuming this is the correct import for your token counter

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

def load_model_data() -> pd.DataFrame:
    """
    Load model data from a CSV file specified by the PDD_PATH environment variable.
    Returns a DataFrame containing the model data.
    """
    pdd_path = os.getenv('PDD_PATH', os.getcwd())
    model_file = os.path.join(pdd_path, 'data', 'llm_model.csv')
    return pd.read_csv(model_file)

def llm_selector(strength: float, temperature: float):
    """
    Selects an LLM model based on the given strength and temperature.
    Returns the instantiated LLM model, token counter function, and cost information.
    """
    # Load model data
    model_data = load_model_data()
    
    # Determine the base model
    base_model_name = os.getenv('PDD_MODEL_DEFAULT', 'gpt-4o-mini')
    base_model_row = model_data[model_data['model'] == base_model_name].iloc[0]
    
    # Extract base model costs and ELO
    base_input_cost = base_model_row['input']
    base_output_cost = base_model_row['output']
    base_elo = base_model_row['coding_arena_elo']
    
    # Calculate average costs
    model_data['average_cost'] = (model_data['input'] + model_data['output']) / 2
    
    if strength < 0.5:
        # Interpolate downwards based on average cost
        min_cost_row = model_data[model_data['average_cost'] == model_data['average_cost'].min()].iloc[0]
        min_input_cost = min_cost_row['input']
        min_output_cost = min_cost_row['output']
        
        # Calculate target cost
        target_cost = base_input_cost + (min_input_cost - base_input_cost) * (strength / 0.5)
        
        # Select model with closest average cost
        selected_model_row = model_data.loc[(model_data['average_cost'] <= target_cost)].iloc[0]
    
    elif strength > 0.5:
        # Interpolate upwards based on ELO
        max_elo_row = model_data[model_data['coding_arena_elo'] == model_data['coding_arena_elo'].max()].iloc[0]
        max_elo = max_elo_row['coding_arena_elo']
        
        # Calculate target ELO
        target_elo = base_elo + (max_elo - base_elo) * ((strength - 0.5) / 0.5)
        
        # Select model with closest ELO
        selected_model_row = model_data.loc[(model_data['coding_arena_elo'] >= target_elo)].iloc[0]
    
    else:
        # Use base model when strength is 0.5
        selected_model_row = base_model_row
    
    # Instantiate the selected LLM model
    provider = selected_model_row['provider']
    model_name = selected_model_row['model']
    
    if provider == 'OpenAI':
        llm = ChatOpenAI(model=model_name, temperature=temperature)
    elif provider == 'Anthropic':
        llm = ChatAnthropic(model=model_name, temperature=temperature)
    elif provider == 'Google':
        llm = ChatGoogleGenerativeAI(model=model_name, temperature=temperature)
    else:
        raise ValueError(f"Unsupported provider: {provider}")
    
    # Get token counter
    counter_type = selected_model_row['counter']
    encoder_name = selected_model_row['encoder']
    token_counter = llm_token_counter(counter_type, encoder_name)
    
    # Get costs
    input_cost = selected_model_row['input']
    output_cost = selected_model_row['output']
    
    return llm, token_counter, input_cost, output_cost

# Example usage
if __name__ == "__main__":
    llm, token_counter, input_cost, output_cost = llm_selector(0.7, 0.5)
    print(f"Selected LLM: {llm}")
    print(f"Token Counter: {token_counter}")
    print(f"Input Cost: {input_cost} per million tokens")
    print(f"Output Cost: {output_cost} per million tokens")