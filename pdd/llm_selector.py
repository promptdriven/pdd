import os
import pandas as pd
from langchain_openai import ChatOpenAI
from langchain_anthropic import ChatAnthropic
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_fireworks import Fireworks
from langchain_groq import ChatGroq
from langchain_together import Together
from .llm_token_counter import llm_token_counter
# Always setup cache to save money and increase speeds
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
set_llm_cache(SQLiteCache(database_path=".langchain.db"))


def llm_selector(strength: float, temperature: float):
    """
    Selects an appropriate Langchain LLM model based on the given strength and temperature.

    :param strength: A float representing the desired strength of the model.
    :param temperature: A float representing the desired temperature for the model.
    :return: A tuple containing the selected LLM, token counter function, input cost, output cost, and model name.
    """
    # Load environment variables
    base_model = os.getenv('PDD_MODEL_DEFAULT', 'gpt-4o-mini')
    pdd_path = os.getenv('PDD_PATH', os.getcwd())
    csv_path = os.path.join(pdd_path, 'data', 'llm_model.csv')
    
    # Load the CSV file
    try:
        df = pd.read_csv(csv_path)
    except FileNotFoundError:
        raise FileNotFoundError(f"CSV file not found at path: {csv_path}")

    # Find the base model details
    try:
        base_model_row = df[df['model'] == base_model].iloc[0]
    except IndexError:
        raise ValueError(f"Base model '{base_model}' not found in CSV.")

    base_input_cost = base_model_row['input']
    base_output_cost = base_model_row['output']
    base_elo = base_model_row['coding_arena_elo']

      # Calculate average costs for all models
    df['average_cost'] = (df['input'] + df['output']) / 2

    if strength < 0.5:
        # Interpolate based on cost
        cheapest_model_row = df.loc[df['average_cost'].idxmin()]
        target_cost = base_input_cost + (cheapest_model_row['average_cost'] - base_input_cost) * (strength / 0.5)
        selected_row = df.iloc[(df['average_cost'] - target_cost).abs().argsort()[:1]].squeeze()
    elif strength > 0.5:
        # Interpolate based on ELO
        highest_elo_row = df.loc[df['coding_arena_elo'].idxmax()]
        target_elo = base_elo + (highest_elo_row['coding_arena_elo'] - base_elo) * ((strength - 0.5) / 0.5)
        selected_row = df.iloc[(df['coding_arena_elo'] - target_elo).abs().argsort()[:1]].squeeze()
    else:
        # Use base model
        selected_row = base_model_row

    # Calculate average cost for the selected row
    selected_row_average_cost = (selected_row['input'] + selected_row['output']) / 2

    # Check for models with higher ELO but lower or equal cost
    higher_elo_models = df[(df['coding_arena_elo'] >= selected_row['coding_arena_elo']) & 
                           (df['average_cost'] <= selected_row_average_cost)]
    
    if not higher_elo_models.empty:
        selected_row = higher_elo_models.iloc[0]


    # Extract model details
    model_name = selected_row['model']
    provider = selected_row['provider']
    input_cost = selected_row['input']
    output_cost = selected_row['output']
    counter_type = selected_row['counter']
    encoder = selected_row['encoder']

    # Instantiate the LLM model
    if provider == 'OpenAI':
        llm = ChatOpenAI(model=model_name, temperature=temperature)#, max_completion_tokens=16384)
    elif provider == 'Anthropic':
        llm = ChatAnthropic(model=model_name, temperature=temperature, max_tokens=8192)
    elif provider == 'Google':
        llm = ChatGoogleGenerativeAI(model=model_name, temperature=temperature, max_tokens=8192)
    elif provider == 'Fireworks':
        llm = Fireworks(model=model_name, temperature=temperature)
    elif provider == 'Groq':
        llm = ChatGroq(model_name=model_name, temperature=temperature)
    elif provider == 'Together':
        llm = Together(model=model_name, temperature=temperature)
    else:
        raise ValueError(f"Unsupported provider: {provider}")

    # Get the token counter function
    token_counter = llm_token_counter(counter_type, encoder)
    print(f"Selected LLM: {model_name}, Input Cost: {input_cost}, Output Cost: {output_cost}")
    return llm, token_counter, input_cost, output_cost, model_name  # Return model_name separately

# Example usage
if __name__ == "__main__":
    i = 0
    while i < 1:
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(i, 0)
        print(f"Strength: {i}, Selected LLM: {model_name}, Input Cost: {input_cost}, Output Cost: {output_cost}")
        i += 0.1