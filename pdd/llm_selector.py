import os
import pandas as pd
from langchain_openai import ChatOpenAI
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_anthropic import ChatAnthropic
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path='.langchain.db'))

def instantiate_llm(provider, model, temperature):
    if provider == 'OpenAI':
        return ChatOpenAI(model=model, temperature=temperature)
    elif provider == 'Google':
        return ChatGoogleGenerativeAI(model=model, temperature=temperature)
    elif provider == 'Anthropic':
        return ChatAnthropic(model=model, temperature=temperature)
    else:
        raise ValueError(f'Unknown provider: {provider}')


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

        # Filter out the base model and check if the resulting DataFrame is empty
        filtered_df = df[df['model'] != base_model]
        if filtered_df.empty:
            selected_model_row = base_model_row
        else:
            selected_model_row = filtered_df.loc[filtered_df['elo_difference'].idxmin()]
    else:
        # Use base model
        selected_model_row = base_model_row
    
    # Instantiate the selected model
    llm = instantiate_llm(selected_model_row['provider'], selected_model_row['model'], temperature)
    print('Selected model:', selected_model_row['model'])
    # Return the model and costs
    return llm, selected_model_row['input'], selected_model_row['output']