# llm_invoke.py

import os
import csv
import json
from pydantic import BaseModel, Field
from rich import print as rprint

from langchain_core.prompts import PromptTemplate, ChatPromptTemplate
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.output_parsers import PydanticOutputParser, StrOutputParser
from langchain_core.runnables import RunnablePassthrough, ConfigurableField

from langchain_openai import AzureChatOpenAI
from langchain_fireworks import Fireworks
from langchain_anthropic import ChatAnthropic
from langchain_openai import ChatOpenAI  # Chatbot and conversational tasks
from langchain_openai import OpenAI  # General language tasks
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_groq import ChatGroq
from langchain_together import Together
from langchain_ollama.llms import OllamaLLM

from langchain.callbacks.base import BaseCallbackHandler
from langchain.schema import LLMResult

# import logging

# Configure logging to output to the console
# logging.basicConfig(level=logging.DEBUG)

# Get the LangSmith logger
# langsmith_logger = logging.getLogger("langsmith")

# Set its logging level to DEBUG
# langsmith_logger.setLevel(logging.DEBUG)

class CompletionStatusHandler(BaseCallbackHandler):
    def __init__(self):
        self.is_complete = False
        self.finish_reason = None
        self.input_tokens = None
        self.output_tokens = None

    def on_llm_end(self, response: LLMResult, **kwargs) -> None:
        self.is_complete = True
        if response.generations and response.generations[0]:
            generation = response.generations[0][0]
            self.finish_reason = generation.generation_info.get('finish_reason', "").lower()

            # Extract token usage
            if hasattr(generation.message, 'usage_metadata'):
                usage_metadata = generation.message.usage_metadata
                self.input_tokens = usage_metadata.get('input_tokens')
                self.output_tokens = usage_metadata.get('output_tokens')


class ModelInfo:
    def __init__(self, provider, model, input_cost, output_cost, coding_arena_elo,
                 base_url, api_key, counter, encoder, max_tokens, max_completion_tokens,
                 structured_output):
        self.provider = provider.strip()
        self.model = model.strip()
        self.input_cost = float(input_cost) if input_cost else 0.0
        self.output_cost = float(output_cost) if output_cost else 0.0
        self.average_cost = (self.input_cost + self.output_cost) / 2
        self.coding_arena_elo = float(coding_arena_elo) if coding_arena_elo else 0.0
        self.base_url = base_url.strip() if base_url else None
        self.api_key = api_key.strip() if api_key else None
        self.counter = counter.strip() if counter else None
        self.encoder = encoder.strip() if encoder else None
        self.max_tokens = int(max_tokens) if max_tokens else None
        self.max_completion_tokens = int(
            max_completion_tokens) if max_completion_tokens else None
        self.structured_output = structured_output.lower(
        ) == 'true' if structured_output else False


def load_models():
    PDD_PATH = os.environ.get('PDD_PATH', '.')
    # Assume that llm_model.csv is in PDD_PATH/data
    models_file = os.path.join(PDD_PATH, 'data', 'llm_model.csv')
    models = []
    try:
        with open(models_file, newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                model_info = ModelInfo(
                    provider=row['provider'],
                    model=row['model'],
                    input_cost=row['input'],
                    output_cost=row['output'],
                    coding_arena_elo=row['coding_arena_elo'],
                    base_url=row['base_url'],
                    api_key=row['api_key'],
                    counter=row['counter'],
                    encoder=row['encoder'],
                    max_tokens=row['max_tokens'],
                    max_completion_tokens=row['max_completion_tokens'],
                    structured_output=row['structured_output']
                )
                models.append(model_info)
    except FileNotFoundError:
        raise FileNotFoundError(f"llm_model.csv not found at {models_file}")
    return models


def select_model(strength, models, base_model_name):
    # Get the base model
    base_model = None
    for model in models:
        if model.model == base_model_name:
            base_model = model
            break
    if not base_model:
        raise ValueError(f"Base model {base_model_name} not found in the models list.")

    if strength == 0.5:
        return base_model
    elif strength < 0.5:
        # Models cheaper than or equal to the base model
        cheaper_models = [
            model for model in models if model.average_cost <= base_model.average_cost]
        # Sort models by average_cost ascending
        cheaper_models.sort(key=lambda m: m.average_cost)
        if not cheaper_models:
            return base_model
        # Interpolate between cheapest model and base model
        cheapest_model = cheaper_models[0]
        cost_range = base_model.average_cost - cheapest_model.average_cost
        target_cost = cheapest_model.average_cost + (strength / 0.5) * cost_range
        # Find the model with closest average cost to target_cost
        selected_model = min(
            cheaper_models, key=lambda m: abs(m.average_cost - target_cost))
        return selected_model
    else:
        # strength > 0.5
        # Models better than or equal to the base model
        better_models = [
            model for model in models if model.coding_arena_elo >= base_model.coding_arena_elo]
        # Sort models by coding_arena_elo ascending
        better_models.sort(key=lambda m: m.coding_arena_elo)
        if not better_models:
            return base_model
        # Interpolate between base model and highest ELO model
        highest_elo_model = better_models[-1]
        elo_range = highest_elo_model.coding_arena_elo - base_model.coding_arena_elo
        target_elo = base_model.coding_arena_elo + \
            ((strength - 0.5) / 0.5) * elo_range
        # Find the model with closest ELO to target_elo
        selected_model = min(
            better_models, key=lambda m: abs(m.coding_arena_elo - target_elo))
        return selected_model


def create_llm_instance(selected_model, temperature, handler):
    provider = selected_model.provider.lower()
    model_name = selected_model.model
    base_url = selected_model.base_url
    api_key_name = selected_model.api_key
    max_completion_tokens = selected_model.max_completion_tokens
    max_tokens = selected_model.max_tokens

    # Retrieve API key from environment variable if needed
    api_key = os.environ.get(api_key_name) if api_key_name else None

    # Initialize the appropriate LLM class
    if provider == 'openai':
        if base_url:
            llm = ChatOpenAI(model=model_name, temperature=temperature,
                                openai_api_key=api_key, callbacks=[handler], openai_api_base = base_url)
        else:
            if model_name[0] == 'o':
                llm = ChatOpenAI(model=model_name, temperature=temperature,
                    openai_api_key=api_key, callbacks=[handler], 
                    model_kwargs = {'reasoning_effort':'high'})
            else:
                llm = ChatOpenAI(model=model_name, temperature=temperature,
                                openai_api_key=api_key, callbacks=[handler])
    elif provider == 'anthropic':
        llm = ChatAnthropic(model=model_name, temperature=temperature,
                            callbacks=[handler])
    elif provider == 'google':
        llm = ChatGoogleGenerativeAI(
            model=model_name, temperature=temperature, callbacks=[handler])
    elif provider == 'ollama':
        llm =  OllamaLLM(
            model=model_name, temperature=temperature, callbacks=[handler])
    elif provider == 'azure':
        llm = AzureChatOpenAI(
            model=model_name, temperature=temperature, callbacks=[handler])
    elif provider == 'fireworks':
        llm = Fireworks(model=model_name, temperature=temperature,
                        callbacks=[handler])
    elif provider == 'together':
        llm = Together(model=model_name, temperature=temperature,
                       callbacks=[handler])
    elif provider == 'groq':
        llm = ChatGroq(model_name=model_name, temperature=temperature,
                       callbacks=[handler])
    else:
        raise ValueError(f"Unsupported provider: {selected_model.provider}")
    if max_completion_tokens:
         llm.model_kwargs = {"max_completion_tokens" : max_completion_tokens}
    else:
        # Set max tokens if available
        if max_tokens:
            if provider == 'google':
                llm.max_output_tokens = max_tokens
            else:
                llm.max_tokens = max_tokens
    return llm


def calculate_cost(handler, selected_model):
    input_tokens = handler.input_tokens or 0
    output_tokens = handler.output_tokens or 0
    input_cost_per_million = selected_model.input_cost
    output_cost_per_million = selected_model.output_cost
    # Cost is (tokens / 1_000_000) * cost_per_million
    total_cost = (input_tokens / 1_000_000) * input_cost_per_million + \
        (output_tokens / 1_000_000) * output_cost_per_million
    return total_cost


def llm_invoke(prompt, input_json, strength, temperature, verbose=False, output_pydantic=None):
    # Validate inputs
    if not prompt:
        raise ValueError("Prompt is required.")
    if input_json is None:
        raise ValueError("Input JSON is required.")
    if not isinstance(input_json, dict):
        raise ValueError("Input JSON must be a dictionary.")

    # Set up cache
    set_llm_cache(SQLiteCache(database_path=".langchain.db"))

    # Get default model
    base_model_name = os.environ.get('PDD_MODEL_DEFAULT', 'gpt-4o-mini')

    # Load models
    models = load_models()

    # Select model
    selected_model = select_model(strength, models, base_model_name)

    # Create the prompt template
    try:
        prompt_template = PromptTemplate.from_template(prompt)
    except Exception as e:
        raise ValueError(f"Invalid prompt template: {str(e)}")

    # Create a handler to capture token counts
    handler = CompletionStatusHandler()

    # Prepare LLM instance
    llm = create_llm_instance(selected_model, temperature, handler)

    # Handle structured output if output_pydantic is provided
    if output_pydantic:
        pydantic_model = output_pydantic
        parser = PydanticOutputParser(pydantic_object=pydantic_model)
        # Handle models that support structured output
        if selected_model.structured_output:
            llm = llm.with_structured_output(pydantic_model)
            chain = prompt_template | llm
        else:
            # Use parser after the LLM
            chain = prompt_template | llm | parser
    else:
        # Output is a string
        chain = prompt_template | llm | StrOutputParser()

    # Run the chain
    try:
        result = chain.invoke(input_json)
    except Exception as e:
        raise RuntimeError(f"Error during LLM invocation: {str(e)}")

    # Calculate cost
    cost = calculate_cost(handler, selected_model)

    # If verbose, print information
    if verbose:
        rprint(f"Selected model: {selected_model.model}")
        rprint(
            f"Per input token cost: ${selected_model.input_cost} per million tokens")
        rprint(
            f"Per output token cost: ${selected_model.output_cost} per million tokens")
        rprint(f"Number of input tokens: {handler.input_tokens}")
        rprint(f"Number of output tokens: {handler.output_tokens}")
        rprint(f"Cost of invoke run: ${cost}")
        rprint(f"Strength used: {strength}")
        rprint(f"Temperature used: {temperature}")
        try:
            rprint(f"Input JSON: {input_json}")
        except:
            print(f"Input JSON: {input_json}")
        if output_pydantic:
            rprint(f"Output Pydantic: {output_pydantic}")
        rprint(f"Result: {result}")

    return {'result': result, 'cost': cost, 'model_name': selected_model.model}
