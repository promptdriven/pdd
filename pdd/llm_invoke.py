import os
import json
import csv
from typing import Optional, Dict, Any, Tuple
from pathlib import Path

from rich import print as rprint
from rich.console import Console
from rich.traceback import install

from langchain.prompts import PromptTemplate, ChatPromptTemplate
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.output_parsers import JsonOutputParser, StrOutputParser
from langchain_openai import AzureChatOpenAI
from langchain_fireworks import Fireworks 
from langchain_anthropic import ChatAnthropic
from langchain_openai import ChatOpenAI # Chatbot and conversational tasks
from langchain_openai import OpenAI # General language tasks
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_groq import ChatGroq
from langchain_together import Together
from langchain.callbacks.base import BaseCallbackHandler
from langchain.schema import LLMResult
from pydantic import BaseModel, Field

# Enable Rich traceback for better error messages
install()
console = Console()


class CompletionStatusHandler(BaseCallbackHandler):
    """
    Callback handler to capture token usage and completion status.
    """
    def __init__(self):
        self.is_complete = False
        self.finish_reason = None
        self.input_tokens = 0
        self.output_tokens = 0

    def on_llm_end(self, response: LLMResult, **kwargs) -> None:
        self.is_complete = True
        if response.generations and response.generations[0]:
            generation = response.generations[0][0]
            self.finish_reason = generation.generation_info.get('finish_reason', 'unknown').lower()
            
            # More robust token usage extraction
            if hasattr(response, 'llm_output') and response.llm_output:
                usage = response.llm_output.get('token_usage', {})
                self.input_tokens = usage.get('prompt_tokens', 0)
                self.output_tokens = usage.get('completion_tokens', 0)
            elif hasattr(generation, 'message'):
                # Try different metadata locations
                usage = (getattr(generation.message, 'metadata', {}) or {}).get('usage', {})
                self.input_tokens = usage.get('prompt_tokens', 0)
                self.output_tokens = usage.get('completion_tokens', 0)
        # Debug information
        console.print("[bold green]CompletionStatusHandler[/bold green] extracted information:")
        console.print(f"Finish reason: {self.finish_reason}")
        console.print(f"Input tokens: {self.input_tokens}")
        console.print(f"Output tokens: {self.output_tokens}")


class ModelConfig(BaseModel):
    provider: str
    model: str
    input_cost: Optional[float] = 0.0  # Cost per million input tokens
    output_cost: Optional[float] = 0.0  # Cost per million output tokens
    coding_arena_elo: Optional[int] = 0
    base_url: Optional[str] = None
    api_key: Optional[str] = None
    counter: Optional[str] = None
    encoder: Optional[str] = None
    max_tokens: Optional[int] = None
    max_completion_tokens: Optional[int] = None


def load_model_configs(csv_path: Path) -> Dict[str, ModelConfig]:
    """
    Load model configurations from a CSV file.
    Returns a dictionary mapping model names to ModelConfig objects.
    """
    models = {}
    try:
        with csv_path.open(mode='r', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            for row in reader:
                model_name = row.get('model')
                if not model_name:
                    continue  # Skip rows without a model name
                models[model_name] = ModelConfig(
                    provider=row.get('provider', '').strip(),
                    model=model_name.strip(),
                    input_cost=float(row.get('input', 0)) if row.get('input') else 0.0,
                    output_cost=float(row.get('output', 0)) if row.get('output') else 0.0,
                    coding_arena_elo=int(row.get('coding_arena_elo', 0)) if row.get('coding_arena_elo') else 0,
                    base_url=row.get('base_url', '').strip(),
                    api_key=row.get('api_key', '').strip(),
                    counter=row.get('counter', '').strip(),
                    encoder=row.get('encoder', '').strip(),
                    max_tokens=int(row.get('max_tokens')) if row.get('max_tokens') else None,
                    max_completion_tokens=int(row.get('max_completion_tokens')) if row.get('max_completion_tokens') else None,
                )
        if not models:
            raise ValueError("No valid models found in the CSV file.")
        return models
    except FileNotFoundError:
        raise FileNotFoundError(f"Model configuration CSV not found at path: {csv_path}")
    except Exception as e:
        raise Exception(f"Error loading model configurations: {str(e)}")


def select_model(
    models: Dict[str, ModelConfig],
    base_model_name: str,
    strength: float
) -> ModelConfig:
    """
    Selects an appropriate model based on the strength parameter.
    """
    if base_model_name not in models:
        raise ValueError(f"Base model '{base_model_name}' not found in model configurations.")

    base_model = models[base_model_name]

    if strength < 0.0 or strength > 1.0:
        raise ValueError("Strength must be between 0 and 1.")

    if strength == 0.5:
        return base_model
    elif strength < 0.5:
        # Interpolate based on cost
        cheapest_model = min(models.values(), key=lambda m: m.input_cost + m.output_cost)
        target_cost = base_model.input_cost + base_model.output_cost
        target_cost -= (base_model.input_cost + base_model.output_cost - (cheapest_model.input_cost + cheapest_model.output_cost)) * (strength / 0.5)
        # Select model with closest average cost to target_cost
        selected = min(
            models.values(),
            key=lambda m: abs((m.input_cost + m.output_cost) - target_cost)
        )
    else:
        # Interpolate based on ELO
        highest_elo = max(models.values(), key=lambda m: m.coding_arena_elo).coding_arena_elo
        target_elo = base_model.coding_arena_elo + (highest_elo - base_model.coding_arena_elo) * ((strength - 0.5) / 0.5)
        # Select model with closest ELO to target_elo
        selected = min(
            models.values(),
            key=lambda m: abs(m.coding_arena_elo - target_elo)
        )
    return selected


def calculate_cost(
    model: ModelConfig,
    input_tokens: int,
    output_tokens: int
) -> float:
    """
    Calculate the cost of the invocation based on token usage and model's token costs.
    """
    input_cost = model.input_cost if model.input_cost else 0.0
    output_cost = model.output_cost if model.output_cost else 0.0
    cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000
    return cost


def instantiate_llm(
    model: ModelConfig,
    temperature: float,
) -> Any:
    """
    Instantiate the appropriate LLM based on the model configuration.
    """
    llm_kwargs = {
        "temperature": temperature,
    }

    # Add max_tokens and max_completions if available
    if model.max_tokens:
        llm_kwargs["max_tokens"] = model.max_tokens
    if model.max_completion_tokens:
        llm_kwargs["max_completions"] = model.max_completion_tokens

    handler = CompletionStatusHandler()

    if model.provider.lower() == "openai":
        llm = ChatOpenAI(
            model=model.model,
            temperature=temperature,
            callbacks=[handler]
        )
    elif model.provider.lower() == "azure":
        if not model.api_key:
            raise ValueError(f"API key not provided for Azure model '{model.model}'.")
        llm = AzureChatOpenAI(
            model=model.model,
            temperature=temperature,
            openai_api_key=model.api_key,
            openai_api_base=model.base_url,
            callbacks=[handler]
        )
    elif model.provider.lower() == "anthropic":
        llm = ChatAnthropic(
            model=model.model,
            temperature=temperature,
            callbacks=[handler]
        )
    elif model.provider.lower() == "google":
        llm = ChatGoogleGenerativeAI(
            model=model.model,
            temperature=temperature,
            callbacks=[handler]
        )
    elif model.provider.lower() == "fireworks":
        llm = Fireworks(
            model=model.model,
            temperature=temperature,
            callbacks=[handler]
        )
    elif model.provider.lower() == "groq":
        llm = ChatGroq(
            model_name=model.model,
            temperature=temperature,
            callbacks=[handler]
        )
    elif model.provider.lower() == "together":
        llm = Together(
            model=model.model,
            temperature=temperature,
            max_tokens=model.max_tokens if model.max_tokens else 500,
            callbacks=[handler]
        )
    else:
        raise ValueError(f"Unsupported provider '{model.provider}' for model '{model.model}'.")

    return llm, handler


def llm_invoke(
    prompt: str,
    input_json: Dict[str, Any],
    strength: float,
    temperature: float,
    verbose: bool,
    output_json: Optional[Dict[str, Any]] = None
) -> Dict[str, Any]:
    """
    Invoke an LLM model with the given prompt and parameters.

    Parameters:
        prompt (str): The prompt template.
        input_json (dict): Input variables for the prompt.
        strength (float): Model selection strength between 0 and 1.
        temperature (float): Temperature for the LLM.
        verbose (bool): If True, print detailed information.
        output_json (dict, optional): Desired output JSON structure.

    Returns:
        dict: Contains 'result', 'cost', and 'model_name'.
    """
    try:
        # Validate inputs
        if not isinstance(prompt, str) or not prompt.strip():
            raise ValueError("The 'prompt' must be a non-empty string.")
        if not isinstance(input_json, dict):
            raise ValueError("The 'input_json' must be a dictionary.")
        if not isinstance(strength, float) or not (0.0 <= strength <= 1.0):
            raise ValueError("The 'strength' must be a float between 0 and 1.")
        if not isinstance(temperature, float):
            raise ValueError("The 'temperature' must be a float.")
        if not isinstance(verbose, bool):
            raise ValueError("The 'verbose' must be a boolean.")
        if output_json is not None and not isinstance(output_json, dict):
            raise ValueError("The 'output_json' must be a dictionary if provided.")

        # Setup Langchain cache
        set_llm_cache(SQLiteCache(database_path=".langchain.db"))

        # Load model configurations
        pdd_path = Path(os.getenv('PDD_PATH', '.'))
        csv_path = pdd_path / 'data' / 'llm_model.csv' if pdd_path.exists() else Path.cwd() / 'llm_model.csv'
        models = load_model_configs(csv_path)

        # Determine base model
        base_model_name = os.getenv('PDD_MODEL_DEFAULT', 'gpt-4o-mini')
        base_model = models.get(base_model_name)
        if not base_model:
            raise ValueError(f"Base model '{base_model_name}' not found in model configurations.")

        # Select appropriate model
        selected_model = select_model(models, base_model_name, strength)

        # Instantiate the LLM
        llm, handler = instantiate_llm(selected_model, temperature)

        # Create PromptTemplate
        if output_json:
            parser = JsonOutputParser()
            # Escape JSON structure in prompt by replacing { with {{ and } with }}
            json_structure = json.dumps(output_json, indent=2).replace("{", "{{").replace("}", "}}");
            formatted_prompt = f"""
                Respond with JSON matching this structure:
                {json_structure}

                {prompt}
            """
            prompt_template = ChatPromptTemplate.from_messages([
                ("system", "You are a helpful assistant that always responds in valid JSON format."),
                ("user", formatted_prompt)
            ])
        else:
            parser = StrOutputParser()
            prompt_template = PromptTemplate(
                template=prompt,
                input_variables=list(input_json.keys())
            )

        # Combine prompt and LLM
        chain = prompt_template | llm | parser

        # Invoke the chain
        result = chain.invoke(input_json)

        # Calculate cost
        cost = calculate_cost(selected_model, handler.input_tokens, handler.output_tokens)

        # Prepare output
        output = {
            "result": result,
            "cost": cost,
            "model_name": selected_model.model
        }

        # Verbose output
        if verbose:
            rprint("[bold blue]Verbose Output[/bold blue]")
            rprint(f"Selected Model: [green]{selected_model.model}[/green]")
            rprint(f"Input Token Cost: ${selected_model.input_cost} per million tokens")
            rprint(f"Output Token Cost: ${selected_model.output_cost} per million tokens")
            rprint(f"Input Tokens Used: {handler.input_tokens}")
            rprint(f"Output Tokens Used: {handler.output_tokens}")
            rprint(f"Total Cost: ${cost:.6f}")
            rprint(f"Strength Used: {strength}")
            rprint(f"Temperature Used: {temperature}")
            rprint(f"Input JSON: {json.dumps(input_json, indent=2)}")
            if output_json:
                rprint(f"Output JSON Structure: {json.dumps(output_json, indent=2)}")
            rprint(f"Result: [bold]{result}[/bold]")

        return output

    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}")
        raise
