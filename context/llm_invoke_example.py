import os
import sys
from typing import List, Optional
from pydantic import BaseModel, Field
from rich.console import Console

# Ensure the package is in the python path for this example
# In a real installation, this would just be 'from pdd.llm_invoke import llm_invoke'
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.llm_invoke import llm_invoke

console = Console()

# --- Example 1: Simple Text Generation ---
def example_simple_text():
    console.print("[bold blue]--- Example 1: Simple Text Generation ---[/bold blue]")
    
    # Define a prompt template
    prompt_template = "Explain the concept of {concept} to a {audience} in one sentence."
    
    # Define input variables
    input_data = {
        "concept": "quantum entanglement",
        "audience": "5-year-old"
    }

    # Invoke the LLM
    # strength=0.5 targets the 'base' model (usually a balance of cost/performance)
    result = llm_invoke(
        prompt=prompt_template,
        input_json=input_data,
        strength=0.5,
        temperature=0.7,
        verbose=True  # Set to True to see detailed logs about model selection and cost
    )

    console.print(f"[green]Result:[/green] {result['result']}")
    console.print(f"[dim]Model used: {result['model_name']} | Cost: ${result['cost']:.6f}[/dim]\n")


# --- Example 2: Structured Output with Pydantic ---
class MovieReview(BaseModel):
    title: str = Field(..., description="The title of the movie")
    rating: int = Field(..., description="Rating out of 10")
    summary: str = Field(..., description="A brief summary of the plot")
    tags: List[str] = Field(..., description="List of genre tags")

def example_structured_output():
    console.print("[bold blue]--- Example 2: Structured Output (Pydantic) ---[/bold blue]")

    prompt = "Generate a review for a fictional sci-fi movie about {topic}."
    input_data = {"topic": "time traveling cats"}

    # Invoke with output_pydantic to enforce a schema
    # strength=0.8 targets a higher-performance model (better at following schemas)
    result = llm_invoke(
        prompt=prompt,
        input_json=input_data,
        strength=0.8,
        output_pydantic=MovieReview,
        temperature=0.5
    )

    # The 'result' key will contain an instance of the Pydantic model
    review: MovieReview = result['result']
    
    console.print(f"[green]Title:[/green] {review.title}")
    console.print(f"[green]Rating:[/green] {review.rating}/10")
    console.print(f"[green]Tags:[/green] {', '.join(review.tags)}")
    console.print(f"[dim]Model used: {result['model_name']}[/dim]\n")


# --- Example 3: Batch Processing ---
def example_batch_processing():
    console.print("[bold blue]--- Example 3: Batch Processing ---[/bold blue]")

    prompt = "What is the capital of {country}?"
    
    # List of inputs triggers batch mode
    batch_inputs = [
        {"country": "France"},
        {"country": "Japan"},
        {"country": "Brazil"}
    ]

    # use_batch_mode=True uses the provider's batch API if available/supported by LiteLLM
    # strength=0.2 targets a cheaper/faster model
    results = llm_invoke(
        prompt=prompt,
        input_json=batch_inputs,
        use_batch_mode=True,
        strength=0.2,
        temperature=0.1
    )

    # In batch mode, 'result' is a list of strings (or objects)
    for i, res in enumerate(results['result']):
        console.print(f"[green]Input:[/green] {batch_inputs[i]['country']} -> [green]Output:[/green] {res}")
    
    console.print(f"[dim]Model used: {results['model_name']} | Total Cost: ${results['cost']:.6f}[/dim]\n")


# --- Example 4: Reasoning / Thinking Time ---
def example_reasoning():
    console.print("[bold blue]--- Example 4: Reasoning / Thinking Time ---[/bold blue]")

    # Some models (like Claude 3.7 or OpenAI o1/o3) support explicit thinking steps.
    # Setting time > 0 enables this behavior based on the model's configuration in llm_model.csv.
    
    prompt = "Solve this riddle: {riddle}"
    input_data = {"riddle": "I speak without a mouth and hear without ears. I have no body, but I come alive with wind. What am I?"}

    result = llm_invoke(
        prompt=prompt,
        input_json=input_data,
        strength=1.0,  # Target highest capability model
        time=0.5,      # Request moderate thinking time/budget
        verbose=True
    )

    console.print(f"[green]Answer:[/green] {result['result']}")
    
    # If the model supports it, thinking output is captured separately
    if result.get('thinking_output'):
        console.print(f"[yellow]Thinking Process:[/yellow] {result['thinking_output']}")
    else:
        console.print("[dim]No separate thinking output returned for this model.[/dim]")


if __name__ == "__main__":
    # Ensure you have a valid .env file or environment variables set for API keys
    # (e.g., OPENAI_API_KEY, ANTHROPIC_API_KEY)
    
    try:
        example_simple_text()
        example_structured_output()
        example_batch_processing()
        example_reasoning()
    except Exception as e:
        console.print(f"[bold red]Error running examples:[/bold red] {e}")