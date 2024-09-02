from pdd.xml_tagger import xml_tagger
from rich import print as rprint

# Example usage
raw_prompt = "Write a story about a magical forest"
strength = 0.5  # Strength parameter for the LLM model (0 = cheapest, 0.5 = base, 1 = highest ELO)
temperature = 0.7  # Temperature parameter for the LLM model (0.0 to 1.0)

try:
    xml_tagged, total_cost, model_name = xml_tagger(raw_prompt, strength, temperature)
    
    rprint("[bold green]XML Tagging completed successfully![/bold green]")
    rprint(f"[bold]XML Tagged Prompt:[/bold]\n{xml_tagged}")
    rprint(f"[bold]Total cost: ${total_cost:.6f}[/bold]")
    rprint(f"[bold]Model used: {model_name}[/bold]")
except Exception as e:
    rprint(f"[bold red]Error: {str(e)}[/bold red]")