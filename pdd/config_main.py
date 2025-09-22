from __future__ import annotations

import os
import sys
from pathlib import Path
import click
from rich.console import Console
import pandas as pd

# --- Initialize Rich Console ---
console = Console()

def discover_api_keys() -> dict[str, str]:
    """Discovers API keys from environment variables."""
    keys = {}
    # Sort the environment keys to ensure deterministic order for tests
    for key in sorted(os.environ.keys()):
        if key.endswith("_API_KEY"):
            keys[key] = os.environ[key]
    return keys

def config_main(directory: str | None) -> tuple[str, float, str]:
    """Main logic for the config command."""
    if directory:
        target_dir = Path(directory)
    else:
        target_dir = Path.cwd()

    pdd_dir = target_dir / ".pdd"
    pdd_dir.mkdir(exist_ok=True)

    console.print(f"PDD configuration directory is at: [bold cyan]{pdd_dir.resolve()}[/bold cyan]")

    api_keys = discover_api_keys()
    selected_keys = {}

    if api_keys:
        console.print("\nFound API keys in your environment variables:")
        for key_name in sorted(api_keys.keys()):
            if click.confirm(f"  Do you want to use the API key stored in [bold yellow]{key_name}[/bold yellow]?", default=True):
                selected_keys[key_name] = api_keys[key_name]
    else:
        console.print("\nNo API keys found in your environment variables.")

    # If no keys were selected from environment, then ask for manual entry.
    if not selected_keys:
        if click.confirm("Do you want to enter API keys manually?", default=True):
            while True:
                provider = click.prompt("Enter the provider name (e.g., OpenAI, Google, Anthropic), or leave blank to finish", default="", show_default=False)
                if not provider:
                    break
                api_key_value = click.prompt(f"Enter the API key for {provider}", hide_input=True)
                
                # Map provider to a standard environment variable name
                if provider.upper() == "GOOGLE":
                    key_name = "GEMINI_API_KEY"
                else:
                    key_name = f"{provider.upper()}_API_KEY"
                selected_keys[key_name] = api_key_value

    if not selected_keys:
        console.print("[bold red]No API keys were selected or provided. Exiting.[/bold red]")
        sys.exit(1)

    # Read the master llm_model.csv
    try:
        pdd_module_path = Path(__file__).parent.resolve()
        master_csv_path = pdd_module_path / "data" / "llm_model.csv"
        if not master_csv_path.exists():
            console.print(f"[bold red]Error: Master llm_model.csv not found at {master_csv_path}[/bold red]")
            sys.exit(1)
        
        df = pd.read_csv(master_csv_path)
    except Exception as e:
        console.print(f"[bold red]Error reading master llm_model.csv: {e}[/bold red]")
        sys.exit(1)

    # Filter the DataFrame based on the selected API keys
    # The 'api_key' column in the CSV holds the environment variable *name*
    filtered_df = df[df['api_key'].isin(selected_keys.keys())]

    if filtered_df.empty:
        console.print("[bold yellow]Warning: None of the selected API keys correspond to models in the master list.[/bold yellow]")
        console.print("[bold yellow]An empty llm_model.csv will be created.[/bold yellow]")

    # Write the new llm_model.csv
    output_csv_path = pdd_dir / "llm_model.csv"
    try:
        filtered_df.to_csv(output_csv_path, index=False)
        console.print(f"\n[bold green]Successfully created configuration file:[/bold green] {output_csv_path.resolve()}")
        
        # Also create the api-env file for sourcing, but only with keys that are in the filtered csv
        api_env_content = ""
        final_keys_to_write = {key: selected_keys[key] for key in filtered_df['api_key'].unique() if key in selected_keys}

        for key, value in final_keys_to_write.items():
            api_env_content += f'export {key}="{value}"\n'
        
        api_env_file = pdd_dir / "api-env"
        api_env_file.write_text(api_env_content)
        console.print(f"[bold green]Successfully created environment file:[/bold green] {api_env_file.resolve()}")
        console.print("\nTo use these keys in your current session, run:")
        console.print(f"[bold cyan]  source {api_env_file.resolve()}[/bold cyan]")

    except Exception as e:
        console.print(f"[bold red]Error writing configuration file: {e}[/bold red]")
        sys.exit(1)
        
    return "Configuration successful", 0.0, "local"