# update_model_costs.py

import argparse
import os
import pandas as pd
import litellm
from rich.console import Console
from rich.table import Table
import math # For isnan check, although pd.isna is preferred

# Initialize Rich Console for pretty printing
console = Console()

# Define expected columns in the CSV, including the manually maintained one
EXPECTED_COLUMNS = [
    'provider', 'model', 'input', 'output', 'coding_arena_elo', 'base_url',
    'api_key', 'counter', 'encoder', 'max_tokens', 'max_completion_tokens',
    'max_reasoning_tokens', 'structured_output'
]

# Placeholder for missing numeric values (optional, pd.NA is generally better)
MISSING_VALUE_PLACEHOLDER = -1.0

def update_model_data(csv_path: str) -> None:
    """
    Reads the llm_model.csv file, updates missing costs and structured output
    support using LiteLLM, and saves the updated file.

    Args:
        csv_path (str): The path to the llm_model.csv file.
    """
    console.print(f"[bold blue]Starting model data update for:[/bold blue] {csv_path}")

    # --- 1. Load CSV and Handle Initial Errors ---
    try:
        df = pd.read_csv(csv_path)
        console.print(f"[green]Successfully loaded:[/green] {csv_path}")
    except FileNotFoundError:
        console.print(f"[bold red]Error:[/bold red] CSV file not found at {csv_path}")
        return
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] Failed to load CSV file: {e}")
        return

    # --- 2. Check and Add Missing Columns ---
    updated_schema = False
    for col in EXPECTED_COLUMNS:
        if col not in df.columns:
            updated_schema = True
            console.print(f"[yellow]Warning:[/yellow] Column '{col}' missing. Adding it.")
            if col in ['input', 'output']:
                df[col] = pd.NA # Use pandas NA for missing floats
            elif col == 'structured_output':
                 # Use pandas NA for missing boolean/object, allowing True/False/NA
                df[col] = pd.NA
            elif col == 'max_reasoning_tokens':
                 # Use pandas NA for missing int/float
                df[col] = pd.NA
            else:
                # Default for other potentially missing columns (like max_tokens etc.)
                df[col] = pd.NA # Or appropriate default like 0 or '' if known
    if updated_schema:
        console.print("[cyan]CSV schema updated with missing columns.[/cyan]")

    # Ensure correct dtypes for columns we might fill
    # Convert potential placeholders like -1 to NA before checking pd.isna
    if 'input' in df.columns:
        df['input'] = pd.to_numeric(df['input'], errors='coerce')
    if 'output' in df.columns:
        df['output'] = pd.to_numeric(df['output'], errors='coerce')
    # For structured_output, keep as object to allow True/False/NA
    if 'structured_output' in df.columns:
       # Attempt to convert to boolean, coercing errors (like strings) to NA
       # This handles existing True/False strings or actual booleans
       df['structured_output'] = df['structured_output'].apply(
           lambda x: pd.NA if pd.isna(x) else (
               True if str(x).strip().lower() == 'true' else (
                   False if str(x).strip().lower() == 'false' else pd.NA
               )
           )
       ).astype('object') # Keep as object to hold True, False, pd.NA


    # --- 3. Iterate Through Models and Update ---
    models_updated_count = 0
    models_failed_count = 0
    rows_to_update = []

    console.print("\n[bold blue]Processing models...[/bold blue]")
    table = Table(title="Model Update Status", show_lines=True)
    table.add_column("Model Identifier", style="cyan")
    table.add_column("Cost Update", style="magenta")
    table.add_column("Struct. Output Update", style="yellow")
    table.add_column("Status", style="green")

    # Pre-fetch all model costs from LiteLLM once
    try:
        all_model_costs = litellm.model_cost
        console.print("[green]Successfully fetched LiteLLM model cost data.[/green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] Could not fetch LiteLLM model cost data: {e}")
        all_model_costs = {} # Proceed without cost updates if fetch fails

    for index, row in df.iterrows():
        model_identifier = row['model']
        if pd.isna(model_identifier):
            console.print(f"[yellow]Warning:[/yellow] Skipping row {index} due to missing model identifier.")
            continue

        cost_update_msg = "Checked"
        struct_update_msg = "Checked"
        row_status = "[green]OK[/green]"
        needs_update = False

        # --- 4. Check and Update Costs ---
        input_cost_missing = pd.isna(row['input']) or row['input'] == MISSING_VALUE_PLACEHOLDER
        output_cost_missing = pd.isna(row['output']) or row['output'] == MISSING_VALUE_PLACEHOLDER

        if input_cost_missing or output_cost_missing:
            cost_update_msg = "Attempting fetch..."
            try:
                # Use the pre-fetched dictionary
                cost_data = all_model_costs.get(model_identifier)

                if cost_data:
                    input_cost_per_token = cost_data.get('input_cost_per_token')
                    output_cost_per_token = cost_data.get('output_cost_per_token')

                    updated_costs = []
                    if input_cost_missing and input_cost_per_token is not None:
                        # Convert cost per token to cost per million tokens
                        input_cost_per_million = input_cost_per_token * 1_000_000
                        df.loc[index, 'input'] = input_cost_per_million
                        updated_costs.append(f"Input: {input_cost_per_million:.4f}")
                        needs_update = True

                    if output_cost_missing and output_cost_per_token is not None:
                        # Convert cost per token to cost per million tokens
                        output_cost_per_million = output_cost_per_token * 1_000_000
                        df.loc[index, 'output'] = output_cost_per_million
                        updated_costs.append(f"Output: {output_cost_per_million:.4f}")
                        needs_update = True

                    if updated_costs:
                        cost_update_msg = f"[green]Updated ({', '.join(updated_costs)})[/green]"
                    else:
                         cost_update_msg = "[yellow]No missing costs found/updated[/yellow]"

                else:
                    cost_update_msg = "[yellow]Cost data not found in LiteLLM[/yellow]"
                    row_status = "[yellow]Partial Fail (Cost)[/yellow]"

            except Exception as e:
                cost_update_msg = f"[red]Error fetching costs: {e}[/red]"
                row_status = "[red]Fail (Cost Error)[/red]"
                models_failed_count += 1 # Count failure if cost fetch errors out

        # --- 5. Check and Update Structured Output Support ---
        # Update if 'structured_output' is NA (missing or failed previous conversion)
        struct_output_missing = pd.isna(row['structured_output'])

        if struct_output_missing:
            struct_update_msg = "Attempting check..."
            try:
                # Ensure the model identifier is valid for litellm functions
                # Note: litellm might expect specific formats like 'openai/gpt-4o-mini'
                # The CSV 'model' column MUST contain these valid identifiers.
                supports_schema = litellm.supports_response_schema(model=model_identifier)
                df.loc[index, 'structured_output'] = bool(supports_schema) # Store as True/False
                struct_update_msg = f"[green]Updated ({bool(supports_schema)})[/green]"
                needs_update = True
            except ValueError as ve:
                 # Often indicates model not known to litellm for this check
                 struct_update_msg = f"[yellow]Check failed (Unknown Model?): {ve}[/yellow]"
                 # Leave as NA to indicate uncertainty
                 df.loc[index, 'structured_output'] = pd.NA
                 if row_status == "[green]OK[/green]": # Don't overwrite a cost failure status
                     row_status = "[yellow]Partial Fail (Struct)[/yellow]"
            except Exception as e:
                struct_update_msg = f"[red]Error checking support: {e}[/red]"
                # Leave as NA
                df.loc[index, 'structured_output'] = pd.NA
                if "Fail" not in row_status: # Prioritize showing full failure
                    row_status = "[red]Fail (Struct Error)[/red]"
                models_failed_count += 1 # Count failure if struct check errors out

        if needs_update and "Fail" not in row_status:
             models_updated_count += 1
             if row_status == "[green]OK[/green]": # Only change if previously OK
                 row_status = "[blue]Updated[/blue]"


        table.add_row(model_identifier, cost_update_msg, struct_update_msg, row_status)

    console.print(table)
    console.print(f"\n[bold]Summary:[/bold]")
    console.print(f"- Models processed: {len(df)}")
    console.print(f"- Rows potentially updated: {models_updated_count}")
    # Note: models_failed_count might double count if both cost and struct fail,
    # but gives an idea of how many models had issues.
    # A more precise count would track unique failed models.
    # console.print(f"- Models with fetch/check errors: {models_failed_count}")


    # --- 6. Save Updated DataFrame ---
    if models_updated_count > 0 or updated_schema:
        try:
            # Ensure NA values are saved correctly (as empty strings by default)
            df.to_csv(csv_path, index=False, na_rep='') # Save NA as empty string
            console.print(f"\n[bold green]Successfully saved updated data to:[/bold green] {csv_path}")
        except Exception as e:
            console.print(f"[bold red]Error:[/bold red] Failed to save updated CSV file: {e}")
    else:
        console.print("\n[bold blue]No updates needed or made to the CSV file.[/bold blue]")

    # --- 7. Reminder about Manual Column ---
    console.print(f"\n[bold yellow]Reminder:[/bold yellow] The '{'max_reasoning_tokens'}' column is not automatically updated by this script and requires manual maintenance.")
    console.print(f"[bold blue]Model data update process finished.[/bold blue]")


def main():
    """Main function to parse arguments and run the update process."""
    parser = argparse.ArgumentParser(
        description="Update LLM model costs and structured output support in a CSV file using LiteLLM."
    )
    parser.add_argument(
        "--csv-path",
        type=str,
        default="data/llm_model.csv",
        help="Path to the llm_model.csv file (default: data/llm_model.csv)"
    )
    args = parser.parse_args()

    # Ensure the directory exists if a non-default path is given
    csv_dir = os.path.dirname(args.csv_path)
    if csv_dir and not os.path.exists(csv_dir):
        try:
            os.makedirs(csv_dir)
            console.print(f"[cyan]Created directory:[/cyan] {csv_dir}")
        except OSError as e:
            console.print(f"[bold red]Error:[/bold red] Could not create directory {csv_dir}: {e}")
            return # Exit if directory cannot be created

    update_model_data(args.csv_path)

if __name__ == "__main__":
    # --- Crucial Note ---
    console.print("[bold yellow]Important:[/bold yellow] This script assumes the 'model' column in the CSV contains")
    console.print("           [bold yellow]valid LiteLLM model identifiers[/bold yellow] (e.g., 'openai/gpt-4o-mini',")
    console.print("           'ollama/llama3', 'anthropic/claude-3-haiku-20240307').")
    console.print("           Please verify the identifiers before running.\n")
    main()
