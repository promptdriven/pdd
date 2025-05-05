# update_model_costs.py

import argparse
import os
import pandas as pd
import litellm
from rich.console import Console
from rich.table import Table
import math # For isnan check, although pd.isna is preferred
from pathlib import Path

# Initialize Rich Console for pretty printing
console = Console()

# Define expected columns in the CSV, including the manually maintained one
EXPECTED_COLUMNS = [
    'provider', 'model', 'input', 'output', 'coding_arena_elo', 'base_url',
    'api_key',
    'max_reasoning_tokens', 'structured_output'
]

# Define columns that should be nullable integers
INT_COLUMNS = ['coding_arena_elo', 'max_reasoning_tokens']

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
                 # Type will be enforced later
                 df[col] = pd.NA
            elif col in INT_COLUMNS: # Handle other integer columns
                 df[col] = pd.NA # Initialize with NA, enforce type later
            else:
                # Default for other potentially missing columns (like max_tokens etc.)
                df[col] = pd.NA # Or appropriate default like 0 or '' if known
    if updated_schema:
        console.print("[cyan]CSV schema updated with missing columns.[/cyan]")

    # --- 3. Enforce Correct Data Types ---
    # Do this *after* loading and adding any missing columns
    console.print("\n[bold blue]Enforcing data types...[/bold blue]")
    try:
        # Floats (allow NA)
        if 'input' in df.columns:
            df['input'] = pd.to_numeric(df['input'], errors='coerce')
        if 'output' in df.columns:
            df['output'] = pd.to_numeric(df['output'], errors='coerce')

        # Boolean/Object (allow NA)
        if 'structured_output' in df.columns:
            df['structured_output'] = df['structured_output'].apply(
                lambda x: pd.NA if pd.isna(x) else (
                    True if str(x).strip().lower() == 'true' else (
                        False if str(x).strip().lower() == 'false' else pd.NA
                    )
                )
            ).astype('object') # Keep as object to hold True, False, pd.NA

        # Integers (allow NA)
        for col in INT_COLUMNS:
            if col in df.columns:
                # Convert to numeric first (handles strings like '123', errors become NA),
                # then cast to nullable Int64.
                df[col] = pd.to_numeric(df[col], errors='coerce').astype('Int64')
                console.print(f"[cyan]Ensured '{col}' is nullable integer (Int64).[/cyan]")

        console.print("[green]Data types enforced successfully.[/green]")

    except Exception as e:
        console.print(f"[bold red]Error during type enforcement:[/bold red] {e}")
        return # Exit if types can't be enforced correctly

    # Remove older, less robust type handling blocks if they exist
    # (The code originally had some dtype checks spread out, this consolidates them)

    # --- 4. Iterate Through Models and Update ---
    models_updated_count = 0
    models_failed_count = 0
    mismatched_cost_count = 0 # Track mismatches
    # Add a temporary column to track failures directly
    df['_failed'] = False
    rows_to_update = []

    console.print("\n[bold blue]Processing models...[/bold blue]")
    table = Table(title="Model Update Status", show_lines=True)
    table.add_column("Model Identifier", style="cyan")
    table.add_column("Cost Update", style="magenta")
    table.add_column("Struct. Output Update", style="yellow")
    table.add_column("Cost Match", style="blue") # New column for matching status
    table.add_column("Status", style="green")

    # Pre-fetch all model costs from LiteLLM once
    try:
        # Note: litellm.model_cost might need adjustment based on actual usage
        # If it requires specific model names not in the CSV, this might fail.
        # For now, assuming it returns a dict keyed by model names matching the CSV.
        all_model_costs = getattr(litellm, 'model_cost', {}) # Safely get attribute
        if not all_model_costs:
             console.print("[yellow]Warning:[/yellow] Could not fetch or find `litellm.model_cost`. Cost updates might be skipped.")
        else:
            console.print("[green]Successfully fetched LiteLLM model cost data.[/green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] Could not fetch LiteLLM model cost data: {e}")
        all_model_costs = {} # Proceed without cost updates if fetch fails

    for index, row in df.iterrows():
        model_identifier = row['model']
        if pd.isna(model_identifier):
            console.print(f"[yellow]Warning:[/yellow] Skipping row {index} due to missing model identifier.")
            continue

        # --- Cost Comparison Variables ---
        fetched_input_cost = None
        fetched_output_cost = None
        cost_match_status = "[grey]N/A[/grey]" # Default if no litellm data or comparison not possible
        cost_data_available = False

        # --- 5. Initial Model Validation & Schema Check ---
        # Attempt an early check using supports_response_schema.
        # A ValueError here often indicates the model identifier is unknown to litellm.
        is_valid_model = True
        schema_check_result = None # Store result if check succeeds
        struct_check_error = None # Store potential error details

        try:
            # This serves as an initial validation. If it fails with ValueError,
            # we assume the model identifier might be invalid/unknown.
            schema_check_result = litellm.supports_response_schema(model=model_identifier)
        except ValueError as ve:
            is_valid_model = False
            struct_check_error = ve # Store the specific error
            row_status = "[red]Fail (Invalid/Unknown Model?)[/red]"
            cost_update_msg = "[red]Skipped[/red]"
            struct_update_msg = f"[red]Validation Failed: {ve}[/red]"
            df.loc[index, '_failed'] = True
            cost_match_status = "[red]Skipped (Validation Failed)[/red]" # Also skip matching
        except Exception as e:
             # Catch other potential errors during the initial check
             is_valid_model = False # Treat other errors as validation failure too
             struct_check_error = e
             row_status = "[red]Fail (Schema Check Error)[/red]"
             cost_update_msg = "[red]Skipped[/red]"
             struct_update_msg = f"[red]Check Error: {e}[/red]"
             df.loc[index, '_failed'] = True
             cost_match_status = "[red]Skipped (Schema Check Error)[/red]" # Also skip matching

        # If initial validation failed, skip further processing for this row
        if not is_valid_model:
            table.add_row(model_identifier, cost_update_msg, struct_update_msg, cost_match_status, row_status)
            continue

        # --- If validation passed, proceed with cost and struct updates ---
        cost_update_msg = "Checked"
        struct_update_msg = "Checked"
        row_status = "[green]OK[/green]"
        needs_update = False

        # --- 6. Check and Update Costs --- (Renumbered from 5)
        # Always attempt to fetch cost data if available
        cost_data = all_model_costs.get(model_identifier)
        cost_fetch_error = None

        if cost_data:
            cost_data_available = True
            try:
                input_cost_per_token = cost_data.get('input_cost_per_token')
                output_cost_per_token = cost_data.get('output_cost_per_token')

                if input_cost_per_token is not None:
                    fetched_input_cost = input_cost_per_token * 1_000_000
                if output_cost_per_token is not None:
                    fetched_output_cost = output_cost_per_token * 1_000_000

            except Exception as e:
                cost_fetch_error = e
                cost_update_msg = f"[red]Error processing costs: {e}[/red]"
                if "Fail" not in row_status: row_status = "[red]Fail (Cost Error)[/red]"

        # Decide action based on fetched data and existing values
        input_cost_missing = pd.isna(row['input'])
        output_cost_missing = pd.isna(row['output'])

        updated_costs_messages = []
        mismatched_costs_messages = []
        matched_costs_messages = []

        if cost_data_available and not cost_fetch_error:
            # Update Input Cost if missing
            if input_cost_missing and fetched_input_cost is not None:
                df.loc[index, 'input'] = fetched_input_cost
                updated_costs_messages.append(f"Input: {fetched_input_cost:.4f}")
                needs_update = True
            # Compare Input Cost if not missing
            elif not input_cost_missing and fetched_input_cost is not None:
                if not math.isclose(row['input'], fetched_input_cost, rel_tol=1e-6):
                    mismatched_costs_messages.append(f"Input (CSV: {row['input']:.4f}, LLM: {fetched_input_cost:.4f})")
                else:
                    matched_costs_messages.append("Input")

            # Update Output Cost if missing
            if output_cost_missing and fetched_output_cost is not None:
                df.loc[index, 'output'] = fetched_output_cost
                updated_costs_messages.append(f"Output: {fetched_output_cost:.4f}")
                needs_update = True
            # Compare Output Cost if not missing
            elif not output_cost_missing and fetched_output_cost is not None:
                if not math.isclose(row['output'], fetched_output_cost, rel_tol=1e-6):
                    mismatched_costs_messages.append(f"Output (CSV: {row['output']:.4f}, LLM: {fetched_output_cost:.4f})")
                else:
                    matched_costs_messages.append("Output")

            # Set Cost Update Message
            if updated_costs_messages:
                cost_update_msg = f"[green]Updated ({', '.join(updated_costs_messages)})[/green]"
            elif mismatched_costs_messages or matched_costs_messages: # If compared, even if no update
                cost_update_msg = "[blue]Checked (No missing values)[/blue]"
            else: # No cost data in litellm for either input/output
                cost_update_msg = "[yellow]No comparable cost data in LiteLLM[/yellow]"
                if row_status == "[green]OK[/green]": row_status = "[yellow]Info (No Cost Data)[/yellow]"

            # Set Cost Match Status Message
            if mismatched_costs_messages:
                cost_match_status = f"[bold red]Mismatch! ({', '.join(mismatched_costs_messages)})[/bold red]"
                mismatched_cost_count += 1 # Increment mismatch counter
            elif matched_costs_messages:
                cost_match_status = f"[green]Match ({', '.join(matched_costs_messages)})[/green]"
            elif updated_costs_messages: # If costs were updated, they now 'match'
                 cost_match_status = f"[blue]N/A (Updated)[/blue]"
            else: # If no costs existed to compare (e.g., LLM has no cost data)
                cost_match_status = "[grey]N/A (No LLM Data)[/grey]"

        elif cost_fetch_error:
            cost_match_status = "[red]Error during fetch[/red]"

        elif not cost_data_available:
            cost_update_msg = "[yellow]Cost data not found in LiteLLM[/yellow]"
            cost_match_status = "[grey]N/A (No LLM Data)[/grey]"
            if row_status == "[green]OK[/green]": row_status = "[yellow]Info (No Cost Data)[/yellow]"
        else: # Should not happen, but catchall
             cost_update_msg = "[orange]Unknown Cost State[/orange]"
             cost_match_status = "[orange]Unknown[/orange]"

        # --- 7. Check and Update Structured Output Support --- (Renumbered from 6)
        # Update if 'structured_output' is NA (missing or failed previous conversion)
        struct_output_missing = pd.isna(row['structured_output'])

        if struct_output_missing:
            # Use the result from the initial check if it succeeded
            if schema_check_result is not None:
                df.loc[index, 'structured_output'] = bool(schema_check_result) # Store as True/False
                struct_update_msg = f"[green]Updated ({bool(schema_check_result)})[/green]"
                needs_update = True
            else:
                # This case should ideally not be reached if initial validation succeeded
                # but handle potential errors stored during the initial check
                if struct_check_error:
                     struct_update_msg = f"[red]Update Failed (Initial Check Error): {struct_check_error}[/red]"
                     df.loc[index, 'structured_output'] = pd.NA # Ensure NA on error
                     if "Fail" not in row_status:
                         row_status = "[red]Fail (Struct Error)[/red]"
                else:
                    # Should not happen, but fallback
                    struct_update_msg = "[orange]Update Skipped (Unknown State)[/orange]"
                    df.loc[index, 'structured_output'] = pd.NA
        else:
            # Value already exists, no need to update
            struct_update_msg = "Checked (Exists)"

        # Tally updates and failures more accurately
        if "Fail" in row_status:
             # models_failed_count += 1 # Increment if any part failed (Original line, less accurate)
             df.loc[index, '_failed'] = True # Mark failure in the DataFrame
        elif needs_update: # Only count as updated if no failure occurred
             models_updated_count += 1
             if row_status == "[green]OK[/green]": # Status was OK before update checks
                 row_status = "[blue]Updated[/blue]"
             # If status was yellow (e.g., no cost data), keep it yellow but acknowledge update elsewhere?
             # Or maybe change yellow to Updated? Let's make Updated override yellow info.
             elif "[yellow]" in row_status:
                 row_status = "[blue]Updated (Info)[/blue]" # Indicate update happened alongside info

        # Add the cost match status to the table row
        table.add_row(model_identifier, cost_update_msg, struct_update_msg, cost_match_status, row_status)

    console.print(table)
    console.print(f"\n[bold]Summary:[/bold]")
    console.print(f"- Models processed: {len(df)}")
    console.print(f"- Models successfully updated: {models_updated_count}")
    # Count unique models with failures for better reporting
    # Calculate based on the temporary '_failed' column in the DataFrame
    unique_failed_models = df[df['_failed']]['model'].nunique()
    console.print(f"- Models with fetch/check errors: {unique_failed_models}") # More accurate count
    console.print(f"- Models with cost mismatches: {mismatched_cost_count}") # Report mismatches
    if mismatched_cost_count > 0:
        console.print(f"  [bold red](Note: Mismatched costs were NOT automatically updated. Check CSV vs LiteLLM.)[/bold red]")

    # Add confirmation if all models passed initial validation
    if unique_failed_models == 0 and len(df) > 0:
        console.print(f"[green]All {len(df)} model identifiers passed initial validation.[/green]")

    # --- 8. Save Updated DataFrame ---
    if models_updated_count > 0 or updated_schema:
        try:
            # Ensure NA values are saved correctly (as empty strings by default)
            # Drop the temporary failure column before saving
            df_to_save = df.drop(columns=['_failed'])
            df_to_save.to_csv(csv_path, index=False, na_rep='') # Save NA as empty string
            console.print(f"\n[bold green]Successfully saved updated data to:[/bold green] {csv_path}")
        except Exception as e:
            console.print(f"[bold red]Error:[/bold red] Failed to save updated CSV file: {e}")
    else:
        console.print("\n[bold blue]No updates needed or made to the CSV file.[/bold blue]")

    # --- 9. Reminder about Manual Column ---
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

    # --- Determine final CSV path ---
    user_pdd_dir = Path.home() / ".pdd"
    user_model_csv_path = user_pdd_dir / "llm_model.csv"
    default_csv_path = Path(args.csv_path).resolve() # Resolve the default path

    final_csv_path = default_csv_path # Start with the default/provided path

    if user_model_csv_path.is_file():
        final_csv_path = user_model_csv_path
        console.print(f"[bold cyan]Found user-specific config, using:[/bold cyan] {final_csv_path}")
    else:
        # Check if the default/provided path actually exists *before* attempting to use it
        if not default_csv_path.is_file():
             # If neither user nor default exists, check if the *directory* for default exists
            default_csv_dir = default_csv_path.parent
            if not default_csv_dir.exists():
                try:
                    os.makedirs(default_csv_dir)
                    console.print(f"[cyan]Created directory for default CSV:[/cyan] {default_csv_dir}")
                    # We still might not have the *file*, update_model_data will handle file not found
                except OSError as e:
                    console.print(f"[bold red]Error:[/bold red] Could not create directory {default_csv_dir}: {e}")
                    return # Exit if directory cannot be created
            # Keep final_csv_path as default_csv_path, update_model_data will report if file doesn't exist
            console.print(f"[cyan]User-specific config not found. Using default/provided path:[/cyan] {final_csv_path}")
        else:
             console.print(f"[cyan]User-specific config not found. Using default/provided path:[/cyan] {final_csv_path}")

    # Pass the determined path to the update function
    update_model_data(str(final_csv_path))

if __name__ == "__main__":
    # --- Crucial Note ---
    console.print("[bold yellow]Important:[/bold yellow] This script assumes the 'model' column in the CSV contains")
    console.print("           [bold yellow]valid LiteLLM model identifiers[/bold yellow] (e.g., 'openai/gpt-4o-mini',")
    console.print("           'ollama/llama3', 'anthropic/claude-3-haiku-20240307').")
    console.print("           Please verify the identifiers before running.\n")
    main()
