# update_model_costs.py

import argparse
import os
import pandas as pd
import litellm
from rich.console import Console
from rich.table import Table
import math # For isnan check, although pd.isna is preferred
from pathlib import Path
from rich.text import Text # Import Text for explicit string conversion if needed

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
# MISSING_VALUE_PLACEHOLDER = -1.0 # Not used in current logic, pd.NA preferred

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

    # Keep a copy for comparison later to determine if actual data changed
    # Do this *before* schema changes and type enforcement
    original_df = df.copy()

    # --- 2. Check and Add Missing Columns ---
    updated_schema = False
    for col in EXPECTED_COLUMNS:
        if col not in df.columns:
            updated_schema = True
            console.print(f"[yellow]Warning:[/yellow] Column '{col}' missing. Adding it.")
            # Initialize with pd.NA regardless of type, enforcement happens next
            df[col] = pd.NA
    if updated_schema:
        console.print("[cyan]CSV schema updated with missing columns.[/cyan]")
        # Reorder columns to match expected order if schema was updated
        df = df.reindex(columns=EXPECTED_COLUMNS)


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
            # Convert common string representations to bool or NA
            df['structured_output'] = df['structured_output'].apply(
                lambda x: pd.NA if pd.isna(x) or str(x).strip().lower() in ['', 'na', 'nan', '<na>'] else (
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

    # --- 4. Iterate Through Models and Update ---
    models_updated_count = 0 # Tracks rows where data was actually changed
    # models_failed_count = 0 # Replaced by unique_failed_models later
    mismatched_cost_count = 0 # Track mismatches
    # Add a temporary column to track failures directly
    df['_failed'] = False
    # Track if any actual data change happened beyond schema or type coercion
    data_changed = False

    console.print("\n[bold blue]Processing models...[/bold blue]")
    table = Table(title="Model Update Status", show_lines=True)
    table.add_column("Model Identifier", style="cyan")
    table.add_column("Cost Update", style="magenta")
    table.add_column("Struct. Output Update", style="yellow")
    table.add_column("Cost Match", style="blue") # New column for matching status
    table.add_column("Status", style="green")

    # Pre-fetch all model costs from LiteLLM once
    all_model_costs = {} # Initialize as empty
    try:
        # Access the property/attribute inside the try block
        cost_data_dict = litellm.model_cost
        # Ensure it's a dictionary, handle None case
        all_model_costs = cost_data_dict if isinstance(cost_data_dict, dict) else {}
        if not all_model_costs:
             console.print("[yellow]Warning:[/yellow] `litellm.model_cost` returned empty or None. Cost updates might be skipped.")
        else:
            console.print("[green]Successfully fetched LiteLLM model cost data.[/green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] Could not fetch LiteLLM model cost data: {e}")
        # all_model_costs remains {}

    for index, row in df.iterrows():
        model_identifier = row['model']
        # Ensure model_identifier is treated as a string for consistency
        model_identifier_str = str(model_identifier) if not pd.isna(model_identifier) else None

        if not model_identifier_str:
            console.print(f"[yellow]Warning:[/yellow] Skipping row {index} due to missing model identifier.")
            continue

        # --- Cost Comparison Variables ---
        fetched_input_cost = None
        fetched_output_cost = None
        cost_match_status = "[grey]N/A[/grey]" # Default if no litellm data or comparison not possible
        cost_data_available = False

        # --- 5. Initial Model Validation & Schema Check ---
        is_valid_model = True
        schema_check_result = None # Store result if check succeeds
        struct_check_error = None # Store potential error details

        try:
            # Use the string version for the LiteLLM call
            schema_check_result = litellm.supports_response_schema(model=model_identifier_str)
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
            # Use string identifier for table
            table.add_row(model_identifier_str, cost_update_msg, struct_update_msg, cost_match_status, row_status)
            continue

        # --- If validation passed, proceed with cost and struct updates ---
        cost_update_msg = "Checked"
        struct_update_msg = "Checked"
        row_status = "[green]OK[/green]"
        row_needs_update = False # Track if this specific row's data changed

        # --- 6. Check and Update Costs ---
        # Use string identifier to look up cost data
        cost_data = all_model_costs.get(model_identifier_str)
        cost_fetch_error = None

        if cost_data and isinstance(cost_data, dict): # Ensure cost_data is a dict
            cost_data_available = True
            try:
                input_cost_per_token = cost_data.get('input_cost_per_token')
                output_cost_per_token = cost_data.get('output_cost_per_token')

                # Ensure costs are numeric before calculation
                if input_cost_per_token is not None:
                    try:
                        fetched_input_cost = float(input_cost_per_token) * 1_000_000
                    except (ValueError, TypeError):
                        console.print(f"[yellow]Warning ({model_identifier_str}):[/yellow] Invalid input_cost_per_token format: {input_cost_per_token}")
                        fetched_input_cost = None
                        cost_fetch_error = cost_fetch_error or ValueError("Invalid input cost format")
                if output_cost_per_token is not None:
                     try:
                        fetched_output_cost = float(output_cost_per_token) * 1_000_000
                     except (ValueError, TypeError):
                        console.print(f"[yellow]Warning ({model_identifier_str}):[/yellow] Invalid output_cost_per_token format: {output_cost_per_token}")
                        fetched_output_cost = None
                        cost_fetch_error = cost_fetch_error or ValueError("Invalid output cost format")


            except Exception as e:
                # Catch errors during the .get or multiplication
                cost_fetch_error = e
                cost_update_msg = f"[red]Error processing costs: {e}[/red]"
                if "Fail" not in row_status: row_status = "[red]Fail (Cost Error)[/red]"
                df.loc[index, '_failed'] = True # Mark failure

        # Decide action based on fetched data and existing values
        # Use .loc for robust NA check after type enforcement
        input_cost_missing = pd.isna(df.loc[index, 'input'])
        output_cost_missing = pd.isna(df.loc[index, 'output'])

        updated_costs_messages = []
        mismatched_costs_messages = []
        matched_costs_messages = []

        if cost_data_available and not cost_fetch_error:
            current_input_cost = df.loc[index, 'input']
            current_output_cost = df.loc[index, 'output']

            # Update Input Cost if missing
            if input_cost_missing and fetched_input_cost is not None:
                df.loc[index, 'input'] = fetched_input_cost
                updated_costs_messages.append(f"Input: {fetched_input_cost:.4f}")
                row_needs_update = True
            # Compare Input Cost if not missing
            elif not input_cost_missing and fetched_input_cost is not None:
                # Use isclose for float comparison
                if not math.isclose(current_input_cost, fetched_input_cost, rel_tol=1e-6):
                    mismatched_costs_messages.append(f"Input (CSV: {current_input_cost:.4f}, LLM: {fetched_input_cost:.4f})")
                else:
                    matched_costs_messages.append("Input")
            elif not input_cost_missing and fetched_input_cost is None:
                 # CSV has cost, but LiteLLM doesn't provide input cost
                 matched_costs_messages.append("Input (CSV Only)")


            # Update Output Cost if missing
            if output_cost_missing and fetched_output_cost is not None:
                df.loc[index, 'output'] = fetched_output_cost
                updated_costs_messages.append(f"Output: {fetched_output_cost:.4f}")
                row_needs_update = True
            # Compare Output Cost if not missing
            elif not output_cost_missing and fetched_output_cost is not None:
                 # Use isclose for float comparison
                if not math.isclose(current_output_cost, fetched_output_cost, rel_tol=1e-6):
                    mismatched_costs_messages.append(f"Output (CSV: {current_output_cost:.4f}, LLM: {fetched_output_cost:.4f})")
                else:
                    matched_costs_messages.append("Output")
            elif not output_cost_missing and fetched_output_cost is None:
                 # CSV has cost, but LiteLLM doesn't provide output cost
                 matched_costs_messages.append("Output (CSV Only)")


            # Set Cost Update Message
            if updated_costs_messages:
                cost_update_msg = f"[green]Updated ({', '.join(updated_costs_messages)})[/green]"
            elif mismatched_costs_messages or matched_costs_messages: # If compared, even if no update
                cost_update_msg = "[blue]Checked (No missing values)[/blue]"
            else: # No cost data in litellm for either input/output that could be processed
                cost_update_msg = "[yellow]No comparable cost data in LiteLLM[/yellow]"
                if row_status == "[green]OK[/green]": row_status = "[yellow]Info (No Cost Data)[/yellow]"

            # Set Cost Match Status Message
            if mismatched_costs_messages:
                cost_match_status = f"[bold red]Mismatch! ({', '.join(mismatched_costs_messages)})[/bold red]"
                mismatched_cost_count += 1 # Increment mismatch counter
            elif matched_costs_messages == ["Input (CSV Only)", "Output (CSV Only)"]:
                 cost_match_status = "[grey]N/A (No LLM Data)[/grey]"
            elif matched_costs_messages:
                 # Mix of matched and CSV only is still a match for available data
                 match_details = ', '.join(m for m in matched_costs_messages if 'CSV Only' not in m)
                 if match_details:
                     cost_match_status = f"[green]Match ({match_details})[/green]"
                 else: # Only CSV Only messages
                     cost_match_status = "[grey]N/A (No LLM Data)[/grey]"
            elif updated_costs_messages: # If costs were updated, they now 'match'
                 cost_match_status = f"[blue]N/A (Updated)[/blue]"
            else: # If no costs existed to compare (e.g., LLM has no cost data)
                cost_match_status = "[grey]N/A (No LLM Data)[/grey]"

        elif cost_fetch_error:
            cost_match_status = "[red]Error during fetch/process[/red]"
            # Ensure row status reflects failure if not already set
            if "Fail" not in row_status: row_status = "[red]Fail (Cost Error)[/red]"
            df.loc[index, '_failed'] = True # Mark failure

        elif not cost_data_available:
            cost_update_msg = "[yellow]Cost data not found in LiteLLM[/yellow]"
            cost_match_status = "[grey]N/A (No LLM Data)[/grey]"
            if row_status == "[green]OK[/green]": row_status = "[yellow]Info (No Cost Data)[/yellow]"
        else: # Should not happen, but catchall
             cost_update_msg = "[orange]Unknown Cost State[/orange]"
             cost_match_status = "[orange]Unknown[/orange]"

        # --- 7. Check and Update Structured Output Support ---
        # Use .loc for robust NA check
        struct_output_missing = pd.isna(df.loc[index, 'structured_output'])

        if struct_output_missing:
            # Use the result from the initial check if it succeeded
            if schema_check_result is not None:
                new_value = bool(schema_check_result)
                df.loc[index, 'structured_output'] = new_value # Store as True/False
                struct_update_msg = f"[green]Updated ({new_value})[/green]"
                row_needs_update = True
            else:
                # This case means initial validation passed, but schema_check_result is None (shouldn't happen)
                # or initial validation failed (handled earlier, but double-check struct_check_error)
                if struct_check_error:
                     # Error already reported during validation phase
                     struct_update_msg = f"[red]Update Failed (Initial Check Error)[/red]"
                     df.loc[index, 'structured_output'] = pd.NA # Ensure NA on error
                     if "Fail" not in row_status:
                         row_status = "[red]Fail (Struct Error)[/red]"
                     df.loc[index, '_failed'] = True # Mark failure
                else:
                    # Fallback if validation passed but result is missing
                    struct_update_msg = "[orange]Update Skipped (Unknown State)[/orange]"
                    df.loc[index, 'structured_output'] = pd.NA
        else:
            # Value already exists, no need to update
            struct_update_msg = "Checked (Exists)"

        # Tally updates and failures
        if df.loc[index, '_failed']: # Check the failure flag
             pass # Failure already marked, status set earlier
        elif row_needs_update: # Only count as updated if no failure occurred and data changed
             models_updated_count += 1
             data_changed = True # Mark that some data was actually modified
             if row_status == "[green]OK[/green]": # Status was OK before update checks
                 row_status = "[blue]Updated[/blue]"
             elif "[yellow]" in row_status: # Update happened alongside info
                 row_status = "[blue]Updated (Info)[/blue]"

        # Add the row to the table using the string identifier
        table.add_row(model_identifier_str, cost_update_msg, struct_update_msg, cost_match_status, row_status)

    console.print(table)
    console.print(f"\n[bold]Summary:[/bold]")
    console.print(f"- Models processed: {len(df)}")
    # Count unique models with failures for better reporting
    unique_failed_models = df[df['_failed']]['model'].nunique()
    console.print(f"- Models with fetch/check errors: {unique_failed_models}")
    console.print(f"- Rows potentially updated (data changed): {models_updated_count}")
    console.print(f"- Models with cost mismatches: {mismatched_cost_count}")
    if mismatched_cost_count > 0:
        console.print(f"  [bold red](Note: Mismatched costs were NOT automatically updated. Check CSV vs LiteLLM.)[/bold red]")

    # Add confirmation if all models passed initial validation
    if unique_failed_models == 0 and len(df) > 0:
        console.print(f"[green]All {len(df)} model identifiers passed initial validation.[/green]")

    # --- 8. Save Updated DataFrame ---
    # Save if schema was updated OR if actual data values changed
    # Compare current df (without _failed col) to original df (before type enforcement/updates)
    df_to_save = df.drop(columns=['_failed'])

    # Use df.equals() for robust comparison, requires identical types and values
    # Note: Type enforcement might change dtypes (e.g., int to Int64) causing equals() to be false
    # even if values look the same. A more lenient check might be needed if saving only on value change is critical.
    # For now, save if schema changed OR data changed (tracked by data_changed flag).
    should_save = updated_schema or data_changed

    # Add logging for save condition
    console.print(f"\n[grey]Save check: updated_schema={updated_schema}, data_changed={data_changed}[/grey]")

    if should_save:
        try:
            console.print(f"[cyan]Attempting to save updates to {csv_path}...[/cyan]")
            # Ensure NA values are saved correctly (as empty strings by default)
            df_to_save.to_csv(csv_path, index=False, na_rep='') # Save NA as empty string
            console.print(f"[bold green]Successfully saved updated data to:[/bold green] {csv_path}")
        except Exception as e:
            console.print(f"[bold red]Error:[/bold red] Failed to save updated CSV file: {e}")
    else:
        console.print("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")

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
        default=".pdd/llm_model.csv",
        help="Path to the llm_model.csv file (default: .pdd/llm_model.csv)"
    )
    args = parser.parse_args()

    # --- Determine final CSV path ---
    user_pdd_dir = Path.home() / ".pdd"
    user_model_csv_path = user_pdd_dir / "llm_model.csv"
    # Resolve the default/provided path to an absolute path
    default_or_arg_path = Path(args.csv_path).resolve()

    final_csv_path = default_or_arg_path # Start with the resolved default/provided path

    if user_model_csv_path.is_file():
        final_csv_path = user_model_csv_path
        console.print(f"[bold cyan]Found user-specific config, using:[/bold cyan] {final_csv_path}")
    else:
        console.print(f"[cyan]User-specific config not found. Using default/provided path:[/cyan] {final_csv_path}")
        # Ensure the directory for the *final* path exists only if it's not the user path
        final_csv_dir = final_csv_path.parent
        if not final_csv_dir.exists():
            try:
                # Use exist_ok=True to avoid error if dir exists (race condition)
                os.makedirs(final_csv_dir, exist_ok=True)
                console.print(f"[cyan]Created directory:[/cyan] {final_csv_dir}")
            except OSError as e:
                console.print(f"[bold red]Error:[/bold red] Could not create directory {final_csv_dir}: {e}")
                return # Exit if directory cannot be created
        # Note: update_model_data will handle if the *file* doesn't exist at final_csv_path

    # Pass the determined absolute path string to the update function
    update_model_data(str(final_csv_path))

if __name__ == "__main__":
    # --- Crucial Note ---
    console.print("[bold yellow]Important:[/bold yellow] This script assumes the 'model' column in the CSV contains")
    console.print("           [bold yellow]valid LiteLLM model identifiers[/bold yellow] (e.g., 'openai/gpt-4o-mini',")
    console.print("           'ollama/llama3', 'anthropic/claude-3-haiku-20240307').")
    console.print("           Please verify the identifiers before running.\n")
    main()
