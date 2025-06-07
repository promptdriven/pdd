import csv
import os
from typing import List, Dict, Tuple, Optional

from rich.console import Console

# Use relative imports for internal modules within the package
from .change import change
from .get_extension import get_extension
# Assuming EXTRACTION_STRENGTH and DEFAULT_STRENGTH might be needed later,
# or just acknowledging their existence as per the prompt.
# from .. import EXTRACTION_STRENGTH, DEFAULT_STRENGTH
from . import DEFAULT_TIME # Added DEFAULT_TIME

# No changes needed in the code_under_test based on these specific errors.

console = Console()

def resolve_prompt_path(prompt_name: str, csv_file: str, code_directory: str) -> Optional[str]:
    """
    Attempts to find a prompt file by trying several possible locations.

    Args:
        prompt_name: The name or path of the prompt file from the CSV
        csv_file: Path to the CSV file (for relative path resolution)
        code_directory: Path to the code directory (as another potential source)

    Returns:
        Resolved path to the prompt file if found, None otherwise
    """
    # Ensure paths are absolute for reliable checking
    abs_code_directory = os.path.abspath(code_directory)
    abs_csv_dir = os.path.abspath(os.path.dirname(csv_file))
    abs_cwd = os.path.abspath(os.getcwd())

    # List of locations to try, in order of priority
    possible_locations = [
        prompt_name,  # Try exactly as specified first (could be absolute or relative to CWD)
        os.path.join(abs_cwd, os.path.basename(prompt_name)),  # Try in current directory (basename only)
        os.path.join(abs_csv_dir, os.path.basename(prompt_name)),  # Try relative to CSV (basename only)
        os.path.join(abs_code_directory, os.path.basename(prompt_name)), # Try in code directory (basename only)
        os.path.join(abs_csv_dir, prompt_name), # Try relative to CSV (full prompt_name path)
        os.path.join(abs_code_directory, prompt_name) # Try relative to code_dir (full prompt_name path)
    ]

    # Try each location, normalizing and checking existence/type
    checked_locations = set()
    for location in possible_locations:
        try:
            # Normalize path to handle relative parts like '.' or '..' and make absolute
            normalized_location = os.path.abspath(location)
            if normalized_location in checked_locations:
                continue
            checked_locations.add(normalized_location)

            # Check if it exists and is a file
            if os.path.exists(normalized_location) and os.path.isfile(normalized_location):
                return normalized_location
        except Exception:
            # Ignore errors during path resolution (e.g., invalid characters)
            continue

    # If we get here, file was not found
    return None

def process_csv_change(
    csv_file: str,
    strength: float,
    temperature: float,
    code_directory: str,
    language: str, # Default language if not specified in prompt filename
    extension: str, # Default extension (unused if language suffix found)
    budget: float,
    time: float = DEFAULT_TIME # Added time parameter
) -> Tuple[bool, List[Dict[str, str]], float, Optional[str]]:
    """
    Reads a CSV file, processes each row to modify associated code files using an LLM,
    and returns the results.

    Args:
        csv_file: Path to the input CSV file. Must contain 'prompt_name' and
                  'change_instructions' columns.
        strength: Strength parameter for the LLM model (0.0 to 1.0).
        temperature: Temperature parameter for the LLM model (0.0 to 1.0).
        code_directory: Path to the directory containing the code files.
        language: Default programming language if the prompt filename doesn't
                  specify one (e.g., '_python').
        extension: Default file extension (including '.') if language cannot be inferred.
                   Note: This is less likely to be used if `get_extension` covers the default language.
        budget: Maximum allowed cost for all LLM operations. Must be non-negative.
        time: Time budget for each LLM operation.

    Returns:
        A tuple containing:
        - success (bool): True if all rows attempted were processed without errors
                          (even if skipped due to missing data) and budget was not exceeded.
                          False otherwise (including partial success due to budget or errors).
        - list_of_jsons (List[Dict[str, str]]): A list of dictionaries, where each
          dictionary contains 'file_name' (original prompt name from CSV) and 'modified_prompt'.
        - total_cost (float): The total cost incurred for the LLM operations.
        - model_name (Optional[str]): The name of the LLM model used for the first successful change.
                                      Returns "N/A" if no changes were successfully processed.
                                      Returns None if an input validation error occurred before processing.
    """
    list_of_jsons: List[Dict[str, str]] = []
    total_cost: float = 0.0
    model_name: Optional[str] = None
    overall_success: bool = True  # Assume success until an error occurs or budget exceeded

    # --- Input Validation ---
    if not os.path.exists(csv_file) or not os.path.isfile(csv_file): # Check it's a file too
        console.print(f"[bold red]Error:[/bold red] CSV file not found or is not a file: '{csv_file}'")
        return False, [], 0.0, None # Return None for model_name on early exit
    if not os.path.isdir(code_directory):
        console.print(f"[bold red]Error:[/bold red] Code directory not found or is not a directory: '{code_directory}'")
        return False, [], 0.0, None # Return None for model_name on early exit
    if not 0.0 <= strength <= 1.0:
         console.print(f"[bold red]Error:[/bold red] 'strength' must be between 0.0 and 1.0. Given: {strength}")
         return False, [], 0.0, None # Return None for model_name on early exit
    if not 0.0 <= temperature <= 1.0: # Added temperature validation (assuming 0-1 range)
         console.print(f"[bold red]Error:[/bold red] 'temperature' must be between 0.0 and 1.0. Given: {temperature}")
         return False, [], 0.0, None # Return None for model_name on early exit
    if budget < 0.0:
         console.print(f"[bold red]Error:[/bold red] 'budget' must be non-negative. Given: {budget}")
         return False, [], 0.0, None # Return None for model_name on early exit
    # --- End Input Validation ---

    console.print(f"[cyan]Starting CSV processing:[/cyan] '{os.path.abspath(csv_file)}'")
    console.print(f"[cyan]Code directory:[/cyan] '{os.path.abspath(code_directory)}'")
    console.print(f"[cyan]Budget:[/cyan] ${budget:.2f}")

    processed_rows = 0
    successful_changes = 0

    try:
        header_valid = True
        with open(csv_file, mode='r', newline='', encoding='utf-8') as file:
            header_valid = True # Flag to track header status
            reader = None # Initialize reader to None

            # Read the header line manually
            header_line = file.readline()
            if not header_line:
                # Handle empty file
                console.print("[yellow]Warning:[/yellow] CSV file is empty.")
                header_valid = False # Treat as invalid header for flow control
                # No rows will be processed, overall_success remains True initially
            else:
                # Parse the header line
                actual_fieldnames = [col.strip() for col in header_line.strip().split(',')]

                # Check if required columns are present
                required_cols = {'prompt_name', 'change_instructions'}
                missing_cols = required_cols - set(actual_fieldnames)
                if missing_cols:
                    console.print(f"[bold red]Error:[/bold red] CSV file must contain 'prompt_name' and 'change_instructions' columns. Missing: {missing_cols}")
                    overall_success = False # Mark overall failure
                    header_valid = False # Mark header as invalid
                else:
                    # Header is valid and has required columns, initialize DictReader for remaining lines
                    reader = csv.DictReader(file, fieldnames=actual_fieldnames)

            # Only loop if the header was valid and reader was initialized
            if header_valid and reader:
                for i, row in enumerate(reader):
                    row_num = i + 1
                    processed_rows += 1
                    console.print(f"\n[cyan]Processing row {row_num}...[/cyan]")

                    prompt_name_from_csv = row.get('prompt_name', '').strip()
                    change_instructions = row.get('change_instructions', '').strip()

                    if not prompt_name_from_csv:
                        console.print(f"[bold yellow]Warning:[/bold yellow] Missing 'prompt_name' in row {row_num}. Skipping.")
                        overall_success = False # Mark as not fully successful if skips occur
                        continue
                    if not change_instructions:
                         console.print(f"[bold yellow]Warning:[/bold yellow] Missing 'change_instructions' in row {row_num}. Skipping.")
                         overall_success = False # Mark as not fully successful if skips occur
                         continue

                    # Try to resolve the prompt file path
                    resolved_prompt_path = resolve_prompt_path(prompt_name_from_csv, csv_file, code_directory)
                    if not resolved_prompt_path:
                        console.print(f"[bold red]Error:[/bold red] Prompt file for '{prompt_name_from_csv}' not found in any location (row {row_num}).")
                        console.print(f"  [dim]Searched: as is, CWD, CSV dir, code dir (using basename and full name)[/dim]")
                        overall_success = False
                        continue

                    console.print(f"  [dim]Prompt name from CSV:[/dim] {prompt_name_from_csv}")
                    console.print(f"  [dim]Resolved prompt path:[/dim] {resolved_prompt_path}")

                    # --- Step 2a: Initialize variables ---
                    input_prompt: Optional[str] = None
                    input_code: Optional[str] = None
                    input_code_path: Optional[str] = None

                    # Read the input prompt from the resolved path
                    try:
                        with open(resolved_prompt_path, 'r', encoding='utf-8') as f:
                            input_prompt = f.read()
                    except IOError as e:
                        console.print(f"[bold red]Error:[/bold red] Could not read prompt file '{resolved_prompt_path}' (row {row_num}): {e}")
                        overall_success = False
                        continue # Skip to next row

                    # Parse prompt_name to determine input_code_name
                    try:
                        # i. remove the path and suffix _language.prompt from the prompt_name
                        prompt_filename = os.path.basename(resolved_prompt_path) # Use basename of resolved path
                        base_name, ext = os.path.splitext(prompt_filename) # Removes .prompt (or other ext)

                        # Ensure it actually ends with .prompt before stripping language
                        if ext.lower() != '.prompt':
                             console.print(f"[bold yellow]Warning:[/bold yellow] Prompt file '{prompt_filename}' does not end with '.prompt'. Attempting to parse language anyway (row {row_num}).")
                             # Keep base_name as is, don't assume .prompt was the only extension part

                        file_stem = base_name
                        actual_language = language # Default language
                        language_from_suffix = False # Track if language came from suffix

                        # Check for _language suffix
                        if '_' in base_name:
                            parts = base_name.rsplit('_', 1)
                            # Check if the suffix looks like a language identifier (simple check: alpha only)
                            if len(parts) == 2 and parts[1].isalpha():
                                file_stem = parts[0]
                                # Use capitalize for consistency, matching get_extension examples
                                actual_language = parts[1].capitalize()
                                language_from_suffix = True # Set flag
                                console.print(f"    [dim]Inferred language from filename:[/dim] {actual_language}")
                            else:
                                console.print(f"    [dim]Suffix '_{parts[1]}' not recognized as language, using default:[/dim] {language}")
                        else:
                            console.print(f"    [dim]Using default language:[/dim] {language}")


                        # ii. use get_extension to infer the extension
                        try:
                            # print(f"DEBUG: Trying get_extension for language: '{actual_language}'") # Keep commented
                            # Use the capitalized version for lookup
                            code_extension = get_extension(actual_language.capitalize())
                            console.print(f"    [dim]Inferred extension for {actual_language}:[/dim] '{code_extension}'")
                        except ValueError: # Handle case where get_extension doesn't know the language
                            # print(f"DEBUG: get_extension failed. Falling back to default extension parameter: '{extension}'") # Keep commented
                            if language_from_suffix:
                                # Suffix was present but get_extension failed for it! Error out for this row.
                                console.print(f"[bold red]Error:[/bold red] Language '{actual_language}' found in prompt suffix, but its extension is unknown (row {row_num}). Skipping.")
                                overall_success = False # Mark failure
                                continue # Skip to next row
                            else:
                                # No suffix, and get_extension failed for the default language.
                                # Fallback to the 'extension' parameter as a last resort (current behavior).
                                console.print(f"[bold yellow]Warning:[/bold yellow] Could not determine extension for default language '{actual_language}'. Using default extension parameter '{extension}' (row {row_num}).")
                                code_extension = extension # Fallback to the provided default extension parameter
                                # Do not mark overall_success as False for this warning, it's a fallback mechanism
                        # print(f"DEBUG: Determined code extension: '{code_extension}'") # Keep commented

                        # iii. add the suffix extension to the prompt_name (stem)
                        input_code_filename = file_stem + code_extension

                        # iv. Construct code file path: place it directly in code_directory.
                        input_code_path = os.path.join(code_directory, input_code_filename)
                        console.print(f"  [dim]Derived target code path:[/dim] {input_code_path}")
                        print(f"DEBUG: Attempting to access code file path: '{input_code_path}'") # Added log


                        # Read the input code from the input_code_path
                        if not os.path.exists(input_code_path) or not os.path.isfile(input_code_path):
                             console.print(f"[bold red]Error:[/bold red] Derived code file not found or is not a file: '{input_code_path}' (row {row_num})")
                             overall_success = False
                             continue # Skip to next row
                        with open(input_code_path, 'r', encoding='utf-8') as f:
                            input_code = f.read()

                    except Exception as e:
                        console.print(f"[bold red]Error:[/bold red] Failed to parse filenames or read code file for row {row_num}: {e}")
                        overall_success = False
                        continue # Skip to next row

                    # Ensure we have all necessary components before calling change
                    # (Should be guaranteed by checks above, but added defensively)
                    if input_prompt is None or input_code is None or change_instructions is None:
                         console.print(f"[bold red]Internal Error:[/bold red] Missing required data (prompt, code, or instructions) for row {row_num}. Skipping.")
                         overall_success = False
                         continue

                    # --- Step 2b: Call the change function ---
                    try:
                        # Check budget *before* making the potentially expensive call
                        if total_cost >= budget:
                             console.print(f"[bold yellow]Warning:[/bold yellow] Budget (${budget:.2f}) already met or exceeded before processing row {row_num}. Stopping.")
                             overall_success = False # Mark as incomplete due to budget
                             break # Exit the loop

                        console.print(f"  [dim]Calling LLM for change... (Budget remaining: ${budget - total_cost:.2f})[/dim]")
                        modified_prompt, cost, current_model_name = change(
                            input_prompt=input_prompt,
                            input_code=input_code,
                            change_prompt=change_instructions,
                            strength=strength,
                            temperature=temperature,
                            time=time, # Pass time
                            budget=budget - total_cost, # Pass per-row budget
                            # verbose=verbose Suppress individual change prints for CSV mode
                        )
                        console.print(f"    [dim]Change cost:[/dim] ${cost:.6f}")
                        console.print(f"    [dim]Model used:[/dim] {current_model_name}")

                        # --- Step 2c: Add cost ---
                        new_total_cost = total_cost + cost

                        # --- Step 2d: Check budget *after* call ---
                        console.print(f"  [dim]Cumulative cost:[/dim] ${new_total_cost:.6f} / ${budget:.2f}")
                        if new_total_cost > budget:
                            console.print(f"[bold yellow]Warning:[/bold yellow] Budget exceeded (${budget:.2f}) after processing row {row_num}. Change from this row NOT saved. Stopping.")
                            total_cost = new_total_cost # Record the cost even if result isn't saved
                            overall_success = False # Mark as incomplete due to budget
                            break # Exit the loop
                        else:
                             total_cost = new_total_cost # Update cost only if within budget

                        # --- Step 2e: Add successful result ---
                        # Capture model name on first successful call within budget
                        if model_name is None and current_model_name:
                            model_name = current_model_name
                        # Warn if model name changes on subsequent calls
                        elif current_model_name and model_name != current_model_name:
                             console.print(f"[bold yellow]Warning:[/bold yellow] Model name changed from '{model_name}' to '{current_model_name}' in row {row_num}.")
                             # Keep the first model_name

                        list_of_jsons.append({
                            "file_name": prompt_name_from_csv, # Use original prompt name from CSV as key
                            "modified_prompt": modified_prompt
                        })
                        successful_changes += 1
                        console.print(f"  [green]Successfully processed change for:[/green] {prompt_name_from_csv}")


                    except Exception as e:
                        console.print(f"[bold red]Error:[/bold red] Failed during 'change' call for '{prompt_name_from_csv}' (row {row_num}): {e}")
                        overall_success = False
                        # Continue to the next row even if one fails

    except FileNotFoundError:
        # This case should be caught by the initial validation, but included for robustness
        console.print(f"[bold red]Error:[/bold red] CSV file not found at '{csv_file}'")
        return False, [], 0.0, None
    except IOError as e:
        console.print(f"[bold red]Error:[/bold red] Could not read CSV file '{csv_file}': {e}")
        return False, [], 0.0, None
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred during CSV processing:[/bold red] {e}")
        # Return potentially partial results, but mark as failure
        return False, list_of_jsons, total_cost, model_name if model_name else "N/A"

    # --- Step 3: Return results ---
    console.print("\n[bold cyan]=== Processing Summary ===[/bold cyan]")
    if processed_rows == 0 and overall_success:
         # This case is handled by the empty file check earlier, but keep for clarity
         console.print("[yellow]No rows found in CSV file.[/yellow]")
    elif not overall_success:
         console.print("[yellow]Processing finished with errors, skips, or budget exceeded.[/yellow]")
    else:
         console.print("[green]CSV processing finished successfully.[/green]")

    console.print(f"[bold]Total Rows Processed:[/bold] {processed_rows}")
    console.print(f"[bold]Successful Changes:[/bold] {successful_changes}")
    console.print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
    console.print(f"[bold]Model Used (first success):[/bold] {model_name if model_name else 'N/A'}")
    console.print(f"[bold]Overall Success Status:[/bold] {overall_success}")


    # --- Summary printing block should be right above here ---

    final_model_name = model_name if model_name else "N/A"
    # If overall_success is False AND header_valid is False, it means we failed on header validation.
    if not overall_success and not header_valid:
         final_model_name = None

    return overall_success, list_of_jsons, total_cost, final_model_name


# Example usage (assuming this file is part of a package structure)
# Keep the example usage block as is for basic testing/demonstration
if __name__ == '__main__':
    # This block is for demonstration/testing purposes.
    # In a real package, you'd import and call process_csv_change from another module.

    # Create dummy files and directories for testing
    if not os.path.exists("temp_code_dir"):
        os.makedirs("temp_code_dir")
    if not os.path.exists("temp_prompt_dir"):
        os.makedirs("temp_prompt_dir")

    # Dummy CSV
    csv_content = """prompt_name,change_instructions
temp_prompt_dir/func1_python.prompt,"Add error handling for negative numbers"
temp_prompt_dir/script2_javascript.prompt,"Convert to async/await"
temp_prompt_dir/invalid_file.prompt,"This will fail code file lookup"
temp_prompt_dir/config_yaml.prompt,"Increase timeout value"
temp_prompt_dir/missing_instr.prompt,
missing_prompt.prompt,"This prompt file won't be found"
temp_prompt_dir/budget_breaker_python.prompt,"This might break the budget"
"""
    with open("temp_changes.csv", "w") as f:
        f.write(csv_content)

    # Dummy prompt files
    with open("temp_prompt_dir/func1_python.prompt", "w") as f:
        f.write("Create a Python function for factorial.")
    with open("temp_prompt_dir/script2_javascript.prompt", "w") as f:
        f.write("Write a JS script using callbacks.")
    with open("temp_prompt_dir/invalid_file.prompt", "w") as f: # Code file missing
        f.write("Some prompt.")
    with open("temp_prompt_dir/config_yaml.prompt", "w") as f:
        f.write("Describe the YAML config.")
    with open("temp_prompt_dir/missing_instr.prompt", "w") as f: # Instructions missing in CSV
        f.write("Prompt with missing instructions.")
    # missing_prompt.prompt does not exist
    with open("temp_prompt_dir/budget_breaker_python.prompt", "w") as f:
        f.write("Prompt for budget breaker.")


    # Dummy code files
    with open("temp_code_dir/func1.py", "w") as f:
        f.write("def factorial(n):\n  if n == 0: return 1\n  return n * factorial(n-1)\n")
    with open("temp_code_dir/script2.js", "w") as f:
        f.write("function fetchData(url, callback) { /* ... */ }")
    # No code file for invalid_file
    with open("temp_code_dir/config.yaml", "w") as f:
        f.write("timeout: 10s\nretries: 3\n")
    with open("temp_code_dir/budget_breaker.py", "w") as f:
        f.write("print('Hello')")


    # Dummy internal modules (replace with actual imports if running within package)
    # Mocking the internal functions for standalone execution
    def mock_change(input_prompt, input_code, change_prompt, strength, temperature):
        # Simulate cost and model name
        cost = 0.01 + (0.0001 * len(change_prompt))
        model = "mock-gpt-4"
        # Simulate success or failure based on input
        if "invalid" in input_prompt.lower():
             raise ValueError("Simulated model error for invalid input.")
        modified_prompt = f"MODIFIED: {input_prompt[:30]}... based on '{change_prompt[:30]}...'"
        return modified_prompt, cost, model

    def mock_get_extension(language_name):
        lang_map = {
            "Python": ".py",
            "Javascript": ".js", # Note: Case difference from prompt example
            "Yaml": ".yaml",
            "Makefile": "" # Example from prompt
        }
        # Match behavior of raising ValueError if unknown, case-sensitive
        if language_name in lang_map:
            return lang_map[language_name]
        else:
            raise ValueError(f"Unknown language: {language_name}")

    # Replace the actual imports with mocks for the example
    change_original = change
    get_extension_original = get_extension
    change = mock_change
    get_extension = mock_get_extension

    console.print("\n[bold magenta]=== Running Example Usage ===[/bold magenta]")

    # Call the function
    success_status, results, final_cost, final_model = process_csv_change(
        csv_file="temp_changes.csv",
        strength=0.6,
        temperature=0.1,
        code_directory="temp_code_dir",
        language="UnknownLang", # Default language
        extension=".txt",   # Default extension (used if get_extension fails)
        budget=0.05 # Set a budget likely to be exceeded
    )

    console.print("\n[bold magenta]=== Example Usage Results ===[/bold magenta]")
    # console.print(f"Overall Success: {success_status}") # Printed in summary now
    # console.print(f"Total Cost: ${final_cost:.6f}") # Printed in summary now
    # console.print(f"Model Name: {final_model}") # Printed in summary now
    console.print("Modified Prompts JSON (results list):")
    console.print(results)

    # Restore original functions if needed elsewhere
    change = change_original
    get_extension = get_extension_original

    # Cleanup dummy files (optional)
    # import shutil
    # try:
    #     os.remove("temp_changes.csv")
    #     shutil.rmtree("temp_code_dir")
    #     shutil.rmtree("temp_prompt_dir")
    #     console.print("\n[bold magenta]=== Cleaned up temporary files ===[/bold magenta]")
    # except OSError as e:
    #     console.print(f"\n[yellow]Warning: Could not clean up all temp files: {e}[/yellow]")
