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
    # List of locations to try, in order of priority
    possible_locations = [
        prompt_name,  # Try exactly as specified first
        os.path.join(os.getcwd(), os.path.basename(prompt_name)),  # Try in current directory
        os.path.join(os.path.dirname(csv_file), os.path.basename(prompt_name)),  # Try relative to CSV
        os.path.join(code_directory, os.path.basename(prompt_name))  # Try in code directory
    ]
    
    # Try each location
    for location in possible_locations:
        if os.path.exists(location) and os.path.isfile(location):
            return location
            
    # If we get here, file was not found
    return None

def process_csv_change(
    csv_file: str,
    strength: float,
    temperature: float,
    code_directory: str,
    language: str, # Default language if not specified in prompt filename
    extension: str, # Default extension (unused if language suffix found)
    budget: float
) -> Tuple[bool, List[Dict[str, str]], float, Optional[str]]:
    """
    Reads a CSV file, processes each row to modify associated code files using an LLM,
    and returns the results.

    Args:
        csv_file: Path to the input CSV file. Must contain 'prompt_name' and 
                  'change_instructions' columns.
        strength: Strength parameter for the LLM model (0.0 to 1.0).
        temperature: Temperature parameter for the LLM model.
        code_directory: Path to the directory containing the code files.
        language: Default programming language if the prompt filename doesn't 
                  specify one (e.g., '_python').
        extension: Default file extension (including '.') if language cannot be inferred. 
                   Note: This is less likely to be used if `get_extension` covers the default language.
        budget: Maximum allowed cost for all LLM operations.

    Returns:
        A tuple containing:
        - success (bool): True if all rows were processed successfully within budget, 
                          False otherwise (including partial success due to budget).
        - list_of_jsons (List[Dict[str, str]]): A list of dictionaries, where each 
          dictionary contains 'file_name' (original prompt path) and 'modified_prompt'.
        - total_cost (float): The total cost incurred for the LLM operations.
        - model_name (Optional[str]): The name of the LLM model used. None if no 
          successful calls were made.
    """
    list_of_jsons: List[Dict[str, str]] = []
    total_cost: float = 0.0
    model_name: Optional[str] = None
    success: bool = True  # Assume success until proven otherwise

    # --- Input Validation ---
    if not os.path.exists(csv_file):
        console.print(f"[bold red]Error:[/bold red] CSV file not found at '{csv_file}'")
        return False, [], 0.0, None
    if not os.path.isdir(code_directory):
        console.print(f"[bold red]Error:[/bold red] Code directory not found at '{code_directory}'")
        return False, [], 0.0, None
    if not 0.0 <= strength <= 1.0:
         console.print(f"[bold red]Error:[/bold red] Strength must be between 0.0 and 1.0. Got: {strength}")
         return False, [], 0.0, None
    # --- End Input Validation ---

    console.print(f"[cyan]Starting CSV processing:[/cyan] '{csv_file}'")
    console.print(f"[cyan]Code directory:[/cyan] '{code_directory}'")
    console.print(f"[cyan]Budget:[/cyan] £{budget:.2f}")

    try:
        with open(csv_file, mode='r', newline='', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            
            # Check for required columns
            if not all(col in reader.fieldnames for col in ['prompt_name', 'change_instructions']):
                console.print(f"[bold red]Error:[/bold red] CSV file must contain 'prompt_name' and 'change_instructions' columns.")
                return False, [], 0.0, None

            for i, row in enumerate(reader):
                console.print(f"\n[cyan]Processing row {i+1}...[/cyan]")
                
                prompt_name_from_csv = row.get('prompt_name')
                change_instructions = row.get('change_instructions')

                if not prompt_name_from_csv or not change_instructions:
                    console.print(f"[bold yellow]Warning:[/bold yellow] Skipping row {i+1} due to missing 'prompt_name' or 'change_instructions'.")
                    success = False # Mark as not fully successful
                    continue

                # Try to resolve the prompt file path
                resolved_prompt_path = resolve_prompt_path(prompt_name_from_csv, csv_file, code_directory)
                if not resolved_prompt_path:
                    console.print(f"[bold red]Error:[/bold red] Prompt file not found in any location: '{prompt_name_from_csv}'")
                    console.print(f"  [dim]Tried: as absolute, in current directory, relative to CSV, in code directory[/dim]")
                    success = False
                    continue
                
                console.print(f"  [dim]Prompt file:[/dim] {prompt_name_from_csv}")
                console.print(f"  [dim]Resolved to:[/dim] {resolved_prompt_path}")

                # --- Step 2a: Initialize variables ---
                input_prompt: Optional[str] = None
                input_code: Optional[str] = None
                input_code_path: Optional[str] = None

                # Read the input prompt from the resolved path
                try:
                    with open(resolved_prompt_path, 'r', encoding='utf-8') as f:
                        input_prompt = f.read()
                except IOError as e:
                    console.print(f"[bold red]Error:[/bold red] Could not read prompt file '{resolved_prompt_path}': {e}")
                    success = False
                    continue # Skip to next row
                
                # Parse prompt_name to determine input_code_name
                try:
                    # i. remove the path and suffix _language.prompt from the prompt_name
                    prompt_filename = os.path.basename(prompt_name_from_csv)
                    base_name, _ = os.path.splitext(prompt_filename) # Removes .prompt

                    file_stem = base_name
                    actual_language = language # Default language
                    
                    # Check for _language suffix
                    if '_' in base_name:
                        parts = base_name.rsplit('_', 1)
                        if len(parts) == 2:
                            # Check if the suffix looks like a language identifier (simple check)
                            # A more robust check might involve a list of known languages
                            if parts[1].isalpha(): 
                                file_stem = parts[0]
                                actual_language = parts[1].capitalize() # Use the language from the filename
                                console.print(f"    [dim]Inferred language from filename:[/dim] {actual_language}")
                            else:
                                console.print(f"    [dim]Suffix '_{parts[1]}' not recognized as language, using default:[/dim] {language}")
                        else:
                             console.print(f"    [dim]Using default language:[/dim] {language}")
                    else:
                        console.print(f"    [dim]Using default language:[/dim] {language}")


                    # ii. use get_extension to infer the extension
                    try:
                        code_extension = get_extension(actual_language)
                        console.print(f"    [dim]Inferred extension:[/dim] {code_extension}")
                    except ValueError: # Handle case where get_extension doesn't know the language
                        console.print(f"[bold yellow]Warning:[/bold yellow] Could not determine extension for language '{actual_language}'. Using default extension '{extension}'.")
                        code_extension = extension # Fallback to the provided default extension parameter
                        success = False # Indicate potential issue

                    # iii. add the suffix extension to the prompt_name (stem)
                    input_code_filename = file_stem + code_extension
                    
                    # iv. change the directory to code_directory + path from prompt_name
                    # Interpretation: Place the code file in the code_directory, preserving
                    # any subdirectories relative to the location of the CSV file.
                    # If prompt_name_full_path is absolute, this might need adjustment.
                    # Assuming prompt paths are relative to the CSV's directory or a common root.
                    # Simpler interpretation: Just place it directly in code_directory. Let's use this.
                    input_code_path = os.path.join(code_directory, input_code_filename)
                    console.print(f"  [dim]Target code file:[/dim] {input_code_path}")


                    # Read the input code from the input_code_name
                    if not os.path.exists(input_code_path):
                         console.print(f"[bold red]Error:[/bold red] Code file not found: '{input_code_path}'")
                         success = False
                         continue # Skip to next row
                    with open(input_code_path, 'r', encoding='utf-8') as f:
                        input_code = f.read()

                except Exception as e:
                    console.print(f"[bold red]Error:[/bold red] Failed to parse filenames or read code file for row {i+1}: {e}")
                    success = False
                    continue # Skip to next row

                # Ensure we have all necessary components before calling change
                if input_prompt is None or input_code is None or change_instructions is None:
                     console.print(f"[bold red]Error:[/bold red] Missing required data (prompt, code, or instructions) for row {i+1}. Skipping.")
                     success = False
                     continue

                # --- Step 2b: Call the change function ---
                try:
                    console.print(f"  [dim]Calling LLM for change...[/dim]")
                    modified_prompt, cost, current_model_name = change(
                        input_prompt=input_prompt,
                        input_code=input_code,
                        change_prompt=change_instructions,
                        strength=strength,
                        temperature=temperature
                    )
                    console.print(f"    [dim]Change cost:[/dim] ${cost:.6f}")
                    console.print(f"    [dim]Model used:[/dim] {current_model_name}")


                    # --- Step 2c: Add cost ---
                    total_cost += cost
                    if model_name is None and current_model_name: # Capture model name on first successful call
                        model_name = current_model_name

                    # --- Step 2d: Check budget ---
                    console.print(f"  [dim]Cumulative cost:[/dim] ${total_cost:.6f} / ${budget:.2f}")
                    if total_cost > budget:
                        console.print(f"[bold yellow]Warning:[/bold yellow] Budget exceeded (£{budget:.2f}) after processing row {i+1}. Stopping.")
                        success = False # Mark as incomplete due to budget
                        # Do not add the result from the call that exceeded the budget
                        break # Exit the loop

                    # --- Step 2e: Add successful result ---
                    list_of_jsons.append({
                        "file_name": prompt_name_from_csv, # Use original prompt name as key
                        "modified_prompt": modified_prompt
                    })
                    console.print(f"  [green]Successfully processed change for:[/green] {prompt_name_from_csv}")


                except Exception as e:
                    console.print(f"[bold red]Error:[/bold red] Failed to process change for '{prompt_name_from_csv}': {e}")
                    success = False
                    # Continue to the next row even if one fails

    except FileNotFoundError:
        console.print(f"[bold red]Error:[/bold red] CSV file not found at '{csv_file}'")
        return False, [], 0.0, None
    except IOError as e:
        console.print(f"[bold red]Error:[/bold red] Could not read CSV file '{csv_file}': {e}")
        return False, [], 0.0, None
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred during CSV processing:[/bold red] {e}")
        return False, [], total_cost, model_name # Return potentially partial results

    # --- Step 3: Return results ---
    if not list_of_jsons and success:
         console.print("[yellow]Warning:[/yellow] CSV file processed, but no valid rows found or processed successfully.")
    elif not success:
         console.print("[yellow]Processing finished with errors or budget exceeded.[/yellow]")
    else:
         console.print("[green]CSV processing finished successfully.[/green]")
         
    console.print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
    console.print(f"[bold]Model Used:[/bold] {model_name if model_name else 'N/A'}")
    console.print(f"[bold]Number of successful changes:[/bold] {len(list_of_jsons)}")


    return success, list_of_jsons, total_cost, model_name if model_name else "N/A"

# Example usage (assuming this file is part of a package structure)
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
temp_prompt_dir/invalid_file.prompt,"This will fail"
temp_prompt_dir/config_yaml.prompt,"Increase timeout value"
"""
    with open("temp_changes.csv", "w") as f:
        f.write(csv_content)

    # Dummy prompt files
    with open("temp_prompt_dir/func1_python.prompt", "w") as f:
        f.write("Create a Python function for factorial.")
    with open("temp_prompt_dir/script2_javascript.prompt", "w") as f:
        f.write("Write a JS script using callbacks.")
    # invalid_file.prompt exists, but its code file won't
    with open("temp_prompt_dir/invalid_file.prompt", "w") as f:
        f.write("Some prompt.")
    with open("temp_prompt_dir/config_yaml.prompt", "w") as f:
        f.write("Describe the YAML config.")


    # Dummy code files
    with open("temp_code_dir/func1.py", "w") as f:
        f.write("def factorial(n):\n  if n == 0: return 1\n  return n * factorial(n-1)\n")
    with open("temp_code_dir/script2.js", "w") as f:
        f.write("function fetchData(url, callback) { /* ... */ }")
    # No code file for invalid_file
    with open("temp_code_dir/config.yaml", "w") as f:
        f.write("timeout: 10s\nretries: 3\n")


    # Dummy internal modules (replace with actual imports if running within package)
    # Mocking the internal functions for standalone execution
    def mock_change(input_prompt, input_code, change_prompt, strength, temperature):
        # Simulate cost and model name
        cost = 0.001 * len(change_prompt) 
        model = "mock-gpt-4"
        # Simulate success or failure based on input
        if "invalid" in input_prompt.lower():
             raise ValueError("Simulated model error for invalid input.")
        modified_prompt = f"Original Prompt: {input_prompt}\n---\nChange Applied: {change_prompt}\n---\nModified Code Hint:\n{input_code[:50]}...\n(Strength: {strength}, Temp: {temperature})"
        return modified_prompt, cost, model

    def mock_get_extension(language_name):
        lang_map = {
            "Python": ".py",
            "Javascript": ".js", # Note: Case difference from prompt example
            "Yaml": ".yaml",
            "Makefile": "" # Example from prompt
        }
        if language_name in lang_map:
            return lang_map[language_name]
        else:
            # Match behavior of raising ValueError if unknown
            raise ValueError(f"Unknown language: {language_name}")

    # Replace the actual imports with mocks for the example
    change = mock_change
    get_extension = mock_get_extension

    console.print("\n[bold magenta]=== Running Example Usage ===[/bold magenta]")

    # Call the function
    success_status, results, final_cost, final_model = process_csv_change(
        csv_file="temp_changes.csv",
        strength=0.6,
        temperature=0.1,
        code_directory="temp_code_dir",
        language="Python", # Default language
        extension=".txt",   # Default extension (used if get_extension fails)
        budget=0.1 # Set a budget
    )

    console.print("\n[bold magenta]=== Example Usage Results ===[/bold magenta]")
    console.print(f"Overall Success: {success_status}")
    console.print(f"Total Cost: ${final_cost:.6f}")
    console.print(f"Model Name: {final_model}")
    console.print("Modified Prompts JSON:")
    console.print(results)

    # Cleanup dummy files
    # import shutil
    # os.remove("temp_changes.csv")
    # shutil.rmtree("temp_code_dir")
    # shutil.rmtree("temp_prompt_dir")
    # console.print("\n[bold magenta]=== Cleaned up temporary files ===[/bold magenta]")
