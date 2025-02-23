#!/usr/bin/env python3
"""
CLI to test prompts against test cases defined in a CSV file.
Usage example:
    python -m tests.prompter_tester prompter_to_be_tested --strength 0.5 --temperature 0.0
"""

import argparse
import csv
import json
import os
import sys
import traceback
from datetime import datetime
from pathlib import Path
from typing import Any

from rich.console import Console
from rich.text import Text
from rich.panel import Panel
from rich.syntax import Syntax
from rich.table import Table

# Absolute import from pdd.llm_invoke (internal module)
from pdd.llm_invoke import llm_invoke

# For dynamic model creation
from pydantic import create_model, ValidationError

# --- Internal helper functions (could be placed in internal modules with relative imports) ---

def load_file_content(path: str) -> str:
    if not os.access(path, os.R_OK):
        raise PermissionError(f"Cannot read file: {path}")
    with open(path, 'r') as f:
        return f.read()

def load_json_from_file(file_path: str):
    """Helper to load JSON content from a file."""
    content = load_file_content(file_path)
    try:
        return json.loads(content)
    except json.JSONDecodeError as exc:
        raise ValueError(f"Error decoding JSON file {file_path}: {exc}")

def create_dynamic_model(expected_dict: dict):
    """
    Create a dynamic Pydantic model from the expected dictionary.
    Each key is given a type based on the type() of the expected value.
    """
    fields = {}
    for key, val in expected_dict.items():
        # For simplicity, we directly use the type of the value.
        fields[key] = (type(val), ...)
    # The created model will validate that these keys are present.
    DynamicModel = create_model("DynamicModel", **fields)
    return DynamicModel

def diff_text(expected: Any, actual: Any) -> Text:
    """Generate a comparison view using Rich text formatting"""
    diff = Text()
    
    # Convert complex objects to strings
    expected_str = json.dumps(expected, indent=2) if isinstance(expected, dict) else str(expected)
    actual_str = json.dumps(actual, indent=2) if isinstance(actual, dict) else str(actual)

    # Expected section
    diff.append("Expected Output:\n", style="bold green")
    diff.append(expected_str + "\n", style="green")
    
    # Divider
    diff.append("\n" + "-" * 50 + "\n", style="bold white")
    
    # Actual section
    diff.append("Actual Output:\n", style="bold red")
    diff.append(actual_str + "\n", style="red")
    
    return diff

def load_nested_files(data, json_ref_dir):
    print(f"Processing in directory: {json_ref_dir}")  # Debug line
    if isinstance(data, dict):
        return {k: load_nested_files(v, json_ref_dir) for k, v in data.items()}
    elif isinstance(data, list):
        return [load_nested_files(item, json_ref_dir) for item in data]
    elif isinstance(data, str):
        file_path = os.path.join(json_ref_dir, data)
        print(f"Checking path: {file_path}")  # Debug line
        if os.path.exists(file_path):
            print(f"Loading file: {file_path}")  # Debug line
            try:
                return load_json_from_file(file_path)
            except ValueError:
                return load_file_content(file_path)
    return data

# --- Main function for testing the prompt ---

def prompt_tester(prompt_name: str, strength: float = 0.5, temperature: float = 0.0) -> None:
    """
    Tests a prompt given by the prompt file name.
      • Reads the prompt file from ./prompts.
      • Loads the CSV with test cases from ./tests/csv.
      • For each test row, replaces key-value filenames (if string) with actual file contents.
      • Invokes the prompt using llm_invoke.
      • Compares the output to the expected output:
            - For "deterministic" tests, performs a plain string comparison.
            - Otherwise (non-deterministic), if the expected output is structured (JSON) then a key-by-key comparison
              is run with each diff pretty printed.
            - For "LLM_equivalent" tests, the equality is determined via an LLM comparison prompt.
      • Logs all results to ./output/prompt_results.log.
    """
    console = Console()

    # Ensure prompt file ends with .prompt
    if not prompt_name.endswith(".prompt"):
        prompt_file_name = prompt_name + ".prompt"
    else:
        prompt_file_name = prompt_name

    # Determine base name (without extension) for CSV and log file lookup.
    base_name = os.path.splitext(os.path.basename(prompt_file_name))[0]

    # Build file paths
    prompt_file_path = os.path.join("prompts", prompt_file_name)
    csv_file_path = os.path.join("tests", "csv", f"{base_name}.csv")
    output_file_path = os.path.join("output", f"{base_name}.log")
    # Also assume referenced JSON files for test cases and expected outputs are located in:
    # ./tests/csv/<base_name>/
    json_ref_dir = os.path.join("tests", "csv", base_name)

    log_lines = []
    log_lines.append(f"Prompt Tester Log: {datetime.now().isoformat()}")
    log_lines.append(f"Prompt file: {prompt_file_path}")
    log_lines.append(f"CSV file: {csv_file_path}")
    log_lines.append("-" * 40)

    # Step 1: Read the prompt file.
    try:
        prompt_text = load_file_content(prompt_file_path)
    except Exception as e:
        console.print(f"[red]Error: Unable to read prompt file: {e}[/red]")
        sys.exit(1)

    # Step 2: Read the CSV file
    try:
        with open(csv_file_path, "r", encoding="utf-8") as csvfile:
            reader = csv.DictReader(csvfile)
            test_rows = list(reader)
    except Exception as e:
        console.print(f"[red]Error: Unable to read CSV file: {e}[/red]")
        sys.exit(1)

    if not test_rows:
        console.print(f"[yellow]Warning: CSV file {csv_file_path} contains no test cases.[/yellow]")
        return

    total_passed = 0
    total_failed = 0

    # Process each test row.
    for idx, row in enumerate(test_rows, start=1):
        console.rule(f"Test Case {idx}")
        log_lines.append(f"\nTest Case {idx}")
        try:
            # For each row, the CSV columns: test_case, eval_type, expected_output.
            eval_type = row.get("eval_type", "deterministic").strip()
            test_case_entry = row.get("test_case", "")
            expected_entry = row.get("expected_output", "")

            # Replace key value if test_case is a string referring to a filename.
            # If the entry is non-empty and the file exists in json_ref_dir, load it as JSON.
            if test_case_entry and os.path.exists(os.path.join(json_ref_dir, test_case_entry)):
                test_case = load_json_from_file(os.path.join(json_ref_dir, test_case_entry))
            else:
                # Otherwise, assume the test_case entry itself is a JSON string.
                try:
                    test_case = json.loads(test_case_entry)
                except json.JSONDecodeError:
                    # Fallback: treat as plain string (could be input text, etc.)
                    test_case = test_case_entry

            # Similarly, replace expected_output if it is a filename in json_ref_dir.
            expected_output = None
            expected_is_structured = False
            if expected_entry and os.path.exists(os.path.join(json_ref_dir, expected_entry)):
                raw_expected = load_json_from_file(os.path.join(json_ref_dir, expected_entry))
                expected_output = raw_expected
                expected_is_structured = isinstance(raw_expected, dict)
            else:
                # Try to parse as JSON.
                try:
                    raw_expected = json.loads(expected_entry)
                    if isinstance(raw_expected, dict):
                        expected_output = raw_expected
                        expected_is_structured = True
                    else:
                        # Not a dict – handle as a simple string comparison.
                        expected_output = expected_entry
                except Exception:
                    # Fallback to raw string.
                    expected_output = expected_entry

            console.print(Panel(f"[bold]Evaluation Type:[/bold] {eval_type}", style="cyan"))
            console.print(Panel(f"[bold]Test Case:[/bold]\n{test_case}", style="green"))
            console.print(Panel(f"[bold]Expected Output:[/bold]\n{expected_output}", style="magenta"))

            # Process test_case with nested file loading
            test_case = load_nested_files(test_case, json_ref_dir)
            
            # Similarly process expected_output
            expected_output = load_nested_files(expected_output, json_ref_dir)

            # Prepare llm_invoke parameters:
            llm_kwargs = {
                "prompt": prompt_text,
                "input_json": test_case,
                "strength": strength,
                "temperature": temperature,
                "verbose": True,
            }
            # If the expected output is structured JSON then build a dynamic model.
            if expected_is_structured:
                try:
                    output_model = create_dynamic_model(expected_output)
                    llm_kwargs["output_pydantic"] = output_model
                except Exception as e:
                    raise ValueError(f"Error creating dynamic model: {e}")

            # Step 3: Invoke the prompt.
            try:
                response = llm_invoke(**llm_kwargs)
            except Exception as e:
                console.print(f"[red]Error invoking llm_invoke: {e}[/red]")
                log_lines.append(f"Error in llm_invoke: {traceback.format_exc()}")
                total_failed += 1
                continue

            # Expect response to have at least a 'result' key and optionally a 'cost' and 'model_name'.
            actual_result = response.get("result", None)
            if actual_result is None:
                console.print(f"[red]Error: llm_invoke returned no result.[/red]")
                total_failed += 1
                continue

            # Compare based on eval_type.
            passed = False
            diff_output = None

            if eval_type.lower() == "deterministic":
                # For deterministic tests, we compare the entire string.
                # If the expected_output is structured (dict) then convert actual_result to dict (or str) for comparison.
                expected_str = (
                    json.dumps(expected_output, indent=2)
                    if expected_is_structured else str(expected_output)
                )
                if expected_is_structured:
                    try:
                        # actual_result should already be a dict from our pydantic model parsing.
                        actual_dict = actual_result if isinstance(actual_result, dict) else actual_result.model_dump()
                        # Reformat for ease of comparison.
                        actual_str = json.dumps(actual_dict, indent=2)
                    except Exception:
                        actual_str = str(actual_result)
                else:
                    actual_str = str(actual_result)

                if expected_str.strip() == actual_str.strip():
                    passed = True
                else:
                    passed = False
                    diff_output = diff_text(expected_str, actual_str)

            elif eval_type.lower() == "llm_equivalent":
                # For LLM_equivalent, call llm_invoke with a comparison prompt.
                comparison_prompt = (
                    "Given two outputs below, determine if they are equivalent in meaning. "
                    "Return YES if they are equivalent and NO if they are not.\n\n"
                    "Expected Output:\n{expected}\n\nActual Output:\n{actual}"
                )
                # Prepare variables (as strings).
                expected_str = (
                    json.dumps(expected_output, indent=2)
                    if expected_is_structured else str(expected_output)
                )
                actual_str = (
                    json.dumps(actual_result, indent=2)
                    if expected_is_structured and isinstance(actual_result, dict)
                    else str(actual_result)
                )

                try:
                    comp_response = llm_invoke(
                        prompt=comparison_prompt,
                        input_json={"expected": expected_str, "actual": actual_str},
                        strength=strength,
                        temperature=temperature,
                        verbose=False
                    )
                    comp_result = comp_response.get("result", "").strip().lower()
                    if "yes" in comp_result:
                        passed = True
                    else:
                        passed = False
                        diff_output = Text("LLM judged the outputs as not equivalent.", style="red")
                except Exception as e:
                    console.print(f"[red]Error during LLM equivalence testing: {e}[/red]")
                    log_lines.append(f"Error during LLM equivalence testing: {traceback.format_exc()}")
                    passed = False
            else:
                # For non-deterministic structured tests, perform key-by-key comparisons if both expected and actual are dictionaries.
                if expected_is_structured and isinstance(actual_result, dict):
                    differences = []
                    for key in expected_output.keys():
                        expected_val = expected_output.get(key, "")
                        actual_val = actual_result.get(key, "")
                        if str(expected_val).strip() != str(actual_val).strip():
                            differences.append((key, str(expected_val), str(actual_val)))
                    if differences:
                        passed = False
                        # Build diff output per key.
                        diff_output = Text()
                        for key, exp_val, act_val in differences:
                            diff_output.append(f"\n[bold magenta]Key:[/bold magenta] {key}\n")
                            diff_output.append(diff_text(exp_val, act_val))
                    else:
                        passed = True
                else:
                    # Fallback: plain string comparison.
                    expected_str = str(expected_output)
                    actual_str = str(actual_result)
                    if expected_str.strip() == actual_str.strip():
                        passed = True
                    else:
                        passed = False
                        diff_output = diff_text(expected_str, actual_str)

            # Display the LLM response summary.
            table = Table(show_header=True, header_style="bold blue")
            table.add_column("Field")
            table.add_column("Value")
            table.add_row("Model Used", str(response.get("model_name", "N/A")))
            table.add_row("Cost", f"${response.get('cost', 0):.6f}")
            table.add_row("Strength", str(strength))
            table.add_row("Temperature", str(temperature))
            console.print(table)

            # Report the result.
            if passed:
                console.print(f"[bold green]Test Case {idx} PASSED[/bold green]")
                log_lines.append(f"Test Case {idx}: PASSED")
                total_passed += 1
            else:
                console.print(f"[bold red]Test Case {idx} FAILED[/bold red]")
                log_lines.append(f"Test Case {idx}: FAILED")
                if diff_output:
                    console.print(diff_output)
                    log_lines.append(diff_output.plain)
                total_failed += 1

            log_lines.append("-" * 40)

        except Exception as e:
            console.print(f"[red]Exception during test case {idx}: {e}[/red]")
            log_lines.append(f"Exception during test case {idx}: {traceback.format_exc()}")
            total_failed += 1

    # Final summary.
    summary = f"Total Passed: {total_passed}   Total Failed: {total_failed}"
    console.rule("[bold blue]Test Summary[/bold blue]")
    console.print(summary)

    log_lines.append("\n" + summary)

    # Write out the log file.
    try:
        os.makedirs(os.path.dirname(output_file_path), exist_ok=True)
        with open(output_file_path, "w", encoding="utf-8") as outf:
            outf.write("\n".join(log_lines))
    except Exception as e:
        console.print(f"[red]Error writing log file: {e}[/red]")

# --- CLI boilerplate ---

def main():
    parser = argparse.ArgumentParser(description="Prompt Tester CLI")
    parser.add_argument("prompt_name", type=str,
                        help="Name of the prompt to test (located in ./prompts, add .prompt if missing).")
    parser.add_argument("--strength", type=float, default=0.5,
                        help="Strength of the LLM model (default: 0.5)")
    parser.add_argument("--temperature", type=float, default=0.0,
                        help="Temperature of the LLM model (default: 0.0)")
    args = parser.parse_args()

    try:
        prompt_tester(prompt_name=args.prompt_name,
                      strength=args.strength,
                      temperature=args.temperature)
    except Exception as exc:
        Console().print(f"[red]Fatal error in prompt_tester: {exc}[/red]")
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()