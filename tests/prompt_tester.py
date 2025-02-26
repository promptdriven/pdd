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
import difflib
import re

from rich.console import Console
from rich.text import Text
from rich.panel import Panel
from rich.syntax import Syntax
from rich.table import Table

# Absolute import from pdd.llm_invoke (internal module)
from pdd.llm_invoke import llm_invoke

# For dynamic model creation
from pydantic import create_model, ValidationError, BaseModel, Field

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
    """Generate a unified diff view using Rich text formatting"""
    diff = Text()
    
    # Convert to strings and split into lines
    def format_value(value):
        if isinstance(value, str):
            # Handle strings with escaped newlines
            return '\n'.join(value.replace('\\n', '\n').splitlines())
        if isinstance(value, (dict, list)):
            return json.dumps(value, indent=2)
        return str(value)
    
    expected_str = format_value(expected)
    actual_str = format_value(actual)
    
    expected_lines = expected_str.splitlines()
    actual_lines = actual_str.splitlines()
    
    # Generate unified diff
    diff_lines = difflib.unified_diff(
        expected_lines, actual_lines,
        fromfile='Expected', tofile='Actual',
        lineterm=''
    )
    
    # Colorize diff output
    for line in diff_lines:
        if line.startswith('+++') or line.startswith('---'):
            diff.append(line + '\n', style="bold cyan")
        elif line.startswith('@@'):
            diff.append(line + '\n', style="bold yellow")
        elif line.startswith('+'):
            diff.append(line + '\n', style="green")
        elif line.startswith('-'):
            diff.append(line + '\n', style="red")
        else:
            diff.append(line + '\n', style="white")
    
    return diff

def load_nested_files(data, json_ref_dir):
    print(f"Processing in directory: {json_ref_dir}")  # Debug line
    if isinstance(data, dict):
        return {k: load_nested_files(v, json_ref_dir) for k, v in data.items()}
    elif isinstance(data, list):
        return [load_nested_files(item, json_ref_dir) for item in data]
    elif isinstance(data, str):
        # Only process non-empty strings as file paths
        if data:  # This is the key check added
            file_path = os.path.join(json_ref_dir, data)
            print(f"Checking path: {file_path}")  # Debug line
            if os.path.exists(file_path):
                print(f"Loading file: {file_path}")  # Debug line
                try:
                    return load_json_from_file(file_path)
                except ValueError:
                    return load_file_content(file_path)
        # Return original data (including empty strings) if not a valid file path
        return data
    return data

def compare_dicts(expected_dict: dict, actual_dict: dict, path: str = "") -> list[tuple[str, Text]]:
    """
    Recursively compare two dicts.
    Return a list of (key_path, diff_text_obj) for each mismatched entry.
    """
    diffs = []
    console = Console()  # Create a Rich console instance
    
    for key in expected_dict:
        new_path = f"{path}.{key}" if path else key
        expected_val = expected_dict[key]
        actual_val = actual_dict.get(key, "<MISSING>")

        # Print comparison result for each key using Rich console
        if expected_val == actual_val:
            console.print(f"[green]✓[/green] Comparing {new_path}")
            console.print(f"  Expected: [blue]{str(expected_val)}[/blue]")
            console.print(f"  Actual:   [blue]{str(actual_val)}[/blue]")
        else:
            console.print(f"[red]✗[/red] Comparing {new_path}")
            console.print(f"  Expected: [blue]{str(expected_val)}[/blue]")
            console.print(f"  Actual:   [red]{str(actual_val)}[/red]")
        console.print()  # Add blank line for readability

        if isinstance(expected_val, dict):
            if not isinstance(actual_val, dict):
                diff = Text()
                diff.append("Dictionary key mismatch: ", style="yellow")
                diff.append(new_path, style="bold yellow")
                diff.append(f"\nExpected dict, got {type(actual_val).__name__}\n")
                diff.append(diff_text(expected_val, actual_val))
                diffs.append((new_path, diff))
            else:
                diffs.extend(compare_dicts(expected_val, actual_dict.get(key, {}), new_path))
        elif isinstance(expected_val, list):
            if not isinstance(actual_val, list):
                diff = Text()
                diff.append("List key mismatch: ", style="yellow")
                diff.append(new_path, style="bold yellow")
                diff.append(f"\nExpected list, got {type(actual_val).__name__}\n")
                diff.append(diff_text(expected_val, actual_val))
                diffs.append((new_path, diff))
            else:
                for i, (e_item, a_item) in enumerate(zip(expected_val, actual_val)):
                    if json.dumps(e_item, sort_keys=True) != json.dumps(a_item, sort_keys=True):
                        item_path = f"{new_path}[{i}]"
                        diff = Text()
                        diff.append("Array item mismatch: ", style="yellow")
                        diff.append(item_path, style="bold yellow")
                        diff.append("\n")
                        diff.append(diff_text(e_item, a_item))
                        diffs.append((item_path, diff))
        else:
            if expected_val != actual_val:
                key_diff = Text()
                key_diff.append("Key mismatch: ", style="yellow")
                key_diff.append(new_path, style="bold yellow")
                key_diff.append("\n")
                key_diff.append(diff_text(expected_val, actual_val))
                diffs.append((new_path, key_diff))
    return diffs

# --- Main function for testing the prompt ---

class ComparisonStrategy:
    """Base class for comparison strategies"""
    def compare_values(self, expected, actual, path: str = "") -> tuple[bool, Text]:
        raise NotImplementedError
        
    def aggregate_results(self, results: list[tuple[bool, Text]]) -> tuple[bool, Text]:
        overall_result = all(result[0] for result in results)
        combined_diff = Text().join(result[1] for result in results)
        return overall_result, combined_diff

class DirectComparisonStrategy(ComparisonStrategy):
    """Strategy for direct value comparisons"""
    def __init__(self, console):
        self.console = console

    def compare_values(self, expected, actual, path: str = "") -> tuple[bool, Text]:
        if expected == actual:
            if path:  # Only print if path exists
                self.console.print(f"[Direct Check] Key {path}: Matched", style="green")
            return True, Text()
            
        if path:  # Only print if path exists
            self.console.print(f"[Direct Check] Key {path}: Mismatch", style="red")
        diff = Text()
        diff.append("Mismatch: ", style="yellow")
        diff.append(path, style="bold yellow") if path else None
        diff.append("\n")
        diff.append(diff_text(expected, actual))
        return False, diff

class LLMComparisonStrategy(ComparisonStrategy):
    """Strategy for LLM-based equivalence checks"""
    def __init__(self, strength: float, temperature: float, console):
        self.strength = strength
        self.temperature = temperature
        self.console = console

    def compare_values(self, expected, actual, path: str = "") -> tuple[bool, Text]:
        class ComparisonResult(BaseModel):
            explanations: list[str] = Field(description="List of similarities AND differences between outputs")
            answer: str = Field(description="Final equivalence verdict: YES or NO")

        comparison_prompt = (
            "Analyze these outputs for equivalence. Identify what is THE SAME and what is DIFFERENT.\n"
            "Return JSON with:\n"
            "1. 'explanations' - list of key similarities AND differences\n"
            "2. 'answer' - YES if outputs are equivalent despite differences, NO otherwise\n\n"
            "Expected Output:\n<expected_output>\n{expected}\n</expected_output>\n\n"
            "Actual Output:\n<actual_output>\n{actual}\n</actual_output>"
        )

        expected_str = json.dumps(expected, indent=2) if isinstance(expected, (dict, list)) else str(expected)
        actual_str = json.dumps(actual, indent=2) if isinstance(actual, (dict, list)) else str(actual)
        
        try:
            comp_response = llm_invoke(
                prompt=comparison_prompt,
                input_json={"expected": expected_str, "actual": actual_str},
                strength=self.strength,
                temperature=self.temperature,
                verbose=False,
                output_pydantic=ComparisonResult
            )
            comp_result = comp_response.get("result", None)
            
            explanations = []
            if comp_result:
                explanations = [f"[{path}] {explanation}" for explanation in comp_result.explanations]
                passed = comp_result.answer.strip().lower() == "yes"
                status = "Equivalent" if passed else "Not Equivalent"
                if path:  # Only print if path exists
                    self.console.print(f"[LLM Check] Key {path}: {status}", style="green" if passed else "red")
            else:
                passed = False
                explanations = [f"[{path}] No comparison result"]
                self.console.print(f"[red]Key {path}: Comparison Failed[/red]")
            
            return passed, Text("\n".join(explanations), style="green" if passed else "red")
        except Exception as e:
            self.console.print(f"[red]Key {path}: Error - {str(e)}[/red]")
            return False, Text(f"[{path}] Comparison failed: {str(e)}", style="red")

def compare_structures(expected, actual, strategy: ComparisonStrategy, path: str = "") -> tuple[bool, Text]:
    """Recursive comparison using the specified strategy"""
    if isinstance(expected, dict) and isinstance(actual, dict):
        results = []
        for key in expected:
            new_path = f"{path}.{key}" if path else key
            result = compare_structures(
                expected[key], 
                actual.get(key, "<MISSING>"), 
                strategy,
                new_path
            )
            results.append(result)
        return strategy.aggregate_results(results)
        
    elif isinstance(expected, list) and isinstance(actual, list):
        results = []
        for i, (e_item, a_item) in enumerate(zip(expected, actual)):
            result = compare_structures(
                e_item, 
                a_item, 
                strategy,
                f"{path}[{i}]" if path else f"[{i}]"
            )
            results.append(result)
        return strategy.aggregate_results(results)
        
    else:
        return strategy.compare_values(expected, actual, path)

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
            expected_str = ""
            actual_str = ""
            passed = False
            diff_output = None

            if eval_type.lower() == "deterministic":
                strategy = DirectComparisonStrategy(console)
                passed, diff_output = compare_structures(expected_output, actual_result, strategy)
                
            elif eval_type.lower() == "llm_equivalent":
                strategy = LLMComparisonStrategy(strength, temperature, console)
                passed, diff_output = compare_structures(expected_output, actual_result, strategy)
            else:
                # For non-deterministic structured tests
                if expected_is_structured:
                    diff_output = Text()
                    actual_dict = (actual_result if isinstance(actual_result, dict)
                                   else actual_result.model_dump())
                    
                    # Compare recursively and get granular diffs
                    subdiffs = compare_dicts(expected_output, actual_dict)
                    
                    if subdiffs:
                        passed = False
                        diff_output.append(f"[bold]Found {len(subdiffs)} differences:[/bold]\n")
                        for i, (path, diff) in enumerate(subdiffs, 1):
                            diff_output.append(f"\n[bold yellow]{i}. Mismatch at path: {path}[/bold yellow]")
                            diff_output.append(diff)
                    else:
                        passed = True
                else:
                    # Fallback: plain string comparison
                    expected_str = str(expected_output)
                    actual_str = str(actual_result)
                    if expected_str.strip() == actual_str.strip():
                        passed = True
                        diff_output = None
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