from __future__ import annotations
import os
from typing import Callable, Optional, Tuple
from pathlib import Path
from rich import print
from pydantic import BaseModel, Field
import re

from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .auto_include import auto_include
from .preprocess import preprocess
from . import DEFAULT_TIME, DEFAULT_STRENGTH

class InsertIncludesOutput(BaseModel):
    output_prompt: str = Field(description="The prompt with dependencies inserted")

def insert_includes(
    input_prompt: str,
    directory_path: str,
    csv_filename: str,
    prompt_filename: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> Tuple[str, str, float, str]:
    """
    Determine needed dependencies and insert them into a prompt.

    Args:
        input_prompt (str): The prompt to process
        directory_path (str): Directory path where the prompt file is located
        csv_filename (str): Name of the CSV file containing dependencies
        prompt_filename (Optional[str]): The prompt filename being processed,
            used to filter out self-referential example files
        strength (float): Strength parameter for the LLM model
        temperature (float): Temperature parameter for the LLM model
        time (float): Time budget for the LLM model
        verbose (bool, optional): Whether to print detailed information. Defaults to False.
        progress_callback (Optional[Callable[[int, int], None]]): Callback for progress updates.
            Called with (current, total) for each file processed.

    Returns:
        Tuple[str, str, float, str]: Tuple containing:
            - output_prompt: The prompt with dependencies inserted
            - csv_output: Complete CSV output from auto_include
            - total_cost: Total cost of running the function
            - model_name: Name of the LLM model used
    """
    try:
        # Step 1: Load and preprocess the prompt template
        insert_includes_prompt = load_prompt_template("insert_includes_LLM")
        if not insert_includes_prompt:
            raise ValueError("Failed to load insert_includes_LLM.prompt template")

        processed_prompt = preprocess(
            insert_includes_prompt,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["actual_prompt_to_update", "actual_dependencies_to_insert"]
        )

        if verbose:
            print("[blue]Loaded and preprocessed insert_includes_LLM prompt template[/blue]")

        # Step 2: Read the CSV file (create with header if missing)
        try:
            with open(csv_filename, 'r') as file:
                csv_content = file.read()
        except FileNotFoundError:
            if verbose:
                print(f"[yellow]CSV file {csv_filename} not found. Creating empty CSV.[/yellow]")
            csv_content = "full_path,file_summary,key_exports,dependencies,content_hash\n"
            Path(csv_filename).write_text(csv_content)

        # Step 3: Get dependencies using auto_include
        dependencies, csv_output, auto_include_cost, auto_include_model = auto_include(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_file=csv_content,
            prompt_filename=prompt_filename,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            progress_callback=progress_callback,
            csv_path=csv_filename,
        )

        if verbose:
            print("[blue]Retrieved dependencies using auto_include[/blue]")
            print(f"Dependencies found: {dependencies}")

        # Step 4: Apply <update> blocks deterministically
        update_blocks = re.findall(r'<update>(.*?)</update>', dependencies, re.DOTALL)
        new_blocks = re.findall(r'<new>(.*?)</new>', dependencies, re.DOTALL)

        output_prompt = input_prompt
        for update_block in update_blocks:
            match = re.search(r'<include[^>]*>(.*?)</include>', update_block, re.DOTALL)
            if match:
                file_path = match.group(1).strip()
                escaped_path = re.escape(file_path)
                pattern = r'<include[^>]*>\s*' + escaped_path + r'\s*</include>'
                new_prompt = re.sub(pattern, update_block.strip(), output_prompt)
                # If the full path didn't match, try matching by basename.
                # This handles cases where the prompt has a bare filename
                # (e.g. "file.py") but the update block has a qualified path
                # (e.g. "dir/file.py"), or vice-versa.
                if new_prompt == output_prompt:
                    basename = os.path.basename(file_path)
                    escaped_basename = re.escape(basename)
                    pattern = r'<include[^>]*>\s*(?:[^\s<]*/)*' + escaped_basename + r'\s*</include>'
                    new_prompt = re.sub(pattern, update_block.strip(), output_prompt)
                output_prompt = new_prompt

        if not update_blocks and not new_blocks and dependencies.strip():
            new_dependencies_str = dependencies
            has_new = True
        else:
            new_dependencies_str = "\n".join([f"<new>{block}</new>" for block in new_blocks])
            has_new = bool(new_blocks)

        # Steps 5 & 6: Invoke LLM if <new> blocks exist, otherwise skip
        if has_new:
            response = llm_invoke(
                prompt=processed_prompt,
                input_json={
                    "actual_prompt_to_update": output_prompt,
                    "actual_dependencies_to_insert": new_dependencies_str
                },
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                output_pydantic=InsertIncludesOutput
            )

            if not response or 'result' not in response:
                raise ValueError("Failed to get valid response from LLM model")

            result: InsertIncludesOutput = response['result']
            model_name = response['model_name']
            total_cost = response['cost'] + auto_include_cost
            output_prompt = result.output_prompt

            if verbose:
                print("[green]Successfully inserted includes into prompt[/green]")
                print(f"Total cost: ${total_cost:.6f}")
                print(f"Model used: {model_name}")
        else:
            model_name = auto_include_model
            total_cost = auto_include_cost
            if verbose:
                print("[green]No new includes to insert, skipping LLM call[/green]")

        return (
            output_prompt,
            csv_output,
            total_cost,
            model_name
        )

    except Exception as e:
        print(f"[red]Error in insert_includes: {str(e)}[/red]")
        raise

def main():
    """Example usage of the insert_includes function."""
    # Example input
    input_prompt = """% Generate a Python function that processes data
    <include>data_processing.py</include>
    """
    directory_path = "./src"
    csv_filename = "dependencies.csv"
    strength = 0.7
    temperature = 0.5

    try:
        output_prompt, csv_output, total_cost, model_name = insert_includes(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_filename=csv_filename,
            strength=strength,
            temperature=temperature,
            time=0.25,
            verbose=True
        )

        print("\n[bold green]Results:[/bold green]")
        print(f"[white]Output Prompt:[/white]\n{output_prompt}")
        print(f"\n[white]CSV Output:[/white]\n{csv_output}")
        print(f"[white]Total Cost: ${total_cost:.6f}[/white]")
        print(f"[white]Model Used: {model_name}[/white]")

    except Exception as e:
        print(f"[red]Error in main: {str(e)}[/red]")

if __name__ == "__main__":
    main()
