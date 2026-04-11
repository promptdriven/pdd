from __future__ import annotations
import difflib
import os
import re
from typing import Callable, List, Optional, Tuple
from pathlib import Path
from rich import print
from pydantic import BaseModel, Field

from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .auto_include import auto_include
from .preprocess import preprocess
from . import DEFAULT_TIME, DEFAULT_STRENGTH
try:
    from .config import get_config
except ImportError:
    def get_config():
        return {"project_root": "."}

from rich.console import Console

console = Console()


class InsertIncludesOutput(BaseModel):
    output_prompt: str = Field(description="The prompt with dependencies inserted")


def _remove_redundant_content(prompt: str, inserted_includes: List[str]) -> str:
    """Remove inline content from the prompt that duplicates included documents.

    For each included file path, read the file and compare contiguous blocks
    (3+ lines) in the prompt against the file content using
    ``difflib.SequenceMatcher``.  Blocks with a similarity ratio >= 0.80 are
    removed.

    Args:
        prompt: The prompt string to clean.
        inserted_includes: List of file paths whose content may be duplicated
            inline in the prompt.

    Returns:
        The cleaned prompt with redundant blocks removed.
    """
    if not inserted_includes:
        return prompt

    # Collect content of each included file.
    # Paths may be repo-root-relative, so resolve against project root
    # rather than relying on CWD.
    try:
        _cfg = get_config()
        _project_root = Path(_cfg.get("project_root", ".")).resolve()
    except Exception:
        _project_root = Path(".").resolve()

    included_contents: List[str] = []
    for file_path in inserted_includes:
        try:
            path = Path(file_path)
            if not path.is_absolute():
                path = _project_root / path
            if path.is_file():
                included_contents.append(path.read_text(encoding="utf-8", errors="replace"))
        except Exception:
            # Skip files that cannot be read
            continue

    if not included_contents:
        return prompt

    lines = prompt.splitlines(keepends=True)
    # Track which lines to keep
    keep = [True] * len(lines)

    # Slide a window of varying size (min 3 lines) over the prompt
    min_block = 3
    i = 0
    while i < len(lines):
        if not keep[i]:
            i += 1
            continue

        # Try the largest possible block first, then shrink
        best_end = -1
        for end in range(len(lines), i + min_block - 1, -1):
            block_text = "".join(lines[i:end])
            # Skip blocks that are only whitespace
            if not block_text.strip():
                continue

            for content in included_contents:
                ratio = difflib.SequenceMatcher(
                    None, block_text, content
                ).ratio()
                if ratio >= 0.80:
                    best_end = end
                    break

            if best_end != -1:
                break

        if best_end != -1:
            for j in range(i, best_end):
                keep[j] = False
            i = best_end
        else:
            i += 1

    cleaned = "".join(line for line, k in zip(lines, keep) if k)
    return cleaned


def insert_includes(
    input_prompt: str,
    directory_path: str,
    csv_filename: str,
    prompt_filename: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
    progress_callback: Optional[Callable[[int, int], None]] = None,
    include_docs: bool = False,
    max_workers: int = 1,
    dedup: bool = True,
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
        include_docs (bool, optional): Whether to include documentation files in
            dependency discovery. Defaults to False. Passed through to auto_include.
        max_workers (int, optional): Number of parallel workers for file
            summarization. Defaults to 1. Passed through to auto_include.
        dedup (bool, optional): Whether to remove redundant inline content after
            inserting includes. Defaults to True.

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
            console.print("[blue]Loaded and preprocessed insert_includes_LLM prompt template[/blue]")

        # Step 2: Read the CSV file (create with header if missing)
        try:
            with open(csv_filename, 'r') as file:
                csv_content = file.read()
        except FileNotFoundError:
            if verbose:
                console.print(f"[yellow]CSV file {csv_filename} not found. Creating empty CSV.[/yellow]")
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
            include_docs=include_docs,
            max_workers=max_workers,
        )

        if verbose:
            console.print("[blue]Retrieved dependencies using auto_include[/blue]")
            console.print(f"Dependencies found: {dependencies}")

        # Step 4: Apply <update> blocks deterministically
        update_blocks = re.findall(r'<update>(.*?)</update>', dependencies, re.DOTALL)
        new_blocks = re.findall(r'<new>(.*?)</new>', dependencies, re.DOTALL)

        output_prompt = input_prompt
        for update_block in update_blocks:
            match = re.search(r'<include[^>]*>(.*?)</include>', update_block, re.DOTALL)
            if match:
                file_path = match.group(1).strip()
                # Extract only the <include>...</include> tag from the update block,
                # ignoring any surrounding content (comments, whitespace, etc.)
                include_tag_match = re.search(r'<include[^>]*>.*?</include>', update_block, re.DOTALL)
                replacement = include_tag_match.group(0) if include_tag_match else update_block.strip()
                escaped_path = re.escape(file_path)
                pattern = r'<include[^>]*>\s*' + escaped_path + r'\s*</include>'
                new_prompt = re.sub(pattern, replacement, output_prompt)
                # If the full path didn't match, try matching by basename.
                # This handles cases where the prompt has a bare filename
                # (e.g. "file.py") but the update block has a qualified path
                # (e.g. "dir/file.py"), or vice-versa.
                # Only apply basename fallback when it uniquely matches a single
                # include in the prompt, to avoid nondeterministic replacements
                # when multiple files share the same basename (e.g. a/utils.py
                # vs b/utils.py).
                if new_prompt == output_prompt:
                    basename = os.path.basename(file_path)
                    escaped_basename = re.escape(basename)
                    pattern = r'<include[^>]*>\s*(?:[^\s<]*/)*' + escaped_basename + r'\s*</include>'
                    matches = re.findall(pattern, output_prompt)
                    if len(matches) == 1:
                        new_prompt = re.sub(pattern, replacement, output_prompt)
                    elif len(matches) > 1 and verbose:
                        console.print(f"[yellow]Warning: basename '{basename}' matches {len(matches)} includes; skipping ambiguous update[/yellow]")
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
                console.print("[green]Successfully inserted includes into prompt[/green]")
                console.print(f"Total cost: ${total_cost:.6f}")
                console.print(f"Model used: {model_name}")
        else:
            model_name = auto_include_model
            total_cost = auto_include_cost
            if verbose:
                console.print("[green]No new includes to insert, skipping LLM call[/green]")

        # Step 6: Dedup — remove inline content that duplicates included documents
        if dedup and dependencies.strip():
            # Extract all <include>...</include> file paths from the dependencies
            include_paths = re.findall(
                r'<include[^>]*>(.*?)</include>', dependencies, re.DOTALL
            )
            include_paths = [p.strip() for p in include_paths if p.strip()]
            if include_paths:
                output_prompt = _remove_redundant_content(output_prompt, include_paths)
                if verbose:
                    console.print(
                        f"[blue]Dedup: checked {len(include_paths)} included file(s) "
                        f"for redundant inline content[/blue]"
                    )

        return (
            output_prompt,
            csv_output,
            total_cost,
            model_name
        )

    except Exception as e:
        console.print(f"[red]Error in insert_includes: {str(e)}[/red]")
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

        console.print("\n[bold green]Results:[/bold green]")
        console.print(f"[white]Output Prompt:[/white]\n{output_prompt}")
        console.print(f"\n[white]CSV Output:[/white]\n{csv_output}")
        console.print(f"[white]Total Cost: ${total_cost:.6f}[/white]")
        console.print(f"[white]Model Used: {model_name}[/white]")

    except Exception as e:
        console.print(f"[red]Error in main: {str(e)}[/red]")

if __name__ == "__main__":
    main()
