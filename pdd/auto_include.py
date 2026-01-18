"""
This module provides the `auto_include` function to automatically find and
insert dependencies into a prompt.
"""
import re
from io import StringIO
from pathlib import Path
from typing import Callable, List, Optional, Set, Tuple

import pandas as pd
from pydantic import BaseModel, Field
from rich.console import Console
from rich.panel import Panel

from . import DEFAULT_TIME, DEFAULT_STRENGTH
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .summarize_directory import summarize_directory

console = Console()

class AutoIncludeOutput(BaseModel):
    """
    Pydantic model for the output of the auto_include extraction.
    """
    string_of_includes: str = Field(description="The string of includes to be added to the prompt")


def _validate_input(input_prompt: str, directory_path: str, strength: float, temperature: float):
    """Validate the inputs for the auto_include function."""
    if not input_prompt:
        raise ValueError("Input prompt cannot be empty")
    if not directory_path:
        raise ValueError("Invalid 'directory_path'.")
    if not 0 <= strength <= 1:
        raise ValueError("Strength must be between 0 and 1")
    if not 0 <= temperature <= 1:
        raise ValueError("Temperature must be between 0 and 1")


def _get_available_includes_from_csv(csv_output: str) -> list[str]:
    """Parse the CSV output and return a list of available includes."""
    if not csv_output:
        return []
    try:
        # pylint: disable=invalid-name
        dataframe = pd.read_csv(StringIO(csv_output))
        return dataframe.apply(
            lambda row: f"File: {row['full_path']}\nSummary: {row['file_summary']}",
            axis=1
        ).tolist()
    except Exception as ex:
        console.print(f"[red]Error parsing CSV: {str(ex)}[/red]")
        return []


def _load_prompts() -> tuple[str, str]:
    """Load the prompt templates."""
    auto_include_prompt = load_prompt_template("auto_include_LLM")
    extract_prompt = load_prompt_template("extract_auto_include_LLM")
    if not auto_include_prompt or not extract_prompt:
        raise ValueError("Failed to load prompt templates")
    return auto_include_prompt, extract_prompt


def _summarize(
    directory_path: str,
    csv_file: Optional[str],
    llm_kwargs: dict,
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> tuple[str, float, str]:
    """Summarize the directory."""
    return summarize_directory(
        directory_path=directory_path,
        csv_file=csv_file,
        progress_callback=progress_callback,
        **llm_kwargs
    )


def _run_llm_and_extract(
    auto_include_prompt: str,
    extract_prompt: str,
    input_prompt: str,
    available_includes: list[str],
    llm_kwargs: dict,
) -> tuple[str, float, str]:
    """Run the LLM prompts and extract the dependencies."""
    # pylint: disable=broad-except
    # Run auto_include_LLM prompt
    auto_include_response = llm_invoke(
        prompt=auto_include_prompt,
        input_json={
            "input_prompt": input_prompt,
            "available_includes": "\n".join(available_includes)
        },
        **llm_kwargs
    )
    total_cost = auto_include_response["cost"]
    model_name = auto_include_response["model_name"]

    # Run extract_auto_include_LLM prompt
    try:
        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json={"llm_output": auto_include_response["result"]},
            output_pydantic=AutoIncludeOutput,
            **llm_kwargs
        )
        total_cost += extract_response["cost"]
        model_name = extract_response["model_name"]
        dependencies = extract_response["result"].string_of_includes
    except Exception as ex:
        console.print(f"[red]Error extracting dependencies: {str(ex)}[/red]")
        dependencies = ""
    return dependencies, total_cost, model_name


def _extract_module_name(prompt_filename: Optional[str]) -> Optional[str]:
    """Extract module name from prompt filename.

    Handles various language suffixes:
    - 'prompts/agentic_fix_python.prompt' -> 'agentic_fix'
    - 'prompts/some_module_LLM.prompt' -> 'some_module'
    - 'prompts/cli_bash.prompt' -> 'cli'

    Args:
        prompt_filename: The prompt filename to extract the module name from.

    Returns:
        The module name, or None if it cannot be extracted.
    """
    if not prompt_filename:
        return None
    # Pattern: captures module name before the last underscore + language + .prompt
    # e.g., "agentic_fix_python.prompt" captures "agentic_fix"
    match = re.search(r'([^/]+)_[^_]+\.prompt$', prompt_filename)
    if match:
        return match.group(1)
    return None


def _filter_self_references(dependencies: str, module_name: Optional[str]) -> str:
    """Remove includes that reference the module's own example file.

    Args:
        dependencies: The dependencies string containing include tags.
        module_name: The module name to filter out self-references for.

    Returns:
        The dependencies string with self-referential includes removed.
    """
    if not module_name:
        return dependencies
    # Pattern matches: <...><include>context/[subdirs/]{module_name}_example.py</include></...>
    # The (?:[^/]+/)* matches zero or more subdirectory levels (e.g., backend/, frontend/)
    pattern = rf'<[^>]+><include>context/(?:[^/]+/)*{re.escape(module_name)}_example\.py</include></[^>]+>\s*'
    return re.sub(pattern, '', dependencies)


def _fix_malformed_includes(dependencies: str) -> str:
    """Fix malformed [File: ...] patterns to proper <include>...</include> format.

    The LLM sometimes outputs [File: path] instead of <include>path</include>.
    This function corrects that error.

    Args:
        dependencies: The dependencies string containing potential malformed includes.

    Returns:
        The dependencies string with [File:] patterns converted to <include> tags.
    """
    # Pattern: <tag>[File: path]</tag> or <tag>\n[File: path]\n</tag>
    pattern = r'(<[^>]+>)\s*\[File:\s*([^\]]+)\]\s*(</[^>]+>)'

    def replacer(match: re.Match) -> str:
        opening_tag = match.group(1)
        path = match.group(2).strip()  # Strip whitespace from captured path
        closing_tag = match.group(3)
        return f'{opening_tag}<include>{path}</include>{closing_tag}'

    fixed = re.sub(pattern, replacer, dependencies)
    if fixed != dependencies:
        console.print("[yellow]Warning: Fixed malformed [File:] patterns in dependencies[/yellow]")
    return fixed


def _extract_example_modules(content: str) -> Set[str]:
    """Extract module names from _example.py includes.

    Args:
        content: The string content to search for include tags.

    Returns:
        A set of module names extracted from _example.py paths.
        E.g., 'context/agentic_bug_example.py' -> 'agentic_bug'
    """
    pattern = r'<include>(.*?)</include>'
    matches = re.findall(pattern, content, re.DOTALL)
    modules = set()
    for match in matches:
        path = match.strip()
        # Match pattern: context/[subdirs/]module_name_example.py
        example_match = re.search(r'context/(?:[^/]+/)*([^/]+)_example\.py$', path)
        if example_match:
            modules.add(example_match.group(1))
    return modules


def _detect_circular_dependencies(
    current_prompt: str,
    new_dependencies: str,
    prompts_dir: Optional[str] = None
) -> List[List[str]]:
    """Detect circular dependencies through example file includes.

    Detects module-level circular dependencies where:
    - Module A's prompt includes module B's example file
    - Module B's prompt includes module A's example file

    Args:
        current_prompt: The current prompt file being processed.
        new_dependencies: The new dependencies string to check.
        prompts_dir: Optional base directory for resolving prompt paths.

    Returns:
        List of cycles found, where each cycle is a list of module names.
    """
    # Extract current module name from prompt filename
    current_module = _extract_module_name(current_prompt)
    if not current_module:
        return []

    # Extract module names from example includes in new dependencies
    new_dep_modules = _extract_example_modules(new_dependencies)
    if not new_dep_modules:
        return []

    cycles: List[List[str]] = []

    # Determine base directory for prompts
    if prompts_dir:
        base_dir = Path(prompts_dir)
    else:
        # Try to find prompts directory relative to current prompt
        current_path = Path(current_prompt)
        if current_path.parent.name == 'prompts' or 'prompts' in str(current_path):
            base_dir = current_path.parent
        else:
            base_dir = Path('prompts')

    # Extract current prompt filename for cycle reporting
    current_prompt_name = Path(current_prompt).name

    # For each module we're about to depend on, check if it depends on us
    for dep_module in new_dep_modules:
        # Find the prompt file for this module (try common patterns)
        prompt_patterns = [
            f"{dep_module}_python.prompt",
            f"{dep_module}_LLM.prompt",
            f"{dep_module}.prompt",
        ]

        for pattern in prompt_patterns:
            prompt_path = base_dir / pattern
            if prompt_path.exists():
                try:
                    content = prompt_path.read_text(encoding='utf-8')
                    # Check if this prompt includes our example file
                    dep_modules = _extract_example_modules(content)
                    if current_module in dep_modules:
                        # Found circular dependency!
                        # Use actual prompt filenames, not hardcoded suffixes
                        cycles.append([
                            current_prompt_name,
                            pattern,
                            current_prompt_name
                        ])
                except Exception:
                    pass
                break

    return cycles


def _filter_circular_dependencies(dependencies: str, cycles: List[List[str]]) -> str:
    """Remove include tags that would create circular dependencies.

    Args:
        dependencies: The dependencies string containing include tags.
        cycles: List of cycles, where each cycle is a list of prompt filenames.

    Returns:
        The dependencies string with circular dependency includes removed.
    """
    if not cycles:
        return dependencies

    # Extract module names from cycles (e.g., 'agentic_bug_python.prompt' -> 'agentic_bug')
    problematic_modules: Set[str] = set()
    for cycle in cycles:
        for prompt_name in cycle:
            # Extract module name from prompt filename using shared helper
            module_name = _extract_module_name(prompt_name)
            if module_name:
                problematic_modules.add(module_name)

    if not problematic_modules:
        return dependencies

    # Pattern to match include tags with _example.py files
    # Matches: <wrapper><include>context/[subdirs/]module_example.py</include></wrapper>
    # Using a simpler approach: find each include and check if it's problematic
    result = dependencies
    for module in problematic_modules:
        # Remove includes for this module's example file
        # Pattern: <wrapper><include>context/[subdirs/]module_example.py</include></wrapper>
        pattern = rf'<[^>]+><include>context/(?:[^/]+/)*{re.escape(module)}_example\.py</include></[^>]+>\s*'
        result = re.sub(pattern, '', result)

    return result


def _extract_includes(content: str) -> Set[str]:
    """Extract all paths from <include> tags in the content.

    Args:
        content: The string content to search.

    Returns:
        A set of paths found in <include> tags.
    """
    pattern = r'<include>(.*?)</include>'
    matches = re.findall(pattern, content, re.DOTALL)
    return {m.strip() for m in matches}


def _filter_existing_includes(input_prompt: str, dependencies: str) -> str:
    """Remove includes from dependencies that already exist in the input prompt.

    If the input prompt already has <include>path/to/file</include>, and the
    generated dependencies also have <wrapper><include>path/to/file</include></wrapper>,
    the duplicate in dependencies should be removed.

    Args:
        input_prompt: The original input prompt.
        dependencies: The generated dependencies string.

    Returns:
        The dependencies string with duplicates removed.
    """
    existing_includes = _extract_includes(input_prompt)
    if not existing_includes:
        return dependencies

    result = dependencies
    for include_path in existing_includes:
        # Remove any include block that contains this path
        # Pattern matches: <wrapper><include>path</include></wrapper>
        # We use re.escape for the path to handle special chars
        pattern = rf'<[^>]+><include>{re.escape(include_path)}</include></[^>]+>\s*'
        result = re.sub(pattern, '', result)
        
        # Also try to remove bare includes if they exist in the dependencies string
        # Pattern matches: <include>path</include> surrounded by whitespace
        pattern_bare = rf'\s*<include>{re.escape(include_path)}</include>\s*'
        result = re.sub(pattern_bare, '', result)

    return result


def auto_include(
    input_prompt: str,
    directory_path: str,
    csv_file: Optional[str] = None,
    prompt_filename: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> Tuple[str, str, float, str]:
    """
    Automatically find and insert proper dependencies into the prompt.

    Args:
        input_prompt (str): The prompt requiring includes
        directory_path (str): Directory path of dependencies
        csv_file (Optional[str]): Contents of existing CSV file
        prompt_filename (Optional[str]): The prompt filename being processed,
            used to filter out self-referential example files
        strength (float): Strength of LLM model (0-1)
        temperature (float): Temperature of LLM model (0-1)
        time (float): Time budget for LLM calls
        verbose (bool): Whether to print detailed information
        progress_callback (Optional[Callable[[int, int], None]]): Callback for progress updates.
            Called with (current, total) for each file processed.

    Returns:
        Tuple[str, str, float, str]: (dependencies, csv_output, total_cost, model_name)
    """
    # pylint: disable=broad-except
    try:
        _validate_input(input_prompt, directory_path, strength, temperature)
        
        llm_kwargs = {
            "strength": strength,
            "temperature": temperature,
            "time": time,
            "verbose": verbose
        }

        if verbose:
            console.print(Panel("Step 1: Loading prompt templates", style="blue"))

        auto_include_prompt, extract_prompt = _load_prompts()
        
        if verbose:
            console.print(Panel("Step 2: Running summarize_directory", style="blue"))

        csv_output, summary_cost, summary_model = _summarize(
            directory_path, csv_file, llm_kwargs, progress_callback
        )

        available_includes = _get_available_includes_from_csv(csv_output)
        
        if verbose:
            console.print(Panel("Step 3: Running auto_include_LLM prompt", style="blue"))

        dependencies, llm_cost, llm_model_name = _run_llm_and_extract(
            auto_include_prompt=auto_include_prompt,
            extract_prompt=extract_prompt,
            input_prompt=input_prompt,
            available_includes=available_includes,
            llm_kwargs=llm_kwargs,
        )

        # Filter out self-referential includes (module's own example file)
        module_name = _extract_module_name(prompt_filename)
        dependencies = _filter_self_references(dependencies, module_name)

        # Fix any malformed [File:] patterns from LLM output
        dependencies = _fix_malformed_includes(dependencies)

        # Detect and filter circular dependencies in prompt includes
        if prompt_filename:
            cycles = _detect_circular_dependencies(
                current_prompt=prompt_filename,
                new_dependencies=dependencies
            )
            if cycles:
                dependencies = _filter_circular_dependencies(dependencies, cycles)
                for cycle in cycles:
                    console.print(
                        f"[yellow]Warning: Filtered circular dependency: "
                        f"{' -> '.join(cycle)}[/yellow]"
                    )

        # Filter out includes that already exist in the input prompt
        dependencies = _filter_existing_includes(input_prompt, dependencies)

        total_cost = summary_cost + llm_cost
        model_name = llm_model_name or summary_model

        if verbose:
            console.print(Panel(
                (
                    f"Results:\n"
                    f"Dependencies: {dependencies}\n"
                    f"CSV Output: {csv_output}\n"
                    f"Total Cost: ${total_cost:.6f}\n"
                    f"Model Used: {model_name}"
                ),
                style="green"
            ))

        return dependencies, csv_output, total_cost, model_name

    except Exception as ex:
        console.print(f"[red]Error in auto_include: {str(ex)}[/red]")
        raise


def main():
    """Example usage of auto_include function"""
    try:
        # Example inputs
        input_prompt = "Write a function to process image data"
        directory_path = "context/c*.py"
        csv_file = (
            "full_path,file_summary,date\n"
            "context/image_utils.py,"
            "\"Image processing utilities\",2023-01-01T10:00:00"
        )

        dependencies, _, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_file=csv_file,
            strength=0.7,
            temperature=0.0,
            time=DEFAULT_TIME,
            verbose=True
        )

        console.print("\n[blue]Final Results:[/blue]")
        console.print(f"Dependencies: {dependencies}")
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print(f"Model Used: {model_name}")

    except Exception as ex:
        console.print(f"[red]Error in main: {str(ex)}[/red]")

if __name__ == "__main__":
    main()