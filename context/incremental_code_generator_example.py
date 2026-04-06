"""
Example demonstrating the usage of the `incremental_code_generator` function
from the `pdd.incremental_code_generator` module.

This example showcases three scenarios:
1. Minor change detected -> incremental patching applied
2. Major change detected -> full regeneration recommended
3. Force incremental patching despite major change detection

All LLM dependencies (llm_invoke, load_prompt_template, preprocess) are mocked
so the example runs standalone without API keys.
"""
import os
import sys
from unittest.mock import patch, MagicMock

from rich.console import Console
from rich.markdown import Markdown

# Resolve project root dynamically
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.incremental_code_generator import (
    incremental_code_generator,
    DiffAnalysis,
    CodePatchResult,
)
from pdd import DEFAULT_STRENGTH, DEFAULT_TIME

console = Console()


def build_diff_response(is_big_change: bool, cost: float = 0.001) -> dict:
    """Build a mock response for the diff_analyzer_LLM step.

    Args:
        is_big_change: Whether the diff analyzer considers this a major change.
        cost: Simulated cost in dollars.
    Returns:
        Dict matching the shape returned by llm_invoke with output_pydantic=DiffAnalysis.
    """
    return {
        "result": DiffAnalysis(
            is_big_change=is_big_change,
            change_description="Added input validation for negative numbers",
            analysis="The change adds a guard clause for negative inputs.",
        ),
        "cost": cost,
        "model_name": "mock-diff-model",
    }


def build_patch_response(patched_code: str, cost: float = 0.002) -> dict:
    """Build a mock response for the code_patcher_LLM step.

    Args:
        patched_code: The patched source code string.
        cost: Simulated cost in dollars.
    Returns:
        Dict matching the shape returned by llm_invoke with output_pydantic=CodePatchResult.
    """
    return {
        "result": CodePatchResult(
            patched_code=patched_code,
            analysis="Inserted a ValueError guard at the top of the function.",
            planned_modifications="Add `if n < 0: raise ValueError(...)` before computation.",
        ),
        "cost": cost,
        "model_name": "mock-patch-model",
    }


# --- Common inputs used across all scenarios ---
ORIGINAL_PROMPT = "Write a Python function to calculate the factorial of a number."
NEW_PROMPT = "Write a Python function to calculate the factorial with input validation (must be non-negative)."
EXISTING_CODE = """\
def factorial(n):
    if n == 0 or n == 1:
        return 1
    return n * factorial(n - 1)
"""
PATCHED_CODE = """\
def factorial(n):
    if not isinstance(n, int) or n < 0:
        raise ValueError("Input must be a non-negative integer")
    if n == 0 or n == 1:
        return 1
    return n * factorial(n - 1)
"""
LANGUAGE = "python"


def scenario_minor_change_incremental():
    """Scenario 1: Minor change detected -- incremental patching applied.

    The diff analyzer reports a small change; the code patcher produces an
    updated version.

    Inputs:
        original_prompt (str): The original specification.
        new_prompt (str): The updated specification with input validation added.
        existing_code (str): Code generated from the original prompt.
        language (str): 'python'
        strength (float): DEFAULT_STRENGTH (0-1 scale, selects LLM capability tier).
        temperature (float): 0.0 (deterministic output).
        time (float): DEFAULT_TIME (0-1, reasoning effort for the LLM).
        force_incremental (bool): False -- let the diff analyzer decide.
        verbose (bool): True -- print step-by-step details.
        preprocess_prompt (bool): True -- preprocess templates before use.

    Outputs (tuple):
        updated_code (str | None): The patched code, or None if full regen needed.
        is_incremental (bool): True if an incremental patch was applied.
        total_cost (float): Accumulated LLM cost in dollars.
        model_name (str): Name of the LLM model used for the main operation.
    """
    console.rule("[bold blue]Scenario 1: Minor change -> Incremental patch[/bold blue]")

    mock_responses = [
        build_diff_response(is_big_change=False),
        build_patch_response(patched_code=PATCHED_CODE),
    ]

    with patch("pdd.incremental_code_generator.load_prompt_template", return_value="mock_template"):
        with patch("pdd.incremental_code_generator.preprocess", return_value="mock_processed"):
            with patch("pdd.incremental_code_generator.llm_invoke", side_effect=mock_responses):
                updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
                    original_prompt=ORIGINAL_PROMPT,
                    new_prompt=NEW_PROMPT,
                    existing_code=EXISTING_CODE,
                    language=LANGUAGE,
                    strength=DEFAULT_STRENGTH,
                    temperature=0.0,
                    time=DEFAULT_TIME,
                    force_incremental=False,
                    verbose=True,
                    preprocess_prompt=True,
                )

    console.print(f"\n[bold green]is_incremental:[/bold green] {is_incremental}")
    console.print(f"[bold green]total_cost:[/bold green] ${total_cost:.6f}")
    console.print(f"[bold green]model_name:[/bold green] {model_name}")
    if updated_code:
        console.print(Markdown(f"### Updated Code:\n```python\n{updated_code.strip()}\n```"))
    console.print()


def scenario_major_change_full_regen():
    """Scenario 2: Major change detected -- full regeneration recommended.

    The diff analyzer reports a big change; the function returns None and
    is_incremental=False to signal the caller to do a full code regeneration.
    """
    console.rule("[bold yellow]Scenario 2: Major change -> Full regeneration[/bold yellow]")

    with patch("pdd.incremental_code_generator.load_prompt_template", return_value="mock_template"):
        with patch("pdd.incremental_code_generator.preprocess", return_value="mock_processed"):
            with patch("pdd.incremental_code_generator.llm_invoke", return_value=build_diff_response(is_big_change=True)):
                updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
                    original_prompt=ORIGINAL_PROMPT,
                    new_prompt="Rewrite everything to use an iterative approach with memoization and logging.",
                    existing_code=EXISTING_CODE,
                    language=LANGUAGE,
                    strength=DEFAULT_STRENGTH,
                    temperature=0.0,
                    time=DEFAULT_TIME,
                    force_incremental=False,
                    verbose=True,
                    preprocess_prompt=True,
                )

    console.print(f"\n[bold yellow]updated_code:[/bold yellow] {updated_code}")
    console.print(f"[bold yellow]is_incremental:[/bold yellow] {is_incremental}")
    console.print(f"[bold yellow]total_cost:[/bold yellow] ${total_cost:.6f}")
    console.print(f"[bold yellow]model_name:[/bold yellow] {model_name}")
    console.print()


def scenario_force_incremental():
    """Scenario 3: Force incremental even when the diff analyzer says 'big change'.

    Setting force_incremental=True overrides the diff analyzer and proceeds with
    patching regardless of the is_big_change result.
    """
    console.rule("[bold magenta]Scenario 3: Force incremental override[/bold magenta]")

    mock_responses = [
        build_diff_response(is_big_change=True),   # would normally trigger full regen
        build_patch_response(patched_code=PATCHED_CODE),
    ]

    with patch("pdd.incremental_code_generator.load_prompt_template", return_value="mock_template"):
        with patch("pdd.incremental_code_generator.preprocess", return_value="mock_processed"):
            with patch("pdd.incremental_code_generator.llm_invoke", side_effect=mock_responses):
                updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
                    original_prompt=ORIGINAL_PROMPT,
                    new_prompt=NEW_PROMPT,
                    existing_code=EXISTING_CODE,
                    language=LANGUAGE,
                    strength=DEFAULT_STRENGTH,
                    temperature=0.0,
                    time=DEFAULT_TIME,
                    force_incremental=True,
                    verbose=True,
                    preprocess_prompt=True,
                )

    console.print(f"\n[bold magenta]is_incremental:[/bold magenta] {is_incremental}")
    console.print(f"[bold magenta]total_cost:[/bold magenta] ${total_cost:.6f}")
    console.print(f"[bold magenta]model_name:[/bold magenta] {model_name}")
    if updated_code:
        console.print(Markdown(f"### Updated Code:\n```python\n{updated_code.strip()}\n```"))
    console.print()


if __name__ == "__main__":
    scenario_minor_change_incremental()
    scenario_major_change_full_regen()
    scenario_force_incremental()
    console.print("[bold green]All scenarios completed successfully.[/bold green]")
