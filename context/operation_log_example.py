"""
Example demonstrating usage of the operation_log module for PDD operation tracking.

This module provides shared logging infrastructure for tracking all PDD operations,
including manual CLI invocations and sync-initiated operations.
"""

import click
from pathlib import Path
from typing import Tuple, Optional

# In a real project, this would be an installed package import
from pdd.operation_log import (
    load_operation_log,
    create_log_entry,
    create_manual_log_entry,
    update_log_entry,
    append_log_entry,
    log_event,
    infer_module_identity,
    save_fingerprint,
    save_run_report,
    clear_run_report,
    log_operation,
)


def demonstrate_log_operations():
    """
    Demonstrates basic log file operations.
    """
    basename = "calculator"
    language = "python"

    # Load existing log entries
    entries = load_operation_log(basename, language)
    print(f"Loaded {len(entries)} existing log entries")

    # Create a new log entry for sync-initiated operation
    entry = create_log_entry(
        operation="generate",
        reason="Prompt changed",
        invocation_mode="sync",
        estimated_cost=0.5,
        confidence=0.95,
        decision_type="generate",
    )
    print(f"Created sync log entry: {entry['operation']}")

    # Create a log entry for manual CLI invocation
    manual_entry = create_manual_log_entry(operation="fix")
    print(f"Created manual log entry: {manual_entry['operation']}")

    # Update entry with execution results
    updated_entry = update_log_entry(
        entry=entry,
        success=True,
        cost=0.192,
        model="gemini/gemini-3-pro-preview",
        duration=6.81,
        error=None,
    )
    print(f"Updated entry - success: {updated_entry['success']}, cost: {updated_entry['actual_cost']}")

    # Append entry to log file
    append_log_entry(basename, language, updated_entry)
    print("Appended entry to log file")

    # Log a special event
    log_event(basename, language, "budget_warning", {"remaining": 0.5})
    print("Logged budget warning event")


def demonstrate_module_identity():
    """
    Demonstrates module identity inference from prompt file paths.
    """
    # Standard prompt path
    basename, language = infer_module_identity("prompts/calculator_python.prompt")
    print(f"Inferred: basename={basename}, language={language}")

    # Full path
    basename, language = infer_module_identity("/path/to/project/prompts/sync_orchestration_python.prompt")
    print(f"Inferred from full path: basename={basename}, language={language}")


def demonstrate_state_management():
    """
    Demonstrates state file management (fingerprints and run reports).
    """
    basename = "calculator"
    language = "python"
    paths = {
        "prompt": Path("prompts/calculator_python.prompt"),
        "code": Path("pdd/calculator.py"),
        "example": Path("context/calculator_example.py"),
        "test": Path("tests/test_calculator.py"),
    }

    # Save run report after test execution
    run_report = {
        "tests_passed": 10,
        "tests_failed": 0,
        "coverage": 95.2,
    }
    save_run_report(basename, language, run_report)
    print("Saved run report")

    # After a successful regeneration that mutates code/tests/etc., invalidate
    # the stale runtime-verification report BEFORE writing the fresh
    # fingerprint. Required ordering (issue #1057): clear_run_report() then
    # save_fingerprint(). If clear_run_report fails or the stale _run.json
    # still exists afterward, skip save_fingerprint() so a fresh fingerprint
    # never coexists with stale runtime state.
    from pdd.operation_log import get_run_report_path

    try:
        clear_run_report(basename, language)
        print("Cleared run report")
    except Exception as exc:  # noqa: BLE001 - non-fatal cleanup warning
        print(f"WARN: clear_run_report failed: {exc}")

    if get_run_report_path(basename, language).exists():
        print(
            "WARN: stale run report still present; skipping save_fingerprint "
            "to avoid partial-sync state (issue #1057)"
        )
    else:
        save_fingerprint(
            basename=basename,
            language=language,
            operation="generate",
            paths=paths,
            cost=0.192,
            model="gemini/gemini-3-pro-preview",
        )
        print("Saved fingerprint")


# Example CLI command using the @log_operation decorator
@click.command()
@click.option("--prompt-file", type=click.Path(exists=True), required=True)
@click.option("--output", type=click.Path(), required=False)
@log_operation("generate", updates_fingerprint=True, clears_run_report=True)
def generate(prompt_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """
    Example command decorated with @log_operation.

    The decorator automatically:
    1. Infers module identity from prompt_file
    2. Creates initial log entry
    3. Executes the wrapped function
    4. Updates log entry with results
    5. On success only: clears stale run report (clears_run_report=True)
       before saving fingerprint, so a failed command never erases existing
       runtime verification state (issue #1057)
    6. Saves fingerprint on success (updates_fingerprint=True)
    """
    # Simulate generation
    generated_output = "Generated code..."
    cost = 0.192
    model = "gemini/gemini-3-pro-preview"
    return generated_output, cost, model


@click.command()
@click.option("--prompt-file", type=click.Path(exists=True), required=True)
@log_operation("fix", updates_fingerprint=True, updates_run_report=True)
def fix(prompt_file: str) -> Tuple[str, float, str]:
    """
    Example fix command that updates both fingerprint and run report on success.
    """
    fixed_output = "Fixed code..."
    cost = 0.45
    model = "claude-3-5-sonnet"
    return fixed_output, cost, model


if __name__ == "__main__":
    print("=== Log Operations Demo ===")
    demonstrate_log_operations()

    print("\n=== Module Identity Demo ===")
    demonstrate_module_identity()

    print("\n=== State Management Demo ===")
    demonstrate_state_management()
