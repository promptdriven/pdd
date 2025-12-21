from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any

from rich.console import Console

from .agentic_common import run_agentic_task
from .load_prompt_template import load_prompt_template

console = Console()


def _get_file_mtimes(root: Path) -> dict[Path, float]:
    """
    Recursively scan the directory to record file modification times.
    Excludes common ignored directories like .git, __pycache__, .venv, etc.
    """
    mtimes = {}
    ignore_dirs = {".git", "__pycache__", ".venv", "venv", "node_modules", ".idea", ".vscode"}
    
    for path in root.rglob("*"):
        # Skip ignored directories
        if any(part in ignore_dirs for part in path.parts):
            continue
            
        if path.is_file():
            try:
                mtimes[path] = path.stat().st_mtime
            except OSError:
                # Handle cases where file might disappear or be inaccessible during scan
                continue
    return mtimes


def _extract_json_from_text(text: str) -> dict[str, Any] | None:
    """
    Attempts to extract a JSON object from a string.
    Handles Markdown code blocks and raw JSON.
    """
    # Try to find JSON within markdown code blocks first
    json_block_pattern = r"```(?:json)?\s*(\{.*?\})\s*```"
    match = re.search(json_block_pattern, text, re.DOTALL)
    
    if match:
        json_str = match.group(1)
    else:
        # Try to find the first opening brace and last closing brace
        start = text.find("{")
        end = text.rfind("}")
        if start != -1 and end != -1 and end > start:
            json_str = text[start : end + 1]
        else:
            return None

    try:
        return json.loads(json_str)
    except json.JSONDecodeError:
        return None


def run_agentic_verify(
    prompt_file: Path,
    code_file: Path,
    program_file: Path,
    verification_log_file: Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
) -> tuple[bool, str, float, str, list[str]]:
    """
    Runs an agentic verification fallback.
    
    This function delegates the verification fix to a CLI agent (explore mode).
    It records file changes, parses the agent's JSON output, and returns the results.

    Args:
        prompt_file: Path to the prompt specification file.
        code_file: Path to the generated code file.
        program_file: Path to the program/driver file.
        verification_log_file: Path to the log containing previous failures.
        verbose: Enable verbose logging.
        quiet: Suppress standard output.

    Returns:
        Tuple containing:
        - success (bool): Whether the agent claims success.
        - message (str): The explanation or output message.
        - cost (float): Estimated cost of the operation.
        - model (str): The model/provider used.
        - changed_files (list[str]): List of files modified during execution.
    """
    project_root = Path.cwd()
    
    if not quiet:
        console.print(f"[bold blue]Starting Agentic Verify (Explore Mode)[/bold blue]")
        console.print(f"Context: {project_root}")

    # 1. Load Prompt Template
    template_name = "agentic_verify_explore_LLM"
    template = load_prompt_template(template_name)
    
    if not template:
        error_msg = f"Failed to load prompt template: {template_name}"
        console.print(f"[bold red]{error_msg}[/bold red]")
        return False, error_msg, 0.0, "unknown", []

    # 2. Prepare Context
    if verification_log_file.exists():
        previous_attempts = verification_log_file.read_text(encoding="utf-8")
    else:
        previous_attempts = "No previous verification logs found."

    # 3. Format Instruction
    instruction = template.format(
        prompt_path=prompt_file.resolve(),
        code_path=code_file.resolve(),
        program_path=program_file.resolve(),
        project_root=project_root.resolve(),
        previous_attempts=previous_attempts
    )

    # 4. Record State Before Execution
    mtimes_before = _get_file_mtimes(project_root)

    # 5. Run Agentic Task
    # We use the project root as the CWD so the agent can explore freely
    agent_success, agent_output, cost, provider = run_agentic_task(
        instruction=instruction,
        cwd=project_root,
        verbose=verbose,
        quiet=quiet,
        label="verify-explore"
    )

    # 6. Record State After Execution & Detect Changes
    mtimes_after = _get_file_mtimes(project_root)
    changed_files = []
    
    for path, mtime in mtimes_after.items():
        # Check if file is new or modified
        if path not in mtimes_before or mtimes_before[path] != mtime:
            # Store relative path for cleaner output
            try:
                rel_path = path.relative_to(project_root)
                changed_files.append(str(rel_path))
            except ValueError:
                changed_files.append(str(path))

    # 7. Parse Agent Output
    # The agent is instructed to return JSON.
    parsed_data = _extract_json_from_text(agent_output)
    
    final_success = False
    final_message = agent_output
    
    if parsed_data:
        # Trust the agent's self-reported success if JSON is valid
        final_success = parsed_data.get("success", False)
        final_message = parsed_data.get("message", agent_output)
        
        # We prefer our calculated changed_files, but if we found none and the agent
        # claims to have changed some (and they exist), we could log that discrepancy.
        # For now, we stick to the physical reality of mtimes.
    else:
        # Fallback if agent didn't output valid JSON but the CLI tool reported success
        if verbose:
            console.print("[yellow]Warning: Could not parse JSON from agent output. Using raw output.[/yellow]")
        
        # If the CLI tool failed (agent_success is False), we definitely failed.
        # If the CLI tool succeeded, we still default to False because we couldn't verify the JSON contract.
        final_success = False

    if not quiet:
        status_color = "green" if final_success else "red"
        console.print(f"[{status_color}]Agentic Verify Finished. Success: {final_success}[/{status_color}]")
        if changed_files:
            console.print(f"Changed files: {', '.join(changed_files)}")

    return final_success, final_message, cost, provider, changed_files
