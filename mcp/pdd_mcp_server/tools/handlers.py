# --- Start of handlers.py ---
"""
MCP tool handlers for executing PDD CLI commands via the runner module.

This module translates incoming MCP tool requests into PDD command-line
invocations, executes them, and formats the results back into MCP format.
"""

import logging
import mcp.types as types
from typing import Dict, List, Any

# Import from the sibling runner module
from .runner import run_pdd_command, PddResult

logger = logging.getLogger(__name__)

# --- Tool Handlers ---

async def handle_pdd_generate(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-generate' MCP tool call by executing the 'pdd generate' command.

    Args:
        arguments: A dictionary containing the validated arguments passed from the MCP client,
                   matching the 'pdd-generate' tool schema. Expected keys include
                   'prompt_file' (required), and optionals like 'output', 'strength',
                   'temperature', 'local', 'force', 'verbose', 'quiet', 'output_cost',
                   'review_examples'.

    Returns:
        An MCP CallToolResult object containing the stdout or stderr of the command execution.
    """
    logger.info("Handling pdd-generate tool call with arguments: %s", arguments)
    cmd_list: List[str] = ['pdd', 'generate']

    # --- Argument Parsing (Specific to 'pdd generate') ---

    # Required positional arguments
    prompt_file = arguments.get('prompt_file')
    if not prompt_file:
         # Schema validation should prevent this, but handle defensively
         logger.error("Missing required argument 'prompt_file' for pdd-generate.")
         return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Server Error: Missing required argument prompt_file")])
    cmd_list.append(prompt_file) # Add positional argument

    # Optional arguments with values
    if arguments.get('output'):
        cmd_list.extend(['--output', arguments['output']])
    if arguments.get('strength') is not None:
        cmd_list.extend(['--strength', str(arguments['strength'])])
    if arguments.get('temperature') is not None:
        cmd_list.extend(['--temperature', str(arguments['temperature'])])
    if arguments.get('output_cost'):
        cmd_list.extend(['--output-cost', arguments['output_cost']]) # Assume output_cost is str if present

    # Boolean flags / Global Options handled as flags
    if arguments.get('local'):
        cmd_list.append('--local')
    if arguments.get('force'):
        cmd_list.append('--force')
    if arguments.get('verbose'):
         cmd_list.append('--verbose')
    if arguments.get('quiet'):
         # Note: Runner might handle verbosity, but pass flag if defined
         cmd_list.append('--quiet')
    if arguments.get('review_examples'):
         cmd_list.append('--review-examples')

    # --- Command Execution ---
    logger.debug("Constructed command list: %s", cmd_list)
    try:
        pdd_result: PddResult = await run_pdd_command(cmd_list)
    except Exception as e:
        logger.exception("An unexpected error occurred while running pdd command: %s", cmd_list)
        return types.CallToolResult(isError=True, content=[types.TextContent(text=f"Internal Server Error: {e}")])

    # --- Result Formatting ---
    if pdd_result.success:
        logger.info("pdd generate command succeeded.")
        content = [types.TextContent(text=pdd_result.stdout)]
        is_error = False
    else:
        logger.warning("pdd generate command failed with exit code %d.", pdd_result.exit_code)
        error_text = f"PDD command 'generate' failed with exit code {pdd_result.exit_code}.\n"
        if pdd_result.stdout: # Include stdout context if available on error
             error_text += f"\n--- STDOUT ---\n{pdd_result.stdout}\n"
        error_text += f"\n--- STDERR ---\n{pdd_result.stderr}"
        content = [types.TextContent(text=error_text)]
        is_error = True

    return types.CallToolResult(content=content, isError=is_error)

# --- End of handlers.py ---