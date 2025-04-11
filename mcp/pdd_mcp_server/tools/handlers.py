"""
MCP tool handlers for executing PDD CLI commands.
"""

import logging
import mcp.types as types
from typing import Dict, List, Any

# Assume runner module provides these (adjust import path if necessary)
from .runner import run_pdd_command, PddResult

logger = logging.getLogger(__name__)

# --- Tool Handlers ---

async def handle_pdd_generate(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-generate' MCP tool call by executing the 'pdd generate' command.
    """
    logger.info("Handling pdd-generate tool call with arguments: %s", arguments)
    cmd_list = ['pdd', 'generate']

    # Required arguments
    prompt_file = arguments.get('prompt_file')
    if not prompt_file:
         # This ideally shouldn't happen if schema validation works
         return types.CallToolResult(isError=True, content=[types.TextContent(text="Missing required argument: prompt_file")])
    cmd_list.append(prompt_file) # Positional argument

    # Optional arguments
    if arguments.get('output'):
        cmd_list.extend(['--output', arguments['output']])
    if arguments.get('strength') is not None:
        cmd_list.extend(['--strength', str(arguments['strength'])])
    if arguments.get('temperature') is not None:
        cmd_list.extend(['--temperature', str(arguments['temperature'])])

    # Boolean flags / Global Options
    if arguments.get('local'):
        cmd_list.append('--local')
    if arguments.get('force'):
        cmd_list.append('--force')
    if arguments.get('verbose'):
         cmd_list.append('--verbose')
    if arguments.get('quiet'):
         cmd_list.append('--quiet')
    if arguments.get('output_cost'):
         cmd_list.extend(['--output-cost', arguments['output_cost']])
    if arguments.get('review_examples'):
         cmd_list.append('--review-examples')


    # Execute the command
    pdd_result: PddResult = await run_pdd_command(cmd_list)

    # Format the result
    if pdd_result.success:
        content = [types.TextContent(text=pdd_result.stdout)]
        is_error = False
        logger.info("pdd generate succeeded.")
    else:
        error_text = f"PDD command failed with exit code {{pdd_result.exit_code}}.\nSTDERR:\n{{pdd_result.stderr}}"
        # Optionally include stdout for context on failure
        # if pdd_result.stdout:
        #    error_text = f"STDOUT:\n{{pdd_result.stdout}}\n\n{{error_text}}"
        content = [types.TextContent(text=error_text)]
        is_error = True
        logger.error("pdd generate failed.")

    return types.CallToolResult(content=content, isError=is_error)

# --- Add handlers for ALL other PDD commands below ---
# handle_pdd_example
# handle_pdd_test
# handle_pdd_preprocess
# handle_pdd_fix
# handle_pdd_split
# handle_pdd_change
# handle_pdd_update
# handle_pdd_detect
# handle_pdd_conflicts
# handle_pdd_crash
# handle_pdd_trace
# handle_pdd_bug
# handle_pdd_auto_deps
# ... (implement each following the pattern above, adapting arg parsing based on pdd_readme)

# Consider creating a helper function for common argument processing if patterns emerge
# def _build_common_cmd_list(base_cmd: list[str], arguments: dict[str, Any]) -> list[str]:
#     # Handles global options like --local, --force, --verbose etc.
#     pass


# Example for a command with different arg types (like fix)
# async def handle_pdd_fix(arguments: Dict[str, Any]) -> types.CallToolResult:
#     logger.info("Handling pdd-fix tool call with arguments: %s", arguments)
#     cmd_list = ['pdd', 'fix']
#     # Positional Args
#     cmd_list.append(arguments['prompt_file'])
#     cmd_list.append(arguments['code_file'])
#     cmd_list.append(arguments['unit_test_file'])
#     if arguments.get('error_file'): # Optional positional
#         cmd_list.append(arguments['error_file'])
#     # Optional Flags with values
#     if arguments.get('output_test'): cmd_list.extend(['--output-test', arguments['output_test']])
#     if arguments.get('output_code'): cmd_list.extend(['--output-code', arguments['output_code']])
#     if arguments.get('output_results'): cmd_list.extend(['--output-results', arguments['output_results']])
#     if arguments.get('verification_program'): cmd_list.extend(['--verification-program', arguments['verification_program']])
#     if arguments.get('max_attempts') is not None: cmd_list.extend(['--max-attempts', str(arguments['max_attempts'])])
#     if arguments.get('budget') is not None: cmd_list.extend(['--budget', str(arguments['budget'])])
#     # Boolean flags
#     if arguments.get('loop'): cmd_list.append('--loop')
#     if arguments.get('auto_submit'): cmd_list.append('--auto-submit')
#     # Add global options if needed
#     # ...
#     pdd_result = await run_pdd_command(cmd_list)
#     # ... format CallToolResult ...
#     return types.CallToolResult(...)

```

**Dependencies for Generation:**

The generation process for `handlers.py` will need the context of `runner.py`. Include it as follows:

```xml
<runner_example>
import asyncio
import logging
from pdd_mcp_server.tools.runner import run_pdd_command, PddResult

# Configure logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("pdd_example")

async def main():
    """Asynchronous main function demonstrating PDD CLI command usage."""
    # Example 1: Basic usage - run a simple command
    result = await run_pdd_command(['pdd', 'version'])
    # Handle the result
    if result.success:
        logger.info(f"PDD version command succeeded with output:\n{{result.stdout}}")
    else:
        logger.error(f"PDD version command failed: {{result.stderr}}")
    
    # Example 2: Run a command with arguments
    result = await run_pdd_command(['pdd', 'generate', '--project-path', './my_project', 
                                   '--output-dir', './output'])
    # Check the result
    if result.success:
        logger.info("Generation completed successfully")
        logger.info(f"Output: {{result.stdout}}")
    else:
        logger.error(f"Generation failed with exit code {{result.exit_code}}")
        logger.error(f"Error message: {{result.stderr}}")
    
    # Example 3: Run a command with a custom timeout (30 seconds)
    try:
        result = await run_pdd_command(['pdd', 'complex-operation', '--large-dataset'], 
                                      timeout=30)
        if result.success:
            logger.info("Complex operation completed successfully")
        else:
            logger.warning(f"Complex operation failed or timed out: {{result.stderr}}")
            logger.warning(f"Exit code: {{result.exit_code}}")
    except FileNotFoundError:
        logger.critical("PDD executable not found in PATH. Please install PDD CLI.")
    
    # Example 4: How to access all results
    result = await run_pdd_command(['pdd', 'analyze', '--project', './source'])
    print(f"Command successful: {{result.success}}")
    print(f"Exit code: {{result.exit_code}}")
    print(f"Standard output:\n{{result.stdout}}")
    print(f"Standard error:\n{{result.stderr}}")

if __name__ == "__main__":
    asyncio.run(main())