# pdd_mcp_server/tools/handlers.py

"""
MCP tool handlers for executing PDD CLI commands via the runner module.

Each function corresponds to a PDD command exposed as an MCP tool.
It receives validated arguments, constructs the appropriate pdd command-line
invocation, executes it using the runner, and formats the result for MCP.
"""

import logging
import mcp.types as types
from typing import Dict, List, Any, Optional
import shlex
import re
import os
import json

# Import the runner function and result type
from .runner import run_pdd_command, PddResult

logger = logging.getLogger(__name__)

# --- Helper Functions ---

def _handle_cli_style_args(arguments: Dict[str, Any], cmd_name: str) -> List[str]:
    """
    Process CLI-style string arguments passed via kwargs.
    
    Args:
        arguments: The arguments dictionary which might contain a 'kwargs' string
        cmd_name: The PDD command name to check for in the args list
        
    Returns:
        A list of command arguments if kwargs was found and processed,
        or an empty list if no kwargs was present
    """
    if 'kwargs' in arguments and isinstance(arguments['kwargs'], str):
        cli_args = arguments['kwargs']
        logger.info("Processing CLI-style arguments: %s", cli_args)
        
        # Split the string into a list, preserving quotes
        args_list = shlex.split(cli_args)
        
        # Build the command list with 'pdd' at the start
        cmd_list = ['pdd']
        
        # Extract prompt_file from various flags
        prompt_file = None
        
        # Check for --file=value format
        for i, arg in enumerate(args_list):
            if arg.startswith("--file="):
                parts = arg.split("=", 1)
                if len(parts) > 1:
                    prompt_file = parts[1]
                    # Store for validation
                    arguments['prompt_file'] = prompt_file
                    # Replace with standard PDD CLI format
                    args_list[i] = "-p"
                    args_list.insert(i+1, prompt_file)
                break
        
        # If we didn't find --file=, check for -p/--prompt flags
        if not prompt_file:
            prompt_index = -1
            for i, arg in enumerate(args_list):
                if arg == '-p' or arg == '--prompt':
                    prompt_index = i
                    break
            
            if prompt_index >= 0 and prompt_index + 1 < len(args_list):
                # Store the prompt file value for later validation
                arguments['prompt_file'] = args_list[prompt_index + 1]
        
        logger.info("Extracted prompt file: %s", arguments.get('prompt_file'))
        
        # Add all args, with modifications we may have made
        cmd_list.extend(args_list)
        
        # If the command name appears at the end, remove it (it will be added later)
        if len(cmd_list) > 1 and cmd_list[-1] == cmd_name:
            cmd_list.pop()
            
        logger.info("Final command list: %s", cmd_list)
        return cmd_list
    
    # No kwargs found, return empty list
    return []

def _add_global_options(cmd_list: List[str], arguments: Dict[str, Any]):
    """Appends global PDD options to the command list if present in arguments."""
    if arguments.get('local'):
        cmd_list.append('--local')
    if arguments.get('force'):
        cmd_list.append('--force')
    if arguments.get('strength') is not None:
        cmd_list.extend(['--strength', str(arguments['strength'])])
    if arguments.get('temperature') is not None:
        cmd_list.extend(['--temperature', str(arguments['temperature'])])
    if arguments.get('verbose'):
        cmd_list.append('--verbose')
    if arguments.get('quiet'):
        cmd_list.append('--quiet')
    if arguments.get('output_cost'):
        cmd_list.extend(['--output-cost', arguments['output_cost']])
    if arguments.get('review_examples'):
        cmd_list.append('--review-examples')
    
    # Additional debugging info
    logger.debug("Global options added to command: %s", 
                 " ".join([opt for opt in cmd_list if opt.startswith('--')]))

# --- Helper Function for Result Formatting ---

def _format_result(pdd_result: PddResult, command_name: str) -> types.CallToolResult:
    """Formats the PddResult into an MCP CallToolResult."""
    if pdd_result.success:
        content = [types.TextContent(text=pdd_result.stdout, type="text")]
        is_error = False
        logger.info("pdd %s succeeded.", command_name)
    else:
        # Enhanced error formatting with more detail
        error_text = f"PDD command '{command_name}' failed with exit code {pdd_result.exit_code}."
        
        # Add troubleshooting information
        if pdd_result.exit_code == 127:  # Command not found
            error_text += "\n\nTROUBLESHOOTING: The 'pdd' command was not found. Make sure it's installed and in your PATH."
        elif pdd_result.exit_code == 126:  # Permission denied
            error_text += "\n\nTROUBLESHOOTING: Permission denied when executing 'pdd'. Check file permissions."
        elif pdd_result.exit_code == -1:  # Timeout
            error_text += "\n\nTROUBLESHOOTING: The command timed out. Consider simplifying your request or checking for network issues."
        elif pdd_result.exit_code == 1:  # Generic error
            error_text += "\n\nTROUBLESHOOTING: Check if the prompt file exists and has the correct format."
        
        # Add stdout and stderr for debugging
        if pdd_result.stdout:
            error_text += f"\n\nSTDOUT:\n-------\n{pdd_result.stdout}"
        if pdd_result.stderr:
            error_text += f"\n\nSTDERR:\n-------\n{pdd_result.stderr}"
        else:
            error_text += "\nNo STDERR output."
            
        # Add example of correct tool usage
        error_text += f"""

TOOL USAGE EXAMPLE:
To use the pdd-{command_name} tool correctly, provide parameters directly:

{{
  "prompt_file": "/absolute/path/to/your/prompt_file.prompt"
}}

Make sure the prompt file exists at the specified path.
"""

        content = [types.TextContent(text=error_text, type="text")]
        is_error = True
        logger.error("pdd %s failed. Exit code: %d. Stderr: %s", command_name, pdd_result.exit_code, pdd_result.stderr)
    
    logger.info("Final result for pdd %s: isError=%s, content_length=%d", 
                command_name, is_error, len(content[0].text) if content else 0)
    
    return types.CallToolResult(content=content, isError=is_error)

def _check_parameter_issues(arguments: Dict[str, Any], command_name: str) -> Optional[types.CallToolResult]:
    """
    Checks for parameter issues and returns an error result if problems are found.
    
    Args:
        arguments: Dictionary of parameters to check
        command_name: Name of the command for error messages
        
    Returns:
        CallToolResult with error message if issues found, None if parameters are good
    """
    # Check for empty parameters
    if not arguments:
        return types.CallToolResult(
            isError=True,
            content=[types.TextContent(
                text=f"Error: No parameters provided for pdd-{command_name}. Please specify required parameters.",
                type="text"
            )]
        )
    
    # Check for kwargs parameter - only if it wasn't already processed upstream
    if 'kwargs' in arguments:
        helpful_message = f"""
Error: Please provide parameters directly, not as 'kwargs'.

INCORRECT WAY:
{{
  "kwargs": {{
    "prompt_file": "/path/to/prompt.txt"
  }}
}}

CORRECT WAY:
{{
  "prompt_file": "/path/to/prompt.txt"
}}

For pdd-{command_name}, the required parameters are documented in the tool schema.
"""
        return types.CallToolResult(
            isError=True,
            content=[types.TextContent(text=helpful_message, type="text")]
        )
        
    return None  # No issues found

# --- Tool Handlers ---

async def handle_pdd_generate(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Super simplified handler for pdd-generate using direct subprocess calls.
    """
    try:
        import subprocess
        import os
        
        # Log what we received
        logger.info(f"handle_pdd_generate called with arguments: {arguments}")
        
        # Handle kwargs in JSON string format (from Claude Code)
        if 'kwargs' in arguments and isinstance(arguments['kwargs'], str):
            try:
                # Parse the JSON string into a dict
                kwargs_dict = json.loads(arguments['kwargs'])
                if isinstance(kwargs_dict, dict):
                    # Update arguments with parsed values
                    arguments.update(kwargs_dict)
                    # Remove the original kwargs to avoid confusion
                    del arguments['kwargs']
                    logger.info(f"Parsed kwargs JSON string into: {kwargs_dict}")
                else:
                    return types.CallToolResult(
                        isError=True,
                        content=[types.TextContent(
                            text="Error: kwargs is not a valid JSON object",
                            type="text"
                        )]
                    )
            except json.JSONDecodeError as e:
                logger.error(f"Failed to parse kwargs JSON: {arguments['kwargs']}")
                return types.CallToolResult(
                    isError=True,
                    content=[types.TextContent(
                        text=f"Error parsing kwargs JSON: {str(e)}",
                        type="text"
                    )]
                )
        
        # Basic validation
        if not arguments or 'prompt_file' not in arguments:
            logger.error("Missing prompt_file parameter")
            return types.CallToolResult(
                isError=True,
                content=[types.TextContent(
                    text="""Error: Missing required 'prompt_file' parameter
                    
For Claude Code integration, use this format:
{"kwargs": "{\\"prompt_file\\": \\"/Users/gregtanaka/pdd/examples/hello.prompt\\"}"}

For direct API usage:
{"prompt_file": "/Users/gregtanaka/pdd/examples/hello.prompt"}
""",
                    type="text"
                )]
            )
        
        prompt_file = arguments['prompt_file']
        if not os.path.exists(prompt_file):
            logger.error(f"Prompt file not found: {prompt_file}")
            return types.CallToolResult(
                isError=True,
                content=[types.TextContent(
                    text=f"Error: Prompt file not found: {prompt_file}",
                    type="text"
                )]
            )
        
        # Build command as a list of arguments
        cmd = ['pdd', 'generate', prompt_file]
        
        # Add output if specified
        if 'output' in arguments:
            output = arguments['output']
            cmd.extend(['--output', output])
        
        # Log the command we're about to run
        logger.info(f"Running command: {' '.join(cmd)}")
        
        # Use subprocess directly for maximum simplicity
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                check=False
            )
            
            # Log the result
            logger.info(f"Command completed with exit code: {result.returncode}")
            logger.info(f"Stdout: {result.stdout}")
            if result.stderr:
                logger.warning(f"Stderr: {result.stderr}")
            
            # Return success or failure
            if result.returncode == 0:
                return types.CallToolResult(
                    isError=False,
                    content=[types.TextContent(
                        text=result.stdout,
                        type="text"
                    )]
                )
            else:
                return types.CallToolResult(
                    isError=True,
                    content=[types.TextContent(
                        text=f"Command failed with exit code {result.returncode}\n\n{result.stderr}",
                        type="text"
                    )]
                )
        except Exception as e:
            logger.exception(f"Error executing command: {e}")
            return types.CallToolResult(
                isError=True,
                content=[types.TextContent(
                    text=f"Error executing command: {str(e)}",
                    type="text"
                )]
            )
    except Exception as e:
        logger.exception(f"Unexpected error in handler: {e}")
        return types.CallToolResult(
            isError=True,
            content=[types.TextContent(
                text=f"Internal server error: {str(e)}",
                type="text"
            )]
        )

async def handle_pdd_example(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-example' MCP tool call by executing the 'pdd example' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'code_file', 'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "example"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        code_file = arguments.get('code_file')
        if not prompt_file or not code_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file' or 'code_file' after validation.")])
        cmd_list.append(prompt_file) # Positional
        cmd_list.append(code_file)   # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_test(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-test' MCP tool call by executing the 'pdd test' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'code_file', 'output' (optional),
                   'language' (optional), 'coverage_report' (optional),
                   'existing_tests' (optional), 'target_coverage' (optional),
                   'merge' (optional, bool), global options.
                   Alternative format: 'kwargs' containing a string of CLI arguments

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "test"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        code_file = arguments.get('code_file')
        if not prompt_file or not code_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file' or 'code_file' after validation.")])
        cmd_list.append(prompt_file) # Positional
        cmd_list.append(code_file)   # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])
        if arguments.get('language'):
            cmd_list.extend(['--language', arguments['language']])
        if arguments.get('coverage_report'):
            cmd_list.extend(['--coverage-report', arguments['coverage_report']])
        if arguments.get('existing_tests'):
            cmd_list.extend(['--existing-tests', arguments['existing_tests']])
        if arguments.get('target_coverage') is not None:
            cmd_list.extend(['--target-coverage', str(arguments['target_coverage'])])

        # Boolean flags
        if arguments.get('merge'):
            cmd_list.append('--merge')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_preprocess(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-preprocess' MCP tool call by executing the 'pdd preprocess' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'output' (optional), 'xml' (optional, bool),
                   'recursive' (optional, bool), 'double' (optional, bool),
                   'exclude' (optional, list[str]), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "preprocess"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        if not prompt_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required argument 'prompt_file' after validation.")])
        cmd_list.append(prompt_file) # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])
        exclude_list = arguments.get('exclude')
        if exclude_list:
            # Click expects multiple --exclude options
            for item in exclude_list:
                 cmd_list.extend(['--exclude', item])

        # Boolean flags
        if arguments.get('xml'):
            cmd_list.append('--xml')
        if arguments.get('recursive'):
            cmd_list.append('--recursive')
        if arguments.get('double'):
            cmd_list.append('--double')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_fix(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-fix' MCP tool call by executing the 'pdd fix' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'code_file', 'unit_test_file',
                   'error_file' (optional), 'output_test' (optional),
                   'output_code' (optional), 'output_results' (optional),
                   'loop' (optional, bool), 'verification_program' (optional),
                   'max_attempts' (optional, int), 'budget' (optional, float),
                   'auto_submit' (optional, bool), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "fix"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        code_file = arguments.get('code_file')
        unit_test_file = arguments.get('unit_test_file')
        # error_file is optional in the command itself if --loop is used, but required by schema if not looping? Check definition. Assuming required for now.
        error_file = arguments.get('error_file') # Optional positional arg

        if not prompt_file or not code_file or not unit_test_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file', 'code_file', or 'unit_test_file' after validation.")])

        cmd_list.append(prompt_file)    # Positional
        cmd_list.append(code_file)      # Positional
        cmd_list.append(unit_test_file) # Positional
        if error_file: # Only add if provided
            cmd_list.append(error_file) # Positional (optional)

        # Optional arguments
        if arguments.get('output_test'):
            cmd_list.extend(['--output-test', arguments['output_test']])
        if arguments.get('output_code'):
            cmd_list.extend(['--output-code', arguments['output_code']])
        if arguments.get('output_results'):
            cmd_list.extend(['--output-results', arguments['output_results']])
        if arguments.get('verification_program'):
            cmd_list.extend(['--verification-program', arguments['verification_program']])
        if arguments.get('max_attempts') is not None:
            cmd_list.extend(['--max-attempts', str(arguments['max_attempts'])])
        if arguments.get('budget') is not None:
            cmd_list.extend(['--budget', str(arguments['budget'])])

        # Boolean flags
        if arguments.get('loop'):
            cmd_list.append('--loop')
        if arguments.get('auto_submit'):
            cmd_list.append('--auto-submit')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_split(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-split' MCP tool call by executing the 'pdd split' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'input_prompt', 'input_code', 'example_code',
                   'output_sub' (optional), 'output_modified' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "split"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        input_prompt = arguments.get('input_prompt')
        input_code = arguments.get('input_code')
        example_code = arguments.get('example_code')
        if not input_prompt or not input_code or not example_code:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'input_prompt', 'input_code', or 'example_code' after validation.")])
        cmd_list.append(input_prompt) # Positional
        cmd_list.append(input_code)   # Positional
        cmd_list.append(example_code) # Positional

        # Optional arguments
        if arguments.get('output_sub'):
            cmd_list.extend(['--output-sub', arguments['output_sub']])
        if arguments.get('output_modified'):
            cmd_list.extend(['--output-modified', arguments['output_modified']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_change(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-change' MCP tool call by executing the 'pdd change' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'change_prompt_file', 'input_code',
                   'input_prompt_file' (optional), 'output' (optional),
                   'csv' (optional, bool), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "change"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        change_prompt_file = arguments.get('change_prompt_file')
        input_code = arguments.get('input_code')
        if not change_prompt_file or not input_code:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'change_prompt_file' or 'input_code' after validation.")])
        cmd_list.append(change_prompt_file) # Positional
        cmd_list.append(input_code)         # Positional

        # Optional positional argument (only if --csv is NOT used)
        input_prompt_file = arguments.get('input_prompt_file')
        use_csv = arguments.get('csv', False)
        if not use_csv and input_prompt_file:
            cmd_list.append(input_prompt_file) # Positional (optional)
        elif not use_csv and not input_prompt_file:
            # This case might need clarification based on CLI behavior.
            # If input_prompt_file is truly optional *only* when --csv is used,
            # this check might be redundant due to schema validation.
            # If it's optional even without --csv, this is correct.
            pass
        elif use_csv and input_prompt_file:
            logger.warning("Ignoring 'input_prompt_file' because '--csv' flag is set.")


        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

        # Boolean flags
        if use_csv:
            cmd_list.append('--csv')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_update(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-update' MCP tool call by executing the 'pdd update' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'input_prompt_file', 'modified_code_file',
                   'input_code_file' (optional), 'output' (optional),
                   'git' (optional, bool), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "update"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        input_prompt_file = arguments.get('input_prompt_file')
        modified_code_file = arguments.get('modified_code_file')
        if not input_prompt_file or not modified_code_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'input_prompt_file' or 'modified_code_file' after validation.")])
        cmd_list.append(input_prompt_file)  # Positional
        cmd_list.append(modified_code_file) # Positional

        # Optional positional argument (only if --git is NOT used)
        input_code_file = arguments.get('input_code_file')
        use_git = arguments.get('git', False)
        if not use_git and input_code_file:
            cmd_list.append(input_code_file) # Positional (optional)
        elif not use_git and not input_code_file:
             # According to README, input_code_file is optional *only* when --git is used.
             # Schema validation should enforce this. If it gets here, it's an issue.
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing 'input_code_file' when '--git' is not used.")])
        elif use_git and input_code_file:
            logger.warning("Ignoring 'input_code_file' because '--git' flag is set.")


        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

        # Boolean flags
        if use_git:
            cmd_list.append('--git')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_detect(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-detect' MCP tool call by executing the 'pdd detect' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_files' (list[str]), 'change_file',
                   'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "detect"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments (positional, variable length first)
        prompt_files = arguments.get('prompt_files')
        change_file = arguments.get('change_file')
        if not prompt_files or not isinstance(prompt_files, list) or not change_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing or invalid required arguments 'prompt_files' (list) or 'change_file' after validation.")])

        cmd_list.extend(prompt_files) # Positional (variable length)
        cmd_list.append(change_file)  # Positional (last)

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_conflicts(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-conflicts' MCP tool call by executing the 'pdd conflicts' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt1', 'prompt2', 'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "conflicts"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt1 = arguments.get('prompt1')
        prompt2 = arguments.get('prompt2')
        if not prompt1 or not prompt2:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt1' or 'prompt2' after validation.")])
        cmd_list.append(prompt1) # Positional
        cmd_list.append(prompt2) # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_crash(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-crash' MCP tool call by executing the 'pdd crash' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'code_file', 'program_file', 'error_file',
                   'output' (optional), 'output_program' (optional),
                   'loop' (optional, bool), 'max_attempts' (optional, int),
                   'budget' (optional, float), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "crash"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        code_file = arguments.get('code_file')
        program_file = arguments.get('program_file')
        error_file = arguments.get('error_file')
        if not prompt_file or not code_file or not program_file or not error_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file', 'code_file', 'program_file', or 'error_file' after validation.")])
        cmd_list.append(prompt_file)    # Positional
        cmd_list.append(code_file)      # Positional
        cmd_list.append(program_file)   # Positional
        cmd_list.append(error_file)     # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])
        if arguments.get('output_program'):
            cmd_list.extend(['--output-program', arguments['output_program']])
        if arguments.get('max_attempts') is not None:
            cmd_list.extend(['--max-attempts', str(arguments['max_attempts'])])
        if arguments.get('budget') is not None:
            cmd_list.extend(['--budget', str(arguments['budget'])])

        # Boolean flags
        if arguments.get('loop'):
            cmd_list.append('--loop')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_trace(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-trace' MCP tool call by executing the 'pdd trace' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'code_file', 'code_line',
                   'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "trace"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        code_file = arguments.get('code_file')
        code_line = arguments.get('code_line') # Should be validated as int by schema
        if not prompt_file or not code_file or code_line is None:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file', 'code_file', or 'code_line' after validation.")])
        cmd_list.append(prompt_file)    # Positional
        cmd_list.append(code_file)      # Positional
        cmd_list.append(str(code_line)) # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_bug(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-bug' MCP tool call by executing the 'pdd bug' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'code_file', 'bug_description',
                   'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "bug"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        code_file = arguments.get('code_file')
        bug_description = arguments.get('bug_description')
        if not prompt_file or not code_file or not bug_description:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file', 'code_file', or 'bug_description' after validation.")])
        cmd_list.append(prompt_file)      # Positional
        cmd_list.append(code_file)        # Positional
        cmd_list.append(bug_description)  # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_continue(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-continue' MCP tool call by executing the 'pdd continue' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'output_file', 'result_file' (optional),
                   'strength' (optional), 'temperature' (optional), 'local' (optional),
                   'force' (optional), 'verbose' (optional).

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "continue"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        output_file = arguments.get('output_file')
        if not prompt_file or not output_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file' or 'output_file' after validation.")])
        cmd_list.append(prompt_file)  # Positional
        cmd_list.append(output_file)  # Positional

        # Optional arguments
        if arguments.get('result_file'):
            cmd_list.append(arguments['result_file'])  # Positional (optional third argument)

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_analyze(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-analyze' MCP tool call by executing the 'pdd analyze' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'source_file', 'output' (optional), 'format' (optional),
                   'strength' (optional), 'temperature' (optional), 'local' (optional),
                   'verbose' (optional).

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "analyze"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        source_file = arguments.get('source_file')
        if not source_file:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required argument 'source_file' after validation.")])
        cmd_list.append(source_file)  # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])
        if arguments.get('format'):
            cmd_list.extend(['--format', arguments['format']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_auto_deps(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-auto-deps' MCP tool call by executing the 'pdd auto-deps' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'input_file', 'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "auto-deps"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = _handle_cli_style_args(arguments, command_name)
    
    if not cmd_list:
        _add_global_options(cmd_list, arguments)
        cmd_list.append(command_name)

        # Required arguments
        prompt_file = arguments.get('prompt_file')
        directory_path = arguments.get('directory_path')
        if not prompt_file or not directory_path:
             return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file' or 'directory_path' after validation.")])
        cmd_list.append(prompt_file)    # Positional
        cmd_list.append(directory_path) # Positional

        # Optional arguments
        if arguments.get('output'):
            cmd_list.extend(['--output', arguments['output']])
        if arguments.get('csv'):
            cmd_list.extend(['--csv', arguments['csv']])

        # Boolean flags
        if arguments.get('force_scan'):
            cmd_list.append('--force-scan')

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

# --- Mapping from tool name to handler function ---
# This could be defined here or in another module (like __init__.py or definitions.py)
# depending on project structure preference.
TOOL_HANDLERS = {
    "pdd-generate": handle_pdd_generate,
    "pdd-example": handle_pdd_example,
    "pdd-test": handle_pdd_test,
    "pdd-preprocess": handle_pdd_preprocess,
    "pdd-fix": handle_pdd_fix,
    "pdd-split": handle_pdd_split,
    "pdd-change": handle_pdd_change,
    "pdd-update": handle_pdd_update,
    "pdd-detect": handle_pdd_detect,
    "pdd-conflicts": handle_pdd_conflicts,
    "pdd-crash": handle_pdd_crash,
    "pdd-trace": handle_pdd_trace,
    "pdd-bug": handle_pdd_bug,
    "pdd-auto-deps": handle_pdd_auto_deps,
    "pdd-continue": handle_pdd_continue,
    "pdd-analyze": handle_pdd_analyze,
}

def get_handler(tool_name: str):
    """Retrieves the handler function for a given tool name."""
    handler = TOOL_HANDLERS.get(tool_name)
    if not handler:
        logger.error("No handler found for tool: %s", tool_name)
        # Consider raising an error or returning a default handler that returns an error result
        raise ValueError(f"No handler registered for tool '{tool_name}'")
    return handler