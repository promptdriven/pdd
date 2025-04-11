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

# Import the runner function and result type
from .runner import run_pdd_command, PddResult

logger = logging.getLogger(__name__)

# --- Helper Function for Global Options ---

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

# --- Helper Function for Result Formatting ---

def _format_result(pdd_result: PddResult, command_name: str) -> types.CallToolResult:
    """Formats the PddResult into an MCP CallToolResult."""
    if pdd_result.success:
        content = [types.TextContent(text=pdd_result.stdout, type="text")]
        is_error = False
        logger.info("pdd %s succeeded.", command_name)
    else:
        error_text = f"PDD command '{command_name}' failed with exit code {pdd_result.exit_code}."
        if pdd_result.stdout:
            error_text += f"\n\nSTDOUT:\n-------\n{pdd_result.stdout}"
        if pdd_result.stderr:
            error_text += f"\n\nSTDERR:\n-------\n{pdd_result.stderr}"
        else:
             error_text += "\nNo STDERR output."

        content = [types.TextContent(text=error_text, type="text")]
        is_error = True
        logger.error("pdd %s failed. Exit code: %d. Stderr: %s", command_name, pdd_result.exit_code, pdd_result.stderr)

    return types.CallToolResult(content=content, isError=is_error)


# --- Tool Handlers ---

async def handle_pdd_generate(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-generate' MCP tool call by executing the 'pdd generate' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'output' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "generate"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = ['pdd']
    _add_global_options(cmd_list, arguments)
    cmd_list.append(command_name)

    # Required arguments
    prompt_file = arguments.get('prompt_file')
    if not prompt_file:
         return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required argument 'prompt_file' after validation.")])
    cmd_list.append(prompt_file) # Positional argument

    # Optional arguments
    if arguments.get('output'):
        cmd_list.extend(['--output', arguments['output']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

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
    cmd_list = ['pdd']
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

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "test"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
    cmd_list = ['pdd']
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
                   Expected keys: 'prompt_file', 'code_file', 'program_file',
                   'current_output_file', 'desired_output_file',
                   'output' (optional), 'language' (optional), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "bug"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = ['pdd']
    _add_global_options(cmd_list, arguments)
    cmd_list.append(command_name)

    # Required arguments
    prompt_file = arguments.get('prompt_file')
    code_file = arguments.get('code_file')
    program_file = arguments.get('program_file')
    current_output_file = arguments.get('current_output_file')
    desired_output_file = arguments.get('desired_output_file')
    if not prompt_file or not code_file or not program_file or not current_output_file or not desired_output_file:
         return types.CallToolResult(isError=True, content=[types.TextContent(text="Internal Error: Missing required arguments 'prompt_file', 'code_file', 'program_file', 'current_output_file', or 'desired_output_file' after validation.")])
    cmd_list.append(prompt_file)         # Positional
    cmd_list.append(code_file)           # Positional
    cmd_list.append(program_file)        # Positional
    cmd_list.append(current_output_file) # Positional
    cmd_list.append(desired_output_file) # Positional

    # Optional arguments
    if arguments.get('output'):
        cmd_list.extend(['--output', arguments['output']])
    if arguments.get('language'):
        cmd_list.extend(['--language', arguments['language']])

    logger.debug("Executing command: %s", " ".join(cmd_list))
    pdd_result: PddResult = await run_pdd_command(cmd_list)
    return _format_result(pdd_result, command_name)

async def handle_pdd_auto_deps(arguments: Dict[str, Any]) -> types.CallToolResult:
    """
    Handles the 'pdd-auto-deps' MCP tool call by executing the 'pdd auto-deps' command.

    Args:
        arguments: Dictionary containing validated parameters from the MCP client.
                   Expected keys: 'prompt_file', 'directory_path',
                   'output' (optional), 'csv' (optional),
                   'force_scan' (optional, bool), global options.

    Returns:
        An MCP CallToolResult containing the stdout or stderr of the command.
    """
    command_name = "auto-deps"
    logger.info("Handling %s tool call with arguments: %s", f"pdd-{command_name}", arguments)
    cmd_list = ['pdd']
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
}

def get_handler(tool_name: str):
    """Retrieves the handler function for a given tool name."""
    handler = TOOL_HANDLERS.get(tool_name)
    if not handler:
        logger.error("No handler found for tool: %s", tool_name)
        # Consider raising an error or returning a default handler that returns an error result
        raise ValueError(f"No handler registered for tool '{tool_name}'")
    return handler