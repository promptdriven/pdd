# edit_file_tool/core.py

"""
This module serves as the core orchestrator for the edit-file tool.

It manages the end-to-end workflow from user input to file modification,
integrating instruction parsing, caching, Claude API calls, and tool
execution into a cohesive async pipeline.
"""

import asyncio
import logging
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

from anthropic.types import ToolUseBlock

from edit_file_tool.claude_api import (MODEL_TO_TEXT_EDITOR_TOOL,
                                       call_claude_api)
from edit_file_tool.editor_tool import EditTool20250124
from edit_file_tool.file_io import read_file_async
from edit_file_tool.think_tool import ThinkTool
from edit_file_tool.cache_manager import CacheManager
from edit_file_tool.utils import EditToolError, get_logger, format_cost

log = get_logger(__name__)

SYSTEM_PROMPT = """
You are an expert software developer and pair programmer. Your task is to help the user edit a file using the provided tools.

1.  **Analyze the Request**: Carefully read the user's instructions and the provided file content.
2.  **Plan Your Edits**: If the request is complex, use the `think` tool to break down the problem, outline your plan, and reflect on the best course of action. This is your private scratchpad.
3.  **Execute Edits**: Use the `text_editor` tool to perform the necessary file modifications. You can use commands like `view`, `str_replace`, `insert`, `create`, and `undo_edit`.
4.  **Verify and Conclude**: After making edits, you can use the `view` command to confirm the changes are correct. When you are finished and believe the user's request is fully addressed, respond with a final confirmation message in plain text, such as "The file has been updated as requested." Do not use a tool for your final response.
"""

async def _process_single_tool_call(
    tool_call: ToolUseBlock,
    editor: EditTool20250124,
    think_tool: ThinkTool,
    model_name: str,
) -> Dict[str, Any]:
    """
    Executes a single tool call and formats the result.

    Args:
        tool_call: The tool use block from the Anthropic API response.
        editor: An instance of the editor tool.
        think_tool: An instance of the think tool.
        model_name: The name of the model being used, for context.

    Returns:
        A dictionary formatted as a tool_result for the Anthropic API.
    """
    tool_name = tool_call.name
    tool_input = tool_call.input
    tool_use_id = tool_call.id
    log.info(f"Executing tool '{tool_name}' with input: {tool_input}")

    output = ""
    is_error = False
    
    try:
        think_tool_name = think_tool.get_definition()["name"]
        editor_tool_names = {v['name'] for v in MODEL_TO_TEXT_EDITOR_TOOL.values()}

        if tool_name == think_tool_name:
            result = think_tool.use(**tool_input)
            output = result.get("output", "OK.")
        elif tool_name in editor_tool_names:
            # The editor tool's __call__ is async
            result = await editor(**tool_input)
            if result.success:
                output = result.output
            else:
                is_error = True
                output = result.error or "An unknown error occurred in the editor tool."
        else:
            is_error = True
            valid_tools = [think_tool_name] + list(editor_tool_names)
            output = f"Unknown tool: '{tool_name}'. Valid tools are: {valid_tools}"

    except Exception as e:
        is_error = True
        output = f"An unexpected error occurred while running tool '{tool_name}': {e}"
        log.error(f"Error executing tool '{tool_name}': {e}", exc_info=True)

    return {
        "type": "tool_result",
        "tool_use_id": tool_use_id,
        "content": [{"type": "text", "text": output}],
        "is_error": is_error,
    }


async def _handle_tool_calls(
    tool_calls: List[ToolUseBlock],
    editor: EditTool20250124,
    think_tool: ThinkTool,
    model_name: str,
) -> Dict[str, Any]:
    """
    Processes a list of tool calls concurrently and formats the results.

    Args:
        tool_calls: A list of tool use blocks from the API.
        editor: An instance of the editor tool.
        think_tool: An instance of the think tool.
        model_name: The name of the model being used.

    Returns:
        A message dictionary containing the aggregated tool results.
    """
    tasks = [
        _process_single_tool_call(tc, editor, think_tool, model_name)
        for tc in tool_calls
    ]
    results = await asyncio.gather(*tasks)
    return {"role": "user", "content": results}


async def edit_file(
    file_path: str,
    edit_instructions: str,
    model: str,
    use_cache: Union[str, bool],
    verbose: bool,
    max_iterations: int,
) -> Tuple[bool, Optional[str], float]:
    """
    Orchestrates the file editing process using an LLM with tool-use capabilities.

    Args:
        file_path: The path to the file to be edited.
        edit_instructions: Natural language instructions for the edit.
        model: The Claude model to use.
        use_cache: Caching strategy ('auto', 'always', 'never', or boolean).
        verbose: If True, enables detailed logging.
        max_iterations: The maximum number of conversation turns.

    Returns:
        A tuple containing:
        - bool: True if the edit was successful, False otherwise.
        - Optional[str]: The final message from the LLM or an error message.
        - float: The total cost of the LLM API calls.
    """
    if verbose:
        log.setLevel(logging.INFO)

    total_cost = 0.0
    try:
        file_content, error = await read_file_async(Path(file_path))
        if error:
            raise FileNotFoundError(f"Could not read file '{file_path}': {error}")

        editor = EditTool20250124()
        think_tool = ThinkTool()
        cache_manager = CacheManager()

        # Determine if caching should be used based on policy and file content
        should_cache = cache_manager.should_use_cache(file_content, use_cache)
        log.info(f"Cache decision for '{file_path}': {should_cache} (mode: {use_cache})")

        # Construct the initial user message with file content and instructions
        initial_user_message = f"""
Here is the file to edit: `{file_path}`

File content:
```
{file_content}
```

My instruction is: "{edit_instructions}"
Please proceed with the necessary edits.
"""
        messages: List[Dict[str, Any]] = [{"role": "user", "content": initial_user_message}]

        for i in range(max_iterations):
            log.info(f"Iteration {i + 1}/{max_iterations}...")
            
            response, cost_info = await call_claude_api(
                messages=messages,
                model=model,
                system_prompt=SYSTEM_PROMPT,
                use_cache=should_cache,
            )
            total_cost += cost_info["total_cost"]
            log.info(f"API call cost: {format_cost(cost_info['total_cost'])}. Total cost so far: {format_cost(total_cost)}")

            # Append assistant's response to message history
            messages.append({"role": response.role, "content": response.content})

            if response.stop_reason == "tool_use":
                tool_calls = [block for block in response.content if isinstance(block, ToolUseBlock)]
                tool_results_message = await _handle_tool_calls(tool_calls, editor, think_tool, model)
                messages.append(tool_results_message)
                continue
            
            # If the model stops for any other reason, we assume it's finished.
            final_message = ""
            if response.content and hasattr(response.content[0], 'text'):
                final_message = response.content[0].text
            
            log.info(f"LLM finished editing. Final message: {final_message}")
            return True, final_message, total_cost

        return False, f"Max iterations ({max_iterations}) reached without completion.", total_cost

    except (EditToolError, FileNotFoundError, ValueError) as e:
        log.error(f"A controlled error occurred: {e}", exc_info=True)
        return False, str(e), total_cost
    except Exception as e:
        log.critical(f"An unexpected error occurred in the core orchestrator: {e}", exc_info=True)
        return False, f"An unexpected internal error occurred: {e}", total_cost
