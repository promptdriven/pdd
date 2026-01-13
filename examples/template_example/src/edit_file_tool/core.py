import os
import json
import logging
from pathlib import Path
from typing import Tuple, Union, List, Dict, Optional

from edit_file_tool import cache_manager_utility
from edit_file_tool import think_tool_capability

# Setup logging
logger = logging.getLogger(__name__)

async def edit_file(
    file_path: str,
    edit_instructions: str,
    model: str = 'claude-haiku-4-5@20251001',
    verbose: bool = False,
    use_cache: Union[str, bool] = 'auto',
    max_iterations: int = 10
) -> Tuple[bool, str, float]:
    """
    Orchestrates the end-to-end workflow to edit a file via Claude.
    """
    # 1. Validate inputs
    error = _validate_inputs(file_path, edit_instructions, max_iterations)
    if error:
        return (False, error, 0.0)

    # 2. Read file and determine caching
    try:
        file_content = Path(file_path).read_text(encoding="utf-8")
        file_size = os.path.getsize(file_path)
    except Exception as e:
        return (False, f"Error reading file: {str(e)}", 0.0)

    use_caching = cache_manager_utility.should_use_cache(file_path, file_size, use_cache)
    
    if verbose:
        logger.info(f"Starting edit on {file_path}. Caching enabled: {use_caching}")

    # 3. Build initial messages (OpenAI format for LiteLLM compatibility)
    messages = _build_initial_messages(file_path, file_content, edit_instructions, use_caching)

    # 4. Build tools schema
    tools = _build_tools_schema()

    total_cost = 0.0
    
    # 5. MAIN ITERATION LOOP
    for iteration in range(max_iterations):
        if verbose:
            logger.info(f"Iteration {iteration + 1}/{max_iterations}...")

        # Call real API via think_tool_capability
        response, iteration_cost = await think_tool_capability.invoke_with_thinking(
            messages=messages,
            tools=tools,
            model=model
        )
        total_cost += iteration_cost

        if verbose:
            usage = response.get("usage", {})
            logger.info(f"Iteration {iteration + 1} cost: ${iteration_cost:.6f}. Usage: {usage}")

        content_blocks = response.get("content", [])
        tool_uses = [block for block in content_blocks if block.get("type") == "tool_use"]

        # If no tool use, Claude is finished
        if not tool_uses:
            if verbose:
                logger.info("No tool use requested. Edit workflow complete.")
            return (True, "", total_cost)

        # Append assistant message with tool_calls in OpenAI format
        assistant_msg = {
            "role": "assistant",
            "tool_calls": []
        }
        
        for tu in tool_uses:
            if tu.get("name") == "text_editor_20250124":
                assistant_msg["tool_calls"].append({
                    "id": tu["id"],
                    "type": "function",
                    "function": {
                        "name": tu["name"],
                        "arguments": json.dumps(tu["input"])
                    }
                })
        
        messages.append(assistant_msg)

        # Execute tool operations and append results
        for tu in tool_uses:
            if tu.get("name") == "text_editor_20250124":
                tool_result = _execute_text_editor(tu["input"])
                # Append tool result in OpenAI format
                messages.append({
                    "role": "tool",
                    "tool_call_id": tu["id"],
                    "name": tu["name"],
                    "content": tool_result
                })

    return (False, f"Max iterations ({max_iterations}) reached without completing the edit.", total_cost)

def _validate_inputs(file_path: str, edit_instructions: str, max_iterations: int) -> Optional[str]:
    """Validates input parameters according to exact error format requirements."""
    if not file_path:
        return "file_path must be non-empty"
    if not edit_instructions:
        return "edit_instructions must be non-empty"
    if max_iterations < 1:
        return "max_iterations must be at least 1"
    
    path_obj = Path(file_path)
    if not path_obj.exists():
        return "file_path does not exist"
    if not path_obj.is_file():
        return "file_path is not a file"
    return None

def _build_initial_messages(file_path: str, file_content: str, edit_instructions: str, caching_enabled: bool) -> List[dict]:
    """Builds the initial message list with optional prompt caching."""
    content_blocks = []
    
    # File content block
    file_block = {
        "type": "text",
        "text": f"Target file: {file_path}\nContent:\n{file_content}"
    }
    if caching_enabled:
        file_block["cache_control"] = {"type": "ephemeral"}
    
    content_blocks.append(file_block)
    
    # Instructions block (uncached as it is dynamic)
    content_blocks.append({
        "type": "text",
        "text": f"Instructions: {edit_instructions}"
    })

    return [{"role": "user", "content": content_blocks}]

def _build_tools_schema() -> List[dict]:
    """Returns the text_editor_20250124 tool definition."""
    return [{
        "name": "text_editor_20250124",
        "description": "A text editor tool to view, create, and edit files. Use 'view' to see content, 'str_replace' to edit, 'insert' to add lines, and 'undo_edit' to revert.",
        "input_schema": {
            "type": "object",
            "properties": {
                "command": {
                    "type": "string", 
                    "enum": ["view", "create", "str_replace", "insert", "undo_edit"]
                },
                "path": {"type": "string"},
                "file_text": {"type": "string"},
                "old_str": {"type": "string"},
                "new_str": {"type": "string"},
                "insert_line": {"type": "integer"},
                "view_range": {"type": "array", "items": {"type": "integer"}}
            },
            "required": ["command", "path"]
        }
    }]

def _execute_text_editor(tool_input: Dict) -> str:
    """Executes text_editor operations on actual files."""
    command = tool_input.get("command")
    path = tool_input.get("path")
    
    try:
        p = Path(path)
        
        if command == "view":
            return p.read_text(encoding="utf-8")
            
        elif command == "create":
            content = tool_input.get("file_text", "")
            p.write_text(content, encoding="utf-8")
            return f"File created successfully at {path}"
            
        elif command == "str_replace":
            old_str = tool_input.get("old_str")
            new_str = tool_input.get("new_str")
            content = p.read_text(encoding="utf-8")
            if old_str not in content:
                return f"Error: 'old_str' not found in {path}"
            new_content = content.replace(old_str, new_str, 1)
            p.write_text(new_content, encoding="utf-8")
            return "Replacement successful."
            
        elif command == "insert":
            insert_line = tool_input.get("insert_line", 0)
            new_str = tool_input.get("new_str", "")
            lines = p.read_text(encoding="utf-8").splitlines(keepends=True)
            lines.insert(insert_line, new_str + "\n")
            p.write_text("".join(lines), encoding="utf-8")
            return "Insertion successful."
            
        elif command == "undo_edit":
            return "undo_edit is currently unsupported in this environment."
            
        else:
            return f"Error: Unknown command '{command}'"
            
    except Exception as e:
        return f"Error executing {command}: {str(e)}"