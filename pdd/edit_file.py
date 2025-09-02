"""
File editor module that uses Claude 3.7 to edit files based on natural language instructions.

This module enables editing files through natural language instructions by:
1. Using a LangGraph workflow to manage the editing process
2. Leveraging Claude 3.7 Sonnet to understand instructions and plan edits
3. Using MCP (Model Control Protocol) tools to read and modify file contents
4. Tracking file state with hashes to ensure safe editing

Requirements:
- ANTHROPIC_API_KEY environment variable set with a valid Anthropic API key
- mcp-text-editor package installed (installed via 'pip install mcp-text-editor')
- A valid mcp_config.json file configured with an editor server

Example usage:
    success, error_msg = await edit_file("path/to/file.txt", "Replace all occurrences of 'foo' with 'bar'")
"""

import asyncio
import json
import os
import hashlib
import logging
import subprocess
import sys
from typing import TypedDict, Annotated, Optional, List, Tuple, Union, Sequence, Literal
import aiofiles
from pathlib import Path
import importlib.resources

# LangGraph imports
from langgraph.graph import StateGraph, END, START
from langgraph.graph.message import add_messages
from langgraph.prebuilt import ToolNode

# LangChain imports (assuming a model is needed for planning)
from langchain_core.messages import BaseMessage, HumanMessage, AIMessage, ToolMessage
# Replace with your preferred LLM provider if needed, e.g., langchain_anthropic
# from langchain_openai import ChatOpenAI
from pydantic import BaseModel, Field
from langchain_core.tools import BaseTool # Import BaseTool

# Anthropic imports for Claude 3.7
from langchain_anthropic import ChatAnthropic
from langchain_core.prompts import ChatPromptTemplate

# Import LangChain caching - use community package
from langchain import globals as langchain_globals
from langchain_community.cache import SQLiteCache

# MCP Adapter imports
from langchain_mcp_adapters.client import MultiServerMCPClient

# Setup logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Configure the SQLite cache
cache_path = ".langchain.db"
llm_cache = SQLiteCache(database_path=cache_path)
langchain_globals.set_llm_cache(llm_cache)

# --- State Definition ---
class EditFileState(TypedDict):
    """
    Represents the state of the file editing process.

    Attributes:
        file_path: The path to the file being edited.
        original_content: The initial content of the file.
        current_content: The content of the file after the latest edit.
        original_hash: The SHA256 hash of the original content.
        current_hash: The SHA256 hash of the current content.
        edit_instructions: The user-provided instructions for editing.
        messages: A list of messages tracking the conversation history for the agent.
        available_tools: List of MCP tools available for editing.
        error_message: An optional error message if something goes wrong.
        last_tool_call_successful: Flag to indicate if the last edit was successful.
    """
    file_path: str
    original_content: str
    current_content: str
    original_hash: str
    current_hash: str
    edit_instructions: str
    messages: Annotated[Sequence[BaseMessage], add_messages]
    available_tools: list # List[BaseTool] once loaded
    error_message: Optional[str]
    last_tool_call_successful: bool


# --- Utility Functions ---

def calculate_hash(content: str) -> str:
    """Calculates the SHA256 hash of the given content."""
    return hashlib.sha256(content.encode('utf-8')).hexdigest()

async def read_file_content(file_path: str) -> tuple[Optional[str], Optional[str]]:
    """Asynchronously reads file content and calculates its hash."""
    try:
        async with aiofiles.open(file_path, mode='r', encoding='utf-8') as f:
            content = await f.read()
            content_hash = calculate_hash(content)
            return content, content_hash
    except FileNotFoundError:
        logger.error(f"File not found: {file_path}")
        return None, None
    except IOError as e:
        logger.error(f"Error reading file {file_path}: {e}")
        return None, None
    except Exception as e:
        logger.error(f"Unexpected error reading file {file_path}: {e}")
        return None, None

async def write_file_content(file_path: str, content: str) -> bool:
    """Asynchronously writes content to a file."""
    try:
        async with aiofiles.open(file_path, mode='w', encoding='utf-8') as f:
            await f.write(content)
        return True
    except IOError as e:
        logger.error(f"Error writing file {file_path}: {e}")
        return False
    except Exception as e:
        logger.error(f"Unexpected error writing file {file_path}: {e}")
        return False

# --- LangGraph Nodes ---

async def start_editing(state: EditFileState) -> EditFileState:
    """Initializes the state with file content and hash."""
    logger.info(f"Starting edit process for: {state['file_path']}")
    content, content_hash = await read_file_content(state['file_path'])
    if content is None:
        return {
            **state,
            "error_message": f"Failed to read initial file content from {state['file_path']}.",
        }

    # Initialize messages with user instructions
    initial_messages = [
        HumanMessage(
            content=f"Please edit the file at '{state['file_path']}'. "
                    f"Here are the instructions: {state['edit_instructions']}\n\n"
                    f"Current file content:\n```\n{content}\n```"
        )
    ]

    return {
        **state,
        "original_content": content,
        "current_content": content,
        "original_hash": content_hash,
        "current_hash": content_hash,
        "messages": initial_messages,
        "error_message": None,
        "last_tool_call_successful": True, # Start optimistically
    }

def format_tools_for_claude(tools):
    """
    Create a summary of available tools and their proper usage format 
    to help Claude understand how to use them correctly.
    """
    tool_descriptions = []
    
    for tool in tools:
        description = f"Tool: {tool.name}\nDescription: {tool.description}\n"
        if hasattr(tool, 'args_schema'):
            description += f"Required Arguments: {str(tool.args_schema)}\n"
        tool_descriptions.append(description)
    
    return "\n".join(tool_descriptions)

async def plan_edits(state: EditFileState) -> EditFileState:
    """
    Uses Claude 3.7 to plan the next edit based on instructions and current content.
    Outputs an AIMessage with tool calls.
    """
    logger.info("Planning next edit with Claude 3.7...")
    if state.get("error_message"):
         logger.warning("Skipping planning due to previous error.")
         return {"messages": []} # No new messages if error occurred

    # Initialize Claude 3.7
    try:
        # Use environment variable for API key
        llm = ChatAnthropic(model="claude-3-7-sonnet-20250219", temperature=1, max_tokens=64000, thinking={"type": "enabled", "budget_tokens": 1024})
        # Cache is set globally now, no need to pass it to the model
        
        # Prepare the tools and their descriptions
        tools = state['available_tools']
        tool_descriptions = format_tools_for_claude(tools)
        
        # Add tool descriptions to the first message if this is the first planning step
        if len(state['messages']) == 1:
            first_message = state['messages'][0]
            enhanced_content = (
                f"{first_message.content}\n\n"
                f"Available tools:\n{tool_descriptions}\n\n"
                f"IMPORTANT: Always use absolute file paths. When editing, you need to first get the file contents "
                f"to obtain the range_hash before you can edit it."
            )
            enhanced_messages = [HumanMessage(content=enhanced_content)]
        else:
            enhanced_messages = state['messages']
        
        # Bind available tools to the model
        llm_with_tools = llm.bind_tools(tools)
        
        # Call Claude with the current state and messages
        response = await llm_with_tools.ainvoke(enhanced_messages)
        logger.info("Claude 3.7 planning complete.")
        
        return {"messages": [response]}
        
    except Exception as e:
        logger.error(f"Error during Claude 3.7 planning: {e}")
        error_message = AIMessage(content=f"I encountered an error while planning the edit: {str(e)}")
        return {"messages": [error_message]}


# ToolNode handles execution. We might need a wrapper for pre/post checks.
# Let's create a custom node for more control over hash checking and state updates.
async def execute_edit(state: EditFileState) -> EditFileState:
    """
    Executes the planned edit using MCP tools, verifies hash, and updates state.
    """
    logger.info("Attempting to execute edit...")
    ai_message = state['messages'][-1]
    if not isinstance(ai_message, AIMessage) or not ai_message.tool_calls:
        logger.warning("No tool calls found in the last AI message. Skipping execution.")
        # This might indicate the planning phase decided to finish.
        return {**state, "last_tool_call_successful": True} # No tool call, so technically not a failure

    # --- Hash Check Before Edit ---
    logger.debug("Verifying file hash before edit...")
    pre_edit_content, pre_edit_hash = await read_file_content(state['file_path'])
    if pre_edit_content is None:
         return {
             **state,
             "error_message": f"Failed to read file {state['file_path']} before edit.",
             "last_tool_call_successful": False,
         }
    if pre_edit_hash != state['current_hash']:
        logger.error(f"Hash mismatch for {state['file_path']}! Expected {state['current_hash']}, found {pre_edit_hash}. File may have been modified externally.")
        return {
            **state,
            "error_message": "File content changed unexpectedly before edit.",
            "last_tool_call_successful": False,
        }
    logger.debug("File hash verified.")

    # --- Execute Tool Call(s) via ToolNode logic ---
    # We'll simulate the ToolNode's core logic here for clarity on state updates
    tool_node = ToolNode(state['available_tools'])
    try:
        # ToolNode expects state['messages'] as input
        tool_result_state = await tool_node.ainvoke(state)
        tool_messages = tool_result_state.get("messages", [])
        logger.info(f"Tool execution completed. Result messages: {tool_messages}")

        # Check for errors within the ToolMessages (ToolNode adds error info)
        for msg in tool_messages:
            if isinstance(msg, ToolMessage) and msg.additional_kwargs.get("is_error", False):
                 error_content = msg.content
                 logger.error(f"MCP Tool execution failed: {error_content}")
                 return {
                     **state,
                     "messages": tool_messages, # Add tool error message to history
                     "error_message": f"MCP Tool execution failed: {error_content}",
                     "last_tool_call_successful": False,
                 }

    except Exception as e:
        logger.exception("Error during MCP tool execution.")
        error_msg = f"Failed to execute MCP tool: {e}"
        # Create a ToolMessage representing the error for the LLM
        tool_messages = []
        for tool_call in ai_message.tool_calls:
             tool_messages.append(ToolMessage(
                 content=f"Error executing tool {tool_call['name']}: {e}",
                 tool_call_id=tool_call['id'],
                 additional_kwargs={"is_error": True} # Flagging the error
             ))
        return {
            **state,
            "messages": tool_messages,
            "error_message": error_msg,
            "last_tool_call_successful": False,
        }

    # --- State Update After Successful Edit ---
    # Assuming the tool modified the file, we need to get the new content and hash.
    # Some MCP tools might return the new content, others might require a separate 'getContent' call.
    # For this example, let's assume we need to re-read the file.
    logger.info("Reading file content after successful edit...")
    post_edit_content, post_edit_hash = await read_file_content(state['file_path'])

    if post_edit_content is None:
        # This is problematic - the tool claimed success but we can't read the file
        error_msg = f"Tool execution seemed successful, but failed to read file {state['file_path']} afterwards."
        logger.error(error_msg)
        return {
            **state,
            "messages": tool_messages, # Include the successful tool message
            "error_message": error_msg,
            "last_tool_call_successful": False, # Mark as failure due to verification issue
        }

    logger.info(f"File content updated. New hash: {post_edit_hash}")
    return {
        **state,
        "messages": tool_messages, # Add the successful tool output messages
        "current_content": post_edit_content,
        "current_hash": post_edit_hash,
        "error_message": None, # Clear any previous error
        "last_tool_call_successful": True,
    }

def handle_error(state: EditFileState) -> EditFileState:
    """Handles errors encountered during the process."""
    logger.error(f"Entering error handling state. Error: {state.get('error_message', 'Unknown error')}")
    # The error message is already set in the state by the node that failed.
    # This node mainly serves as a terminal point in case of errors.
    return state # Return state as is, error message is already set

# --- Conditional Edges ---

def decide_next_step(state: EditFileState) -> Literal["execute_edit", "handle_error", END]:
    """Determines the next step after planning."""
    if state.get("error_message"):
        return "handle_error"
    last_message = state['messages'][-1]
    if last_message.__class__.__name__ == "AIMessage" and hasattr(last_message, "tool_calls") and last_message.tool_calls:
        logger.info("Decision: Execute tool call.")
        return "execute_edit"
    else:
        logger.info("Decision: No more tool calls planned, ending process.")
        return END

def check_edit_result(state: EditFileState) -> Literal["plan_edits", "handle_error"]:
     """Determines the next step after attempting an edit."""
     if not state.get("last_tool_call_successful", False) or state.get("error_message"):
         logger.warning("Edit failed or error occurred. Routing to error handler.")
         return "handle_error"
     else:
         # Even after a successful edit, we go back to planning
         # to see if more edits are needed based on the original instructions.
         logger.info("Edit successful. Routing back to planning.")
         return "plan_edits"

# --- Create the graph at module level for LangGraph to discover ---
# Build the graph definition
graph_builder = StateGraph(EditFileState)
graph_builder.add_node("start_editing", start_editing)
graph_builder.add_node("plan_edits", plan_edits)
graph_builder.add_node("execute_edit", execute_edit)
graph_builder.add_node("handle_error", handle_error)

graph_builder.add_edge(START, "start_editing")
graph_builder.add_edge("start_editing", "plan_edits")
graph_builder.add_conditional_edges("plan_edits", decide_next_step, {
    "execute_edit": "execute_edit",
    "handle_error": "handle_error",
    END: END
})
graph_builder.add_conditional_edges("execute_edit", check_edit_result, {
    "plan_edits": "plan_edits",
    "handle_error": "handle_error"
})
graph_builder.add_edge("handle_error", END)

# Compile the graph and expose it as a module-level variable
graph = graph_builder.compile()

# --- Main Function ---

async def edit_file(file_path: str, edit_instructions: str, mcp_config_path: str = None) -> tuple[bool, Optional[str]]:
    """
    Asynchronously edits a file based on instructions using LangGraph and MCP tools.

    Args:
        file_path: The path to the file to edit.
        edit_instructions: A description of the changes to make.
        mcp_config_path: Optional path to MCP config. If None, will look for 'pdd/mcp_config.json' within the package.

    Returns:
        A tuple containing:
            - success (boolean): Whether the file was edited successfully.
            - error_message (Optional[str]): An error message if unsuccessful, None otherwise.
    """
    # Print current working directory
    current_dir = os.getcwd()
    logger.info(f"Current working directory: {current_dir}")
    
    # 1. Initial File Validation
    if not os.path.exists(file_path):
        return False, f"File not found: {file_path}"
    if not os.access(file_path, os.R_OK) or not os.access(file_path, os.W_OK):
        return False, f"File not accessible (read/write permissions required): {file_path}"

    # 2. Load MCP Configuration
    if mcp_config_path is None:
        # Default to looking inside the package directory
        try:
            # Use importlib.resources to find the file within the 'pdd' package
            mcp_config_path_obj = importlib.resources.files('pdd').joinpath('mcp_config.json')
            # Check if the resource exists and is a file
            if mcp_config_path_obj.is_file():
                 mcp_config_path = str(mcp_config_path_obj)
                 logger.info(f"Using default MCP config from package: {mcp_config_path}")
            else:
                 # Handle case where default config isn't found in package
                 # Try CWD as a fallback (or raise error?)
                 fallback_path = os.path.join(os.getcwd(), 'pdd', 'mcp_config.json')
                 if os.path.exists(fallback_path):
                     mcp_config_path = fallback_path
                     logger.warning(f"Default MCP config not found in package, using fallback: {fallback_path}")
                 else:
                     return False, f"Default MCP configuration 'pdd/mcp_config.json' not found in package or current directory."

        except (ImportError, FileNotFoundError, Exception) as e:
             # Handle errors during resource discovery (e.g., package not found)
             logger.warning(f"Could not find default MCP config using importlib.resources: {e}. Trying CWD.")
             fallback_path = os.path.join(os.getcwd(), 'pdd', 'mcp_config.json')
             if os.path.exists(fallback_path):
                 mcp_config_path = fallback_path
                 logger.warning(f"Using fallback MCP config: {fallback_path}")
             else:
                return False, f"MCP configuration 'pdd/mcp_config.json' not found using importlib.resources or in current directory."
    
    # Ensure we have an absolute path if it's not None
    if mcp_config_path:
        mcp_config_path = os.path.abspath(mcp_config_path)
    else:
        # This case should ideally not be reached if the logic above is correct
        return False, "MCP configuration path could not be determined."

    mcp_servers_config = {}
    try:
        # Log absolute path of config file
        logger.info(f"Attempting to load MCP config from: {mcp_config_path}")
        
        with open(mcp_config_path, 'r') as f:
            mcp_servers_config = json.load(f)
        logger.info(f"Successfully loaded MCP configuration from {mcp_config_path}")
        # Basic validation of config structure
        if not isinstance(mcp_servers_config, dict) or not mcp_servers_config:
             raise ValueError("MCP config must be a non-empty dictionary.")
        # Example: Ensure a 'text_editor' server is defined (adjust key as needed)
        if 'my_editor_server' not in mcp_servers_config:
             logger.warning("MCP config doesn't contain a 'my_editor_server' server definition. Ensure your config is correct.")
             # Depending on requirements, you might want to raise an error here.

    except FileNotFoundError:
        return False, f"MCP configuration file not found: {mcp_config_path}"
    except json.JSONDecodeError:
        return False, f"Error decoding JSON from {mcp_config_path}"
    except ValueError as e:
         return False, f"Invalid MCP configuration: {e}"
    except Exception as e:
        return False, f"Unexpected error loading MCP config: {e}"

    # 3. MCP Client and Tool Loading
    available_tools = []
    try:
        async with MultiServerMCPClient(mcp_servers_config) as mcp_client:
            logger.info("MCP Client connected.")
            try:
                # get_tools() might return a list directly or a coroutine
                tools_result = mcp_client.get_tools()
                # Check if the result is awaitable before awaiting it
                if hasattr(tools_result, "__await__"):
                    available_tools = await tools_result
                else:
                    available_tools = tools_result
                
                logger.info(f"Discovered {len(available_tools)} MCP tools.")
                if not available_tools:
                    logger.warning("No MCP tools discovered. Editing will likely fail.")
                # Add validation for specific required tools if necessary
                # e.g., tool_names = {t.name for t in available_tools}
                # if "replace_text_tool_name" not in tool_names:
                #     return False, "Required MCP tool 'replace_text_tool_name' not found."

            except Exception as e:
                logger.exception("Failed to load MCP tools.")
                return False, f"Failed to load MCP tools: {e}"

            # 4. Setup and Run LangGraph
            # We're now using the global graph variable defined above
            app = graph  # Use the globally defined graph

            initial_state: EditFileState = {
                "file_path": file_path,
                "edit_instructions": edit_instructions,
                "available_tools": available_tools,
                # Other fields will be populated by start_editing
                "original_content": "",
                "current_content": "",
                "original_hash": "",
                "current_hash": "",
                "messages": [],
                "error_message": None,
                "last_tool_call_successful": True,
            }

            try:
                logger.info("Invoking LangGraph...")
                final_state = await app.ainvoke(initial_state)
                logger.info("LangGraph invocation complete.")

                # 5. Process Final State
                if final_state.get("error_message"):
                    logger.error(f"Graph finished with error: {final_state['error_message']}")
                    # Optionally try to restore original content if hash changed?
                    # For simplicity, just report error for now.
                    return False, final_state["error_message"]
                else:
                    # Check if content actually changed before writing
                    if final_state["current_hash"] != final_state["original_hash"]:
                        logger.info("File content changed, writing final version.")
                        # write_success = await write_file_content(file_path, final_state["current_content"])
                        # if not write_success:
                        #     return False, f"Successfully edited in memory, but failed to write final content to {file_path}"
                        # The execute_edit node already wrote the file via MCP tool
                        logger.info(f"File '{file_path}' edited successfully.")
                        return True, None
                    else:
                        logger.info("No changes made to the file content.")
                        return True, None # Success, but no changes needed/made

            except Exception as e:
                logger.exception("Error during LangGraph invocation.")
                return False, f"Error during graph execution: {e}"

    except Exception as e:
        logger.exception("Failed to connect or interact with MCP client.")
        return False, f"MCP Client error: {e}"


# --- Example Usage and Testing ---

async def main():
    """Main function to run the example."""
    # Check for required API key
    if "ANTHROPIC_API_KEY" not in os.environ:
        logger.error("ANTHROPIC_API_KEY environment variable is not set. Please set it before running this script.")
        return
        
    # Initialize and log SQLite cache location
    logger.info(f"Using SQLite cache at: {cache_path}")
        
    test_file_path = os.path.abspath("output/test_edit_file.txt")  # Use absolute path
    
    # --- Determine MCP Config Path for Example ---
    # Option 1: Assume running from project root during development
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) # Get project root (assuming script is in pdd/)
    mcp_config_path_example = os.path.join(project_root, 'pdd', 'mcp_config.json')

    # Option 2: Try using importlib.resources (might work if package installed editable)
    try:
        mcp_config_path_obj = importlib.resources.files('pdd').joinpath('mcp_config.json')
        if mcp_config_path_obj.is_file():
            mcp_config_path_example = str(mcp_config_path_obj)
        # else: keep the project root relative path
    except Exception:
        pass # Keep the project root relative path if importlib fails

    mcp_config_path_example = os.path.abspath(mcp_config_path_example)
    # --- /Determine MCP Config Path ---

    initial_content = "This is the initial content.\nIt has multiple lines."
    edit_instructions = "Replace the word 'initial' with 'edited' and add a new line at the end saying 'Edit complete.'"

    # 1. Create dummy MCP config if it doesn't exist (using the determined path)
    if not os.path.exists(mcp_config_path_example):
        # Log absolute path where config will be created
        logger.info(f"MCP config not found. Creating dummy config at: {mcp_config_path_example}")

        # Ensure parent directory exists
        os.makedirs(os.path.dirname(mcp_config_path_example), exist_ok=True)

        # IMPORTANT: Replace with your actual MCP server configuration
        # This dummy config assumes a server named 'my_editor_server' running via stdio
        dummy_config = {
            "my_editor_server": {
                "command": "npx",
                "args": ["-y", "mcp-server-text-editor"],
                "transport": "stdio"
            }
        }
        try:
            with open(mcp_config_path_example, 'w') as f:
                json.dump(dummy_config, f, indent=2)
            logger.info(f"Dummy MCP config created at: {mcp_config_path_example}")
        except Exception as e:
            logger.error(f"Could not create dummy MCP config: {e}")
            return

    # 2. Create the test file
    logger.info(f"Creating test file: {test_file_path}")
    async with aiofiles.open(test_file_path, mode='w', encoding='utf-8') as f:
        await f.write(initial_content)
    logger.info("Test file created with initial content.")

    # 3. Run the edit function
    logger.info("Calling edit_file function...")
    # --- IMPORTANT ---
    # Ensure your pdd/mcp_config.json points to a valid, running MCP server
    # that provides text editing tools (e.g., replace_text, insert_line, etc.)
    # The dummy response in plan_edits assumes a tool named 'replace_text_tool_name' exists.
    # You MUST adapt the dummy response or implement a real LLM planner
    # based on the actual tools provided by your MCP server.
    # --- /IMPORTANT ---
    success, error_msg = await edit_file(test_file_path, edit_instructions, mcp_config_path=mcp_config_path_example) # Use example path

    # 4. Verify the result
    if success:
        logger.info("edit_file completed successfully.")
        async with aiofiles.open(test_file_path, mode='r', encoding='utf-8') as f:
            final_content = await f.read()
        logger.info(f"Final file content:\n---\n{final_content}\n---")
        # Add specific checks for expected content if possible
        expected_content = "This is the edited content.\nIt has multiple lines.\nEdit complete."
        if final_content.strip() == expected_content.strip():
             logger.info("File content matches expected output.")
        else:
             logger.warning("File content does NOT match expected output.")
             logger.warning(f"Expected:\n{expected_content}")
             logger.warning(f"Got:\n{final_content}")

    else:
        logger.error(f"edit_file failed: {error_msg}")

def run_edit_in_subprocess(file_path: str, edit_instructions: str) -> Tuple[bool, Optional[str]]:
    """
    Run the edit_file function in a separate process to bridge between async and sync worlds.
    
    This function allows synchronous callers to use the asynchronous edit_file function without
    needing to manage async event loops themselves. It runs a child Python process that executes 
    a small script to run the async function and capture its results.
    
    Args:
        file_path: The path to the file to edit
        edit_instructions: Instructions for editing the file
        
    Returns:
        A tuple containing:
            - success (boolean): Whether the edit was successful
            - error_message (Optional[str]): Error message if unsuccessful, None otherwise
    """
    logger.info(f"Running edit_file in subprocess for: {file_path}")

    # --- Determine MCP Config Path for Subprocess ---
    # Default to package location unless specified otherwise (though this func doesn't take it as arg)
    mcp_config_abs_path = None
    try:
        mcp_config_path_obj = importlib.resources.files('pdd').joinpath('mcp_config.json')
        if mcp_config_path_obj.is_file():
             mcp_config_abs_path = str(mcp_config_path_obj)
             logger.info(f"Subprocess using default MCP config from package: {mcp_config_abs_path}")
        # else: # Fallback or error if needed, similar to edit_file function
        # For simplicity, assume it exists in package or was handled by caller
    except Exception as e:
         logger.warning(f"Could not find default MCP config for subprocess via importlib: {e}. Trying CWD relative path.")
         fallback_path = os.path.join(os.getcwd(), 'pdd', 'mcp_config.json')
         if os.path.exists(fallback_path):
             mcp_config_abs_path = fallback_path
             logger.warning(f"Subprocess using fallback MCP config: {fallback_path}")

    # Ensure we have an absolute path
    if mcp_config_abs_path:
        mcp_config_abs_path = os.path.abspath(mcp_config_abs_path)
    else:
        # Handle error: config path couldn't be determined
        logger.error("MCP config path could not be determined for subprocess.")
        return False, "MCP config path could not be determined for subprocess."

    # Get the actual directory of this module to pass to the subprocess
    module_dir = os.path.dirname(os.path.abspath(__file__))

    # Create a temporary Python script to run the async function
    script = f"""
import asyncio
import json
import os
import sys
import logging

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Add the module directory to sys.path to import the edit_file module
module_dir = {repr(module_dir)}
sys.path.append(module_dir)
from edit_file import edit_file

async def main():
    # Print current working directory in subprocess
    current_dir = os.getcwd()
    print(f"Subprocess working directory: {{current_dir}}")
    
    # Use the absolute path for MCP config passed from parent process
    mcp_config_path = {repr(mcp_config_abs_path)}
    print(f"Subprocess using MCP config at: {{mcp_config_path}}")
    print(f"MCP config exists: {{os.path.exists(mcp_config_path)}}")
    
    file_path = {repr(file_path)}
    edit_instructions = {repr(edit_instructions)}
    
    # Run the async edit_file function with explicit MCP config path
    success, error_msg = await edit_file(file_path, edit_instructions, mcp_config_path=mcp_config_path)
    
    # Return the result as JSON to stdout
    result = {{"success": success, "error_message": error_msg}}
    print(json.dumps(result))

if __name__ == "__main__":
    asyncio.run(main())
"""
    
    # Execute the script in a subprocess
    try:
        # Make sure the environment variable is passed to the subprocess
        env = os.environ.copy()
        result = subprocess.run(
            [sys.executable, "-c", script],
            capture_output=True,
            text=True,
            env=env
        )
        
        if result.returncode != 0:
            logger.error(f"Subprocess failed with return code {result.returncode}")
            logger.error(f"Stderr: {result.stderr}")
            return False, f"Subprocess error: {result.stderr}"
        
        # Parse the JSON result from stdout
        try:
            output = result.stdout.strip()
            # Find the last line that might be JSON (in case there's logging output)
            for line in reversed(output.split('\n')):
                try:
                    result_data = json.loads(line)
                    return result_data["success"], result_data["error_message"]
                except json.JSONDecodeError:
                    continue
            
            # If we get here, we couldn't find valid JSON
            logger.error(f"Could not parse subprocess output as JSON: {output}")
            return False, f"Could not parse subprocess output: {output}"
            
        except json.JSONDecodeError as e:
            logger.error(f"Failed to parse subprocess JSON output: {e}")
            logger.error(f"Output was: {result.stdout}")
            return False, f"Failed to parse subprocess result: {e}"
    
    except Exception as e:
        logger.exception(f"Error running subprocess: {e}")
        return False, f"Error running subprocess: {e}"

if __name__ == "__main__":
    # Ensure an event loop is running if executing directly (e.g., in a script)
    # In environments like Jupyter, this might not be necessary.
    try:
        asyncio.run(main())
    except RuntimeError as e:
        if "Cannot run the event loop while another loop is running" in str(e):
            # Handle cases where loop is already running (like in Jupyter)
            logger.info("Event loop already running, executing main directly.")
            # This might require adjustments depending on the environment
            # For simplicity, just calling await main() if loop exists
            # loop = asyncio.get_event_loop()
            # loop.run_until_complete(main())
            import nest_asyncio
            nest_asyncio.apply()
            asyncio.run(main())

        else:
            raise e 