import json
import os
import uuid
from typing import TypedDict, Annotated, Literal, Sequence, Optional

# Enable LangChain caching
from langchain.cache import SQLiteCache
from langchain.globals import set_llm_cache

# LangChain and LangGraph imports
from langchain_core.messages import HumanMessage, AIMessage, ToolMessage
# from langchain_openai import ChatOpenAI # Or any other chat model supporting tool calling
from langchain_anthropic import ChatAnthropic
from langgraph.graph import StateGraph, END, START, MessagesState
from langgraph.prebuilt import ToolNode, tools_condition, chat_agent_executor
from langgraph.checkpoint.memory import MemorySaver # Optional: If state needs persistence across calls

# MCP Adapter imports
from langchain_mcp_adapters.client import MultiServerMCPClient

# --- Configuration ---
# Assume an MCP server is running with a file editing tool.
# We'll load its details from a JSON config file.
MCP_CONFIG_FILE = "mcp_config.json"
DEFAULT_MCP_TOOL_NAME = "text_editor" # The expected name of the MCP tool

# --- Define Graph State ---

class EditFileState(TypedDict):
    """
    Represents the state of the file editing agent.

    Attributes:
        file_path: The path to the file being edited.
        edit_instructions: The natural language instructions for editing.
        messages: The history of messages exchanged within the graph.
        mcp_tools: A list of loaded MCP tools.
        success: Boolean indicating if the edit was successful.
        error_message: String containing an error message if unsuccessful.
    """
    file_path: str
    edit_instructions: str
    messages: MessagesState # Using prebuilt MessagesState for convenience (includes add_messages reducer)
    mcp_tools: list
    success: Optional[bool]
    error_message: Optional[str]

# --- Define Graph Nodes ---

async def load_mcp_tools_node(state: EditFileState) -> EditFileState:
    """
    Loads MCP tools based on the configuration file.
    Handles potential errors during loading.
    """
    print("---LOADING MCP TOOLS---")
    mcp_tools = []
    error_message = None
    success = None
    
    # Initialize basic state fields with defaults if not provided
    file_path = state.get("file_path", "unknown_file.txt")
    edit_instructions = state.get("edit_instructions", "Please edit the file")
    
    try:
        if not os.path.exists(MCP_CONFIG_FILE):
            raise FileNotFoundError(f"MCP configuration file not found: {MCP_CONFIG_FILE}")

        with open(MCP_CONFIG_FILE, 'r') as f:
            mcp_config = json.load(f)

        if not isinstance(mcp_config, dict):
            raise ValueError("Invalid MCP configuration format. Expected a dictionary.")

        # Create the client using async context manager
        async with MultiServerMCPClient() as client:
            # Connect to the text editor server
            await client.connect_to_server(
                "text_editor",
                command="uvx",
                args=["mcp-text-editor"],
                encoding_error_handler="ignore"
            )
            
            # Get tools
            mcp_tools = client.get_tools()
            if not mcp_tools:
                raise ValueError("No tools were loaded")
                
            success = True
            print(f"Loaded tools: {[t.name for t in mcp_tools]}")

    except Exception as e:
        print(f"Error loading MCP tools: {e}")
        error_message = f"Failed to load or connect to MCP tools: {e}"
        success = False

    return {
        "mcp_tools": mcp_tools,
        "error_message": error_message,
        "success": success,
        "file_path": file_path,
        "edit_instructions": edit_instructions
    }

def create_initial_prompt_node(state: EditFileState) -> EditFileState:
    """
    Creates the initial user message based on the input file path and instructions.
    """
    print("---CREATING INITIAL PROMPT---")
    # Only proceed if tools were loaded successfully
    if state.get("success") is False:
         print("Skipping initial prompt creation due to previous error.")
         return {} # No update needed if there was an error loading tools

    # Check if file_path and edit_instructions are provided in the state
    file_path = state.get("file_path")
    edit_instructions = state.get("edit_instructions")
    
    # If messages already exists, don't modify it
    if "messages" in state:
        return {}
        
    # Create an initial message if we have enough information
    if file_path and edit_instructions:
        initial_message = HumanMessage(content=f"""Please edit the file located at '{file_path}'. 
Instructions: <edit_instructions>{edit_instructions}</edit_instructions>

IMPORTANT: When editing the file, please:
1. Get the current content and hash first
2. Make one edit at a time, ensuring line numbers are valid:
   - Start line must be >= 1
   - End line must be >= start line
   - When replacing text, specify exact line ranges
3. Get the new hash after each edit
4. Use the new hash for the next edit
5. If you encounter a line range error, retry the edit with corrected line numbers""")
        
        return {"messages": [initial_message]}
    
    # If we don't have enough information, return an empty update
    return {}

async def agent_node(state: EditFileState) -> EditFileState:
    """
    The core agent logic. Calls the LLM with the current message history
    and the loaded MCP tools to decide the next action (call tool or finish).
    """
    print("---CALLING AGENT---")
    # Only proceed if tools were loaded successfully
    if state.get("success") is False:
         print("Skipping agent execution due to previous error.")
         # If tools failed to load, we should end here with failure
         return {"success": False, "error_message": state.get("error_message", "Unknown error during tool loading.")}

    # Handle case where messages may not exist in the state
    messages = state.get("messages", [])
    if not messages:
        # If messages is empty, initialize with a default message using file_path and edit_instructions
        file_path = state.get("file_path", "unknown_file.txt")
        edit_instructions = state.get("edit_instructions", "Please edit the file")
        
        # Create an initial message
        messages = [
            HumanMessage(content=f"""Please edit the file located at '{file_path}'. 
Instructions: <edit_instructions>{edit_instructions}</edit_instructions>

IMPORTANT: When editing the file, please:
1. Get the current content and hash first
2. Make one edit at a time, ensuring line numbers are valid:
   - Start line must be >= 1
   - End line must be >= start line
   - When replacing text, specify exact line ranges
3. Get the new hash after each edit
4. Use the new hash for the next edit
5. If you encounter a line range error, retry the edit with corrected line numbers""")
        ]
        # Update the state with the new messages
        state_update = {"messages": messages}
        return state_update

    mcp_tools = state["mcp_tools"]

    # Configure the LLM - replace with your preferred model
    # Ensure the model supports tool calling
    # Add OPENAI_API_KEY to your environment variables
    # llm = ChatOpenAI(model="gpt-4", temperature=0)
    llm = ChatAnthropic(model="claude-3-7-sonnet-20250219", temperature=1,  max_tokens=64000, thinking={"type": "enabled", "budget_tokens": 4000})
    llm_with_tools = llm.bind_tools(mcp_tools)

    # Invoke the LLM
    try:
        # Use await for async method
        response = await llm_with_tools.ainvoke(messages)
        # We return a list, because this will get added to the existing list
        return {"messages": [response]}
    except Exception as e:
        print(f"Error during agent LLM call: {e}")
        return {"success": False, "error_message": f"Agent LLM failed: {e}"}


# ToolNode handles the execution of the MCP tool if called by the agent
# It needs the list of tools available.
# We create it dynamically within the main function once tools are loaded.

def set_result_node(state: EditFileState) -> EditFileState:
    """
    Sets the final success/error status based on the agent's execution.
    Checks the last message for tool results or errors.
    """
    print("---SETTING FINAL RESULT---")
    # If success/error was already determined (e.g., during tool loading), keep it.
    if state.get("success") is not None:
        print(f"Result already set: success={state['success']}, error='{state.get('error_message', '')}'")
        return {"success": state["success"], "error_message": state.get("error_message")}

    # Handle case where messages may not exist in the state
    messages = state.get("messages", [])
    if not messages:
        error_message = "No messages in state, cannot determine result."
        print(error_message)
        return {"success": False, "error_message": error_message}
        
    last_message = messages[-1] if messages else None
    success = False
    error_message = "No edit performed or final result unclear."

    if isinstance(last_message, AIMessage) and not last_message.tool_calls:
        # Agent finished without calling a tool or after processing a tool result successfully
        # Check previous messages for ToolMessage indicating success/failure
        tool_messages = [msg for msg in reversed(messages) if isinstance(msg, ToolMessage)]
        if tool_messages:
            last_tool_message = tool_messages[0]
            if "error" not in last_tool_message.additional_kwargs and last_tool_message.content and "error" not in last_tool_message.content.lower():
                 # Assuming successful tool execution if no error in kwargs and content doesn't indicate error
                 success = True
                 error_message = None
                 print("Edit likely succeeded based on last tool message.")
            else:
                 error_content = last_tool_message.additional_kwargs.get("error", last_tool_message.content)
                 error_message = f"MCP tool execution failed: {error_content}"
                 print(f"Edit failed: {error_message}")
        else:
            # Agent finished without any tool interaction, maybe instructions were unclear?
             error_message = "Agent finished without attempting an edit. Instructions might be unclear or tool not called."
             print(error_message)


    elif isinstance(last_message, ToolMessage):
         # This case might happen if the graph ends immediately after the tool node
         if "error" not in last_message.additional_kwargs and last_message.content and "error" not in last_message.content.lower():
             success = True
             error_message = None
             print("Edit likely succeeded (ended after tool message).")
         else:
             error_content = last_message.additional_kwargs.get("error", last_message.content)
             error_message = f"MCP tool execution failed: {error_content}"
             print(f"Edit failed: {error_message}")

    else:
        # Handle unexpected end states
        error_message = f"Graph ended in an unexpected state. Last message: {type(last_message)}"
        print(error_message)


    return {"success": success, "error_message": error_message}

# --- Define Graph Edges ---

def should_continue_or_end(state: EditFileState) -> Literal["execute_mcp_tool", "set_result"]:
    """
    Determines the next step after the agent node.
    If the agent called a tool, execute it. Otherwise, set the final result.
    Also routes to set_result immediately if an error occurred earlier.
    """
    if state.get("success") is False: # Check if an early error occurred (e.g., tool loading)
        print("Routing to set_result due to previous error.")
        return "set_result"

    # Handle case where messages may not exist in the state
    messages = state.get("messages", [])
    if not messages:
        print("No messages in state, routing to set_result.")
        return "set_result"
        
    last_message = messages[-1]
    if last_message.tool_calls:
        print("Agent requested tool call. Routing to execute_mcp_tool.")
        return "execute_mcp_tool"
    else:
        print("Agent did not request tool call or finished processing. Routing to set_result.")
        return "set_result"

# --- Build the Graph ---

def build_graph():
    """Builds and returns an uncompiled StateGraph for the file editing workflow."""
    workflow = StateGraph(EditFileState)

    # Add nodes
    workflow.add_node("load_mcp_tools", load_mcp_tools_node)
    workflow.add_node("create_initial_prompt", create_initial_prompt_node)
    workflow.add_node("agent", agent_node)
    workflow.add_node("set_result", set_result_node)
    
    # Add a placeholder node for execute_mcp_tool that will handle minimal operation
    # This is needed for LangGraph Studio visualization
    async def placeholder_tool_node(state: EditFileState) -> EditFileState:
        """Basic implementation of tool execution for visualization purposes."""
        print("---EXECUTING PLACEHOLDER TOOL NODE---")
        # When running in LangGraph Studio, just pass through with a tool response message
        messages = state.get("messages", [])
        last_message = messages[-1] if messages else None
        
        if last_message and hasattr(last_message, "tool_calls") and last_message.tool_calls:
            # Get tool call ID - handle both dict and object formats
            tool_call_id = "placeholder-id"
            if last_message.tool_calls:
                tool_call = last_message.tool_calls[0]
                # Check if it's a dictionary (access via key) or object (access via attribute)
                if isinstance(tool_call, dict) and "id" in tool_call:
                    tool_call_id = tool_call["id"]
                elif hasattr(tool_call, "id"):
                    tool_call_id = tool_call.id
            
            # Create a simple tool response message
            tool_response = ToolMessage(
                content="This is a visualization placeholder. In real execution, MCP tools would be used.",
                tool_call_id=tool_call_id
            )
            return {"messages": messages + [tool_response]}
        
        # If there's no tool call or messages, just return the state unchanged
        return {}
    
    workflow.add_node("execute_mcp_tool", placeholder_tool_node)

    # Define edges
    workflow.add_edge(START, "load_mcp_tools")
    workflow.add_edge("load_mcp_tools", "create_initial_prompt")
    workflow.add_edge("create_initial_prompt", "agent")
    
    # Add edge from tool execution back to agent
    workflow.add_edge("execute_mcp_tool", "agent")

    # Conditional edge after the agent decides
    workflow.add_conditional_edges(
        "agent",
        should_continue_or_end,
        {
            "execute_mcp_tool": "execute_mcp_tool",
            "set_result": "set_result",
        },
    )

    # Final edge to end the process
    workflow.add_edge("set_result", END)

    return workflow

# Create an instance of the graph for LangGraph CLI
# Note: This is the uncompiled graph, it will be properly initialized
# and compiled when running via the CLI with necessary tools
graph = build_graph()

# A helper function to properly initialize the graph with required tools
async def get_initialized_graph():
    """
    Initializes the graph with required MCP tools and returns the compiled graph.
    This should be used at runtime, not during CLI graph discovery.
    """
    workflow = build_graph()
    
    # Create the MCP client and get tools
    async with MultiServerMCPClient() as client:
        # Connect to the text editor server
        await client.connect_to_server(
            "text_editor",
            command="uvx",
            args=["mcp-text-editor"],
            encoding_error_handler="ignore"
        )
        
        # Get tools
        tools = client.get_tools()
        if not tools:
            raise ValueError("No MCP tools were loaded")
            
        # Create a new tool node
        tool_node = ToolNode(tools)
        
        # Replace the placeholder with the real implementation
        # Instead of removing, just replace the node implementation
        workflow.update_node("execute_mcp_tool", tool_node)
        
        # Compile and return the initialized graph
        return workflow.compile()

# --- Main Function ---

async def edit_file(file_path: str, edit_instructions: str) -> tuple[bool, Optional[str]]:
    """
    Edits a file based on natural language instructions using a LangGraph agent
    that interacts with an MCP tool.

    Args:
        file_path: The path to the file to edit.
        edit_instructions: A description of the changes to make.

    Returns:
        A tuple containing:
        - success (boolean): Whether the file was edited successfully.
        - error_message (string | None): An error message if unsuccessful.
    """
    # Convert to absolute path
    abs_file_path = os.path.abspath(file_path)
    print(f"Attempting to edit file: {abs_file_path}")
    print(f"Instructions: {edit_instructions}")

    # Create MCP config if it doesn't exist
    if not os.path.exists(MCP_CONFIG_FILE):
        print(f"Warning: {MCP_CONFIG_FILE} not found. Creating configuration.")
        config = {
            "text_editor_server": {
                "command": "uvx",
                "args": ["mcp-text-editor"],
                "transport": "stdio"
            }
        }
        try:
            with open(MCP_CONFIG_FILE, 'w') as f:
                json.dump(config, f, indent=2)
            print(f"{MCP_CONFIG_FILE} created.")
        except IOError as e:
            return False, f"Failed to create MCP config file: {e}"

    # Load MCP tools
    try:
        async with MultiServerMCPClient() as client:
            # Connect to the text editor server
            await client.connect_to_server(
                "text_editor",
                command="uvx",
                args=["mcp-text-editor"],
                encoding_error_handler="ignore"
            )
            
            # Get tools
            tools = client.get_tools()
            if not tools:
                return False, "No tools were loaded"
            
            print(f"Loaded tools: {[t.name for t in tools]}")

            # First, get the current file content and hash with explicit line range validation
            try:
                get_content_result = await tools[0].ainvoke({
                    "files": [
                        {
                            "file_path": abs_file_path,
                            "ranges": [
                                {
                                    "start": 1,  # Always start from line 1
                                    "end": None,  # Let the tool determine the end
                                    "validate_range": True  # Add explicit validation flag
                                }
                            ]
                        }
                    ]
                })
                
                print(f"Tool response: {get_content_result}")
                print(f"Response type: {type(get_content_result)}")

                if isinstance(get_content_result, str):
                    try:
                        get_content_result = json.loads(get_content_result)
                    except json.JSONDecodeError:
                        return False, "Failed to parse tool response as JSON"

                if not isinstance(get_content_result, dict):
                    return False, f"Unexpected response type: {type(get_content_result)}"

                if "error" in get_content_result:
                    return False, f"Failed to get file content: {get_content_result['error']}"

                file_info = get_content_result.get(abs_file_path, {})
                file_hash = file_info.get("file_hash")

                if not file_hash:
                    return False, "Could not get file hash"

            except Exception as e:
                return False, f"Error during content retrieval: {str(e)}"

            # Instead of using our LangGraph structure, we'll create a simpler one for direct calls
            # to maintain backward compatibility
            try:
                print("simple graph")
                # Create the LLM
                llm = ChatAnthropic(model="claude-3-7-sonnet-20250219", temperature=1, max_tokens=64000, thinking={"type": "enabled", "budget_tokens": 4000})
                llm_with_tools = llm.bind_tools(tools)

                # Create a simple graph for this function call
                graph_builder = StateGraph(MessagesState)

                # Add nodes
                async def agent_node(state: MessagesState):
                    messages = state["messages"]
                    response = await llm_with_tools.ainvoke(messages)
                    return {"messages": [response]}

                tool_node = ToolNode(tools)

                graph_builder.add_node("agent", agent_node)
                graph_builder.add_node("tools", tool_node)

                # Add edges
                graph_builder.add_edge(START, "agent")
                graph_builder.add_conditional_edges(
                    "agent",
                    tools_condition,
                    {
                        "tools": "tools",
                        END: END,
                    }
                )
                graph_builder.add_edge("tools", "agent")

                # Compile the graph
                graph = graph_builder.compile()
            except Exception as e:
                return False, f"Error setting up agent: {str(e)}"

            # Run the graph with the current file hash
            initial_state = {
                "messages": [
                    HumanMessage(content=f"""Please edit the file located at '{abs_file_path}'. 
Instructions: <edit_instructions>{edit_instructions}</edit_instructions>
Current file hash: {file_hash}

IMPORTANT: When editing the file, please:
1. Get the current content and hash first
2. Make one edit at a time, ensuring line numbers are valid:
   - Start line must be >= 1
   - End line must be >= start line
   - When replacing text, specify exact line ranges
3. Get the new hash after each edit
4. Use the new hash for the next edit
5. If you encounter a line range error, retry the edit with corrected line numbers""")
                ]
            }

            # Run the graph
            try:
                # Run the graph and collect all events
                events = []
                async for event in graph.astream(initial_state):
                    events.append(event)

                # Check if any tool execution was successful
                success = False
                for event in events:
                    if "tools" in event:
                        tool_result = event["tools"]
                        if isinstance(tool_result, dict) and tool_result.get("messages"):
                            last_message = tool_result["messages"][-1]
                            if isinstance(last_message, ToolMessage):
                                if "error" in last_message.additional_kwargs or (isinstance(last_message.content, str) and "error" in last_message.content.lower() and not last_message.content.startswith("{")):
                                    error_content = last_message.additional_kwargs.get("error", last_message.content)
                                    if "Content hash mismatch" in error_content:
                                        # This is expected when making multiple edits
                                        continue
                                    if "End line must be greater than or equal to start line" in error_content:
                                        # Line range error - let the agent retry with corrected numbers
                                        continue
                                    return False, f"Tool execution failed: {error_content}"
                                else:
                                    success = True  # At least one successful tool execution

                # Verify the final state of the file
                if os.path.exists(abs_file_path):
                    with open(abs_file_path, 'r') as f:
                        final_content = f.read()
                    
                    # Check if any changes were made
                    if final_content != get_content_result[abs_file_path]["ranges"][0]["content"]:
                        return True, None
                    else:
                        return False, "No changes were made to the file"

                return False, "File does not exist after edits"

            except Exception as e:
                print(f"Error during graph execution: {e}")
                return False, str(e)

    except Exception as e:
        print(f"Error during execution: {e}")
        return False, str(e)

# --- Example Usage (requires async context) ---
async def main():
    # Create a dummy file for testing
    test_file = "test_edit_file.txt"
    with open(test_file, "w") as f:
        f.write("This is the original content.\nLine 2.\nLine 3.")

    # Define edit instructions
    instructions = "Change 'original' to 'modified' on the first line and delete line 2."

    # IMPORTANT: Ensure mcp_config.json points to a running MCP server
    # with a tool named 'file_editor' (or update DEFAULT_MCP_TOOL_NAME)
    # that accepts 'file_path' and 'edit_instructions'.
    # For this example to run without a real MCP server, it will fail at the tool loading/execution step.
    print("\n--- RUNNING edit_file ---")
    try:
        success, error = await edit_file(test_file, instructions) # Use await
        print(f"\n--- edit_file Result ---")
        print(f"Success: {success}")
        if error:
            print(f"Error: {error}")

        # Verify file content (if successful and a real MCP was used)
        if success and os.path.exists(test_file):
             print("\n--- Final File Content ---")
             with open(test_file, "r") as f:
                 print(f.read())
        elif not success and os.path.exists(test_file):
             print("\n--- File Content After Failed Edit ---")
             with open(test_file, "r") as f:
                 print(f.read()) # Show original content if edit failed

    finally:
        # Clean up the dummy file
        if os.path.exists(test_file):
            # os.remove(test_file)
            print(f"\n(Keeping {test_file} for inspection)")
            pass


if __name__ == "__main__":
    import asyncio
    # Enable LangChain caching with SQLite
    set_llm_cache(SQLiteCache(database_path=".langchain.db"))
    
    # Create mcp_config.json with the correct configuration for mcp-text-editor
    if not os.path.exists(MCP_CONFIG_FILE):
        print(f"Creating {MCP_CONFIG_FILE} for mcp-text-editor")
        config = {
            "text_editor_server": {
                "command": "uvx",
                "args": ["mcp-text-editor"],
                "transport": "stdio"
            }
        }
        with open(MCP_CONFIG_FILE, 'w') as f:
            json.dump(config, f, indent=2)
    
    # Run the async main function
    asyncio.run(main())