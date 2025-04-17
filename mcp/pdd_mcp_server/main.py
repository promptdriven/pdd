import asyncio
import logging
import sys
import os
from typing import Dict, Any

# Import MCP SDK - use FastMCP which is more declarative and simpler
try:
    from mcp.server.fastmcp import FastMCP
    import mcp.types as types
except ImportError:
    logger = logging.getLogger(__name__)
    logger.error("MCP SDK not found. Please install it with: pip install mcp")
    sys.exit(1)

# Use direct imports from the local package
try:
    from tools import definitions
    from tools import handlers
except ImportError:
    try:
        # Alternative: try relative imports
        from .tools import definitions
        from .tools import handlers
    except ImportError:
        logger = logging.getLogger(__name__)
        logger.error("Failed to import tools modules. Check that tools/ directory exists with __init__.py")
        sys.exit(1)

# Configure logging
log_level = os.environ.get("LOGLEVEL", "INFO").upper()
numeric_level = getattr(logging, log_level, logging.INFO)
logging.basicConfig(
    level=numeric_level,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    stream=sys.stderr,
    force=True
)
logger = logging.getLogger(__name__)
logger.info("Log level set to %s", log_level)

# Define server initialization message and workflow prompt
INITIALIZATION_MESSAGE = """
PDD MCP Server v1.0.0: Prompt-Driven Development Tools

CORE CONCEPT:
In Prompt-Driven Development (PDD), prompts are the primary artifact, while code is generated. 
When changes are needed, modify prompts rather than directly editing code.

TOOL CATEGORIES:
- Code Generation: pdd-generate, pdd-example
- Testing & Debugging: pdd-test, pdd-fix, pdd-bug, pdd-crash
- Maintenance: pdd-update, pdd-change, pdd-trace
- Refactoring: pdd-split, pdd-auto-deps, pdd-conflicts, pdd-detect
- Preprocessing: pdd-preprocess

CRITICAL NOTES:
- 'force': true required for all file-writing operations
- After prompt changes, 'example' must be updated to reflect interfaces
- pdd-fix supports loop mode (automated iterative fixing) by setting 'loop': true
- ERROR_FILE is always required for pdd-fix (even with loop=true), but can be a path to a non-existent file when using loop mode

For detailed workflow guidance, see the 'pdd-workflows' prompt.
"""

# Create a FastMCP server instance
mcp = FastMCP(
    name="pdd-mcp-server",
    version="0.1.0",  
    description="PDD MCP Server for exposing PDD commands as MCP tools",
    instructions=INITIALIZATION_MESSAGE
)

# Define the workflow prompt
WORKFLOW_PROMPT = {
    "id": "pdd-workflows",
    "name": "PDD Workflow Guide",
    "description": "Detailed guide for PDD tool workflows and dependencies",
    "content": """
# PDD Workflow Dependencies

## Critical Tool Dependencies
- 'generate' must be done before 'example' or 'test'
- 'crash' is used to fix runtime errors and make code runnable
- 'fix' requires runnable code created/verified by 'crash'
- 'test' must be created before using 'fix'
- After major prompt changes, 'example' must be updated to reflect interface changes

## Parameters to Remember
- 'force': true required for all file-writing operations to prevent hangs waiting for user confirmation
- When using 'fix' with loop=true, make sure to include 'verification_program'

## Key Tool Distinctions
- 'generate': Complete implementation code (larger, comprehensive)
- 'example': Interface/usage examples only (smaller, token-efficient)
- 'crash': Fixes runtime errors in code to make it executable
- 'fix': Resolves test failures in already-runnable code
  - Standard mode: Requires error_file with test failures
  - Loop mode: Automatically runs tests and fixes issues iteratively until success
- 'update': Sync code changes back to prompts (prompt is source of truth)
- 'split': Extract modular functionality while preserving imports

## Fix Loop Mode
The fix command supports an iterative fixing process with the 'loop' parameter:

1. How it works:
   - Runs the verification program to generate error output
   - Analyzes errors and makes fixes to both code and tests
   - Repeats until all tests pass or max attempts reached

2. Required parameters:
   - prompt_file, code_file, unit_test_file: Standard required parameters
   - error_file: Required by CLI constraints, but can be a non-existent file path when using loop mode
   - verification_program: Program to run for validation (REQUIRED with loop)
   - loop: Set to true to enable iterative fixing

3. Optional parameters:
   - max_attempts: Maximum fix iterations (default: 3)
   - budget: Maximum cost allowed for the process (default: $5.0)
   - output_code, output_test: Where to save fixed files

4. Example:
   {
     "prompt_file": "/path/to/prompt.txt", 
     "code_file": "/path/to/code.py", 
     "unit_test_file": "/path/to/test.py", 
     "error_file": "/path/to/errors.log",
     "loop": true,
     "verification_program": "/path/to/example.py",
     "force": true
   }

## Recommended Workflows

1. Initial Development Pipeline:
   auto-deps → generate → example → crash → test → fix
   *Creates new functionality from scratch with proper testing*

2. Code-to-Prompt Update Pipeline:
   update → detect → change
   *Maintains prompt as source of truth after code changes*

3. Refactoring Pipeline:
   split → auto-deps → example
   *Breaks large prompts into modular components*

## Debugging Workflows

1. Prompt Context Issues:
   preprocess → generate
   *When generating incorrect code due to prompt preprocessing issues*

2. Runtime Crash Debugging:
   generate → example → crash
   *When initial code has syntax errors or crashes on execution*

3. Logical Bug Fixing:
   bug → fix
   *When code runs but produces incorrect results*

4. Debugger-Guided Analysis:
   trace → [edit prompt directly]
   *When stepping through code with a debugger to identify issues*

5. Widespread Changes:
   trace → detect → change
   *When issues affect multiple prompts*

## Architecture & Integration Workflows

1. Multi-Prompt Architecture:
   conflicts/detect → change → generate → example → test
   *When multiple prompts are created from PRD/architecture docs and need alignment*
   *Example must be updated after major prompt changes to reflect interface changes*

2. Feature Enhancement:
   change → generate → example → test → fix
   *Adds new features to existing functionality*
"""
}

# Register the workflow prompt using decorator pattern
@mcp.prompt(
    name=WORKFLOW_PROMPT["name"],
    description=WORKFLOW_PROMPT["description"]
)
def pdd_workflows():
    """PDD workflow guidance prompt"""
    return WORKFLOW_PROMPT["content"]

# Create a simple function to register a tool - we'll use this to handle the schema difference
def register_tool(tool_def):
    """Register a PDD tool with the server."""
    handler_name = f"handle_{tool_def.name.replace('-', '_')}"
    handler = getattr(handlers, handler_name, None)
    
    if not handler:
        logger.warning(f"No handler found for tool definition: {tool_def.name}. Skipping registration.")
        return False
        
    try:
        # Create a wrapper for the handler that accepts typed parameters
        # and explicitly forbids 'kwargs' parameter to force proper usage
        @mcp.tool(
            name=tool_def.name, 
            description=tool_def.description
        )
        async def wrapped_handler(**kwargs):
            """Tool wrapper that sends parameters to the appropriate handler."""
            try:
                # Process kwargs in various formats
                
                # 1. Handle nested kwargs dict (API client might send this)
                if 'kwargs' in kwargs and isinstance(kwargs['kwargs'], dict):
                    inner_params = kwargs.pop('kwargs')
                    kwargs.update(inner_params)
                    logger.debug(f"Processed nested kwargs dict for {tool_def.name}")
                
                # 2. Handle JSON string kwargs (Claude Code sends this)
                elif 'kwargs' in kwargs and isinstance(kwargs['kwargs'], str):
                    try:
                        # Parse the JSON string into a dict
                        import json
                        json_kwargs = kwargs['kwargs']
                        inner_params = json.loads(json_kwargs)
                        if isinstance(inner_params, dict):
                            # Update the kwargs with the parsed values
                            kwargs.pop('kwargs')  # Remove the original kwargs
                            kwargs.update(inner_params)
                            logger.debug(f"Successfully parsed JSON kwargs for {tool_def.name}: {inner_params}")
                        else:
                            logger.warning(f"JSON kwargs for {tool_def.name} is not a dict: {inner_params}")
                    except json.JSONDecodeError as e:
                        logger.warning(f"Failed to parse JSON kwargs for {tool_def.name}: {str(e)}")
                        # Continue with the original kwargs
                
                # Call the handler
                return await handler(kwargs)
            except Exception as e:
                logger.exception(f"Error in {tool_def.name}: {str(e)}")
                return types.CallToolResult(
                    isError=True, 
                    content=[types.TextContent(text=f"Tool error: {str(e)}", type="text")]
                )
        
        logger.info(f"Registered tool: {tool_def.name}")
        return True
    except Exception as e:
        logger.error(f"Failed to register tool '{tool_def.name}': {e}", exc_info=True)
        return False

async def main_async():
    """Main entry point for the MCP server."""
    logger.info("Starting PDD MCP Server...")
    
    # Register all PDD tools
    registered_count = 0
    for tool_def in definitions.PDD_TOOLS:
        if register_tool(tool_def):
            registered_count += 1
    
    if registered_count > 0:
        logger.info(f"Successfully registered {registered_count} out of {len(definitions.PDD_TOOLS)} defined tools.")
    else:
        logger.error("CRITICAL: No tools were successfully registered. Server will not be functional.")
        return
    
    # The prompt is now registered via decorator, no need for explicit registration
    
    try:
        # Run the server with stdio transport
        logger.info("Running PDD MCP Server with stdio transport...")
        await mcp.run_stdio_async()
    except Exception as e:
        logger.exception("Server loop encountered an unhandled exception.")
    finally:
        logger.info("PDD MCP Server shutting down...")

if __name__ == "__main__":
    try:
        asyncio.run(main_async())
    except KeyboardInterrupt:
        logger.info("Server stopped by user (KeyboardInterrupt).")
        sys.exit(0)
    except Exception as e:
        logger.critical(f"Critical error during server startup or final shutdown: {e}", exc_info=True)
        sys.exit(1)