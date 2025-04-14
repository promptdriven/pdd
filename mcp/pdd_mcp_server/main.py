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

# Create a FastMCP server instance
mcp = FastMCP(
    name="pdd-mcp-server",
    version="0.1.0",  
    description="PDD MCP Server for exposing PDD commands as MCP tools"
)

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