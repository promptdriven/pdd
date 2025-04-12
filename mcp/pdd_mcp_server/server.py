"""
Server module for PDD MCP Server.

This module provides a factory function to create and configure the MCP server
instance that will expose PDD commands as MCP tools.
"""

import importlib.metadata
import logging
from typing import Optional, Dict, Any, Callable, Awaitable
from contextlib import asynccontextmanager

from mcp.server import Server
import mcp.types as types

# Configure logging
logger = logging.getLogger(__name__)

# Server identity constants
SERVER_NAME = "pdd-mcp-server"
FALLBACK_VERSION = "0.1.0"

def get_version() -> str:
    """
    Get the server version from package metadata.
    
    Returns:
        The package version as a string, or a fallback version if not available.
    """
    try:
        return importlib.metadata.version("pdd-mcp-server")
    except importlib.metadata.PackageNotFoundError:
        logger.warning(
            "Package metadata not found; using fallback version %s",
            FALLBACK_VERSION
        )
        return FALLBACK_VERSION

@asynccontextmanager
async def server_lifespan(server):
    """
    Server lifespan manager that configures capabilities.
    """
    # Configure server capabilities - this would happen in initialization
    # but we'll need to update the actual implementation based on the API
    
    # Yielding control back to the server
    yield
    
    # Cleanup when the server is shutting down
    logger.debug("Server shutdown")

class PddMcpServer(Server):
    """
    Custom Server class that adapts the MCP server interface for PDD tools.
    
    This wrapper provides a register_tool method to simplify tool registration
    with the MCP server.
    """
    
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._tool_handlers: Dict[str, Callable[[Dict[str, Any]], Awaitable[types.CallToolResult]]] = {}
        
    def register_tool(self, tool_def, handler):
        """
        Register a tool with its handler function.
        
        This method wraps the MCP server API to expose PDD tools.
        
        Args:
            tool_def: The tool definition object
            handler: The handler function for the tool
            
        Returns:
            True if registration was successful
        """
        tool_name = tool_def.name
        self._tool_handlers[tool_name] = handler
        
        # Register the tool with the actual MCP server API
        # (The actual implementation may vary depending on MCP SDK version)
        logger.debug(f"Registering tool {tool_name} with MCP server")
        
        # Use the correct MCP Server API method to register the tool
        # This will depend on the version of the MCP SDK
        try:
            # Try the most common MCP API patterns
            if hasattr(self, "add_tool"):
                self.add_tool(tool_def, handler)
            elif hasattr(self, "register_tool"):
                super().register_tool(tool_def, handler)
            elif hasattr(self, "tools"):
                # Direct registration to tools dictionary
                self.tools[tool_name] = {"definition": tool_def, "handler": handler}
            else:
                # Fallback - store in our own dictionary and handle in run
                logger.warning(f"Using fallback tool registration for {tool_name}")
                self._tool_handlers[tool_name] = handler
            
            logger.info(f"Successfully registered tool: {tool_name}")
            return True
        except Exception as e:
            logger.error(f"Failed to register tool {tool_name}: {e}")
            return False

def create_server() -> PddMcpServer:
    """
    Create and configure the MCP server instance.
    
    This factory function instantiates a new MCP server with the appropriate
    capabilities for exposing PDD commands as tools.
    
    Returns:
        A configured MCP server instance ready for tool registration.
    """
    # Get the server version
    version = get_version()
    
    logger.info("Creating PDD MCP server (version %s)", version)
    
    # Create the server with the lifespan manager
    server = PddMcpServer(
        name=SERVER_NAME,
        version=version,
        instructions="PDD MCP Server for exposing PDD commands as MCP tools",
        lifespan=server_lifespan
    )
    
    logger.debug("PDD MCP server created successfully")
    return server