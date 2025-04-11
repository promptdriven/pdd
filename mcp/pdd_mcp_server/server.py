"""
Server module for PDD MCP Server.

This module provides a factory function to create and configure the MCP server
instance that will expose PDD commands as MCP tools.
"""

import importlib.metadata
import logging
from typing import Optional

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

def create_server() -> Server:
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
    
    # Configure server capabilities
    capabilities = types.ServerCapabilities(
        # Enable tools capability to expose PDD commands
        tools=types.ServerCapabilities.Tools(
            # We don't currently support dynamic tool list changes,
            # but could enable this in the future if needed
            listChanged=False
        ),
        # Enable logging capability for diagnostics
        logging=types.ServerCapabilities.Logging()
    )
    
    # Create and return the server instance
    server = Server(
        SERVER_NAME,
        version=version,
        capabilities=capabilities
    )
    
    logger.debug("PDD MCP server created successfully")
    return server