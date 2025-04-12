import asyncio
import sys
import logging
import json
from typing import Dict, Any
import os

# Add the parent directory to sys.path so we can import pdd_mcp_server
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd_mcp_server import main
from pdd_mcp_server.tools import definitions

logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)

async def run_server():
    """
    Run the PDD MCP Server in its own process.
    """
    await main.main_async()

async def client_example():
    """
    Example client that calls the PDD generate tool.
    """
    logger.info("Starting client example")

    # Create a subprocess for the server
    process = await asyncio.create_subprocess_exec(
        sys.executable, "-m", "pdd_mcp_server.main",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )

    request = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "callTool", 
        "params": {
            "name": "pdd-generate",
            "parameters": {
                "prompt_file": "example.prompt",
                "output": "output.py",
                "strength": 0.7,
                "temperature": 0.2,
                "force": True,
                "verbose": True
            }
        }
    }

    # Write to stdin of the subprocess
    process.stdin.write(json.dumps(request).encode() + b'\n')
    await process.stdin.drain()

    # Read response from stdout
    response_line = await process.stdout.readline()
    response = json.loads(response_line.decode())

    logger.info(f"Received response: {json.dumps(response, indent=2)}")

    # Close the subprocess
    process.terminate()
    await process.wait()

def display_available_tools():
    """
    Display all available PDD tools with their descriptions and parameters.
    """
    print("\nAvailable PDD Tools:")
    print("===================")

    for tool_def in definitions.PDD_TOOLS:
        print(f"\n{tool_def.name}: {tool_def.description}")

        required = tool_def.inputSchema.get("required", [])
        print(f"  Required parameters: {', '.join(required)}")

        properties = tool_def.inputSchema.get("properties", {})
        for param, details in properties.items():
            param_type = details.get("type", "any")
            desc = details.get("description", "No description")
            required_mark = "(required)" if param in required else "(optional)"
            print(f"  - {param} [{param_type}] {required_mark}: {desc}")

if __name__ == "__main__":
    # Display the tools instead of running the server
    #asyncio.run(run_server())
    #asyncio.run(client_example())
    display_available_tools()