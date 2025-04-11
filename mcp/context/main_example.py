import asyncio
import sys
import logging
import json
from typing import Dict, Any

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

    reader, writer = await asyncio.open_connection(host=None, port=None, stdin=sys.stdout.buffer, stdout=sys.stdin.buffer)

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

    writer.write(json.dumps(request).encode() + b'\n')
    await writer.drain()

    response_line = await reader.readline()
    response = json.loads(response_line.decode())

    logger.info(f"Received response: {json.dumps(response, indent=2)}")

    writer.close()
    await writer.wait_closed()

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
    asyncio.run(run_server())