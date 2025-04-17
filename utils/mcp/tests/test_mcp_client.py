import asyncio
import os
import sys
from mcp.stdio_client import StdioClient

async def main():
    # Create a client that spawns the server
    print("Starting MCP client...")
    client = StdioClient(
        command="/opt/anaconda3/envs/pdd/bin/python",
        args=["-u", "/Users/gregtanaka/pdd/mcp/pdd_mcp_server/main.py"],
        env={"SKIP_PYTHONDOTENV": "1", "PYTHONPATH": "/Users/gregtanaka/pdd", "LOGLEVEL": "DEBUG"}
    )
    
    # Connect to the server
    print("Connecting to server...")
    await client.initialize()
    
    # List available tools
    print("Listing tools...")
    tools = await client.list_tools()
    print(f"Available tools: {[tool.name for tool in tools]}")
    
    # Try to call the generate tool
    prompt_file = "/Users/gregtanaka/pdd/examples/hello.prompt"
    if os.path.exists(prompt_file):
        print(f"Calling pdd-generate with prompt file: {prompt_file}")
        try:
            result = await client.call_tool("pdd-generate", {"prompt_file": prompt_file})
            print("Result:", result)
        except Exception as e:
            print(f"Error calling tool: {e}")
    else:
        print(f"Prompt file not found: {prompt_file}")
    
    # Close the client
    await client.shutdown()

if __name__ == "__main__":
    asyncio.run(main()) 