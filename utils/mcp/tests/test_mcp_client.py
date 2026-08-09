import asyncio
import os
import sys
from pathlib import Path

from mcp.stdio_client import StdioClient


async def main():
    repo_root = Path(__file__).resolve().parents[3]
    server_main = repo_root / "utils" / "mcp" / "pdd_mcp_server" / "main.py"
    prompt_file = repo_root / "examples" / "hello" / "hello_python.prompt"

    print("Starting MCP client...")
    client = StdioClient(
        command=sys.executable,
        args=["-u", str(server_main)],
        env={
            **os.environ,
            "SKIP_PYTHONDOTENV": "1",
            "PYTHONPATH": str(repo_root),
            "LOGLEVEL": "DEBUG",
        },
    )

    print("Connecting to server...")
    await client.initialize()

    print("Listing tools...")
    tools = await client.list_tools()
    print(f"Available tools: {[tool.name for tool in tools]}")

    if prompt_file.exists():
        print(f"Calling pdd-generate with prompt file: {prompt_file}")
        try:
            result = await client.call_tool("pdd-generate", {"prompt_file": str(prompt_file)})
            print("Result:", result)
        except Exception as exc:
            print(f"Error calling tool: {exc}")
    else:
        print(f"Prompt file not found: {prompt_file}")

    await client.shutdown()


if __name__ == "__main__":
    asyncio.run(main())
