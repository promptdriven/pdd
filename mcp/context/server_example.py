import logging
import asyncio
from pdd_mcp_server.server import create_server
import mcp.types as types
from mcp.transports.http import HttpTransport

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

async def main():
    """
    Main function that demonstrates the usage of PDD MCP Server.
    """
    # Create the MCP server using the factory function
    server = create_server()

    # Register PDD commands as MCP tools
    @server.tool("example_command")
    async def example_command(params: types.JsonObject) -> types.JsonObject:
        """
        Example PDD command exposed as an MCP tool.
        
        Args:
            params: A JSON object containing input parameters
                - input_text (str): Text to process
        
        Returns:
            A JSON object containing the results
                - result (str): Processed result
                - timestamp (str): Time when processing occurred
        """
        from datetime import datetime

        input_text = params.get("input_text", "")
        result = f"Processed: {input_text}"
        timestamp = datetime.now().isoformat()

        return {
            "result": result,
            "timestamp": timestamp
        }

    # Connect the server to a transport (e.g., HTTP)
    http_transport = HttpTransport(host="0.0.0.0", port=8080)
    server.connect(http_transport)

    # Start the server - this will run until stopped
    try:
        logger.info("Starting PDD MCP Server")
        await server.serve()
    except Exception as e:
        logger.error(f"Server error: {e}")
    finally:
        # Clean up resources when shutting down
        await server.stop()
        logger.info("Server stopped")

if __name__ == "__main__":
    # Run the async main function
    asyncio.run(main())