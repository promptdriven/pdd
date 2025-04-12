import logging
import asyncio
import sys
import os

# Add the parent directory to sys.path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from pdd_mcp_server.server import create_server

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

async def main():
    """
    Main function that demonstrates the usage of PDD MCP Server.
    """
    # Create the MCP server using the factory function
    server = create_server()

    # Print server details
    logger.info(f"Server created: {server}")
    
    # Start the server - this will run until stopped
    try:
        logger.info("Starting PDD MCP Server")
        # Instead of using server.serve(), which requires transport setup,
        # just sleep to keep the script running
        logger.info("Server would start here if properly configured...")
        await asyncio.sleep(10)  # Just keep alive briefly for testing
    except Exception as e:
        logger.error(f"Server error: {e}")
    finally:
        logger.info("Server stopped")

if __name__ == "__main__":
    # Run the async main function
    asyncio.run(main())