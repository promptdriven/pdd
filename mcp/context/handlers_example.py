import asyncio
import logging
from typing import Dict, Any
import mcp.types as types

# Import the handler function
from pdd_mcp_server.tools.handlers import handle_pdd_generate

# Set up logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

async def main():
    """
    Demonstrate how to use the PDD MCP handlers module to generate code.
    """
    # Create arguments dictionary for the pdd-generate tool
    # The 'prompt_file' parameter is required
    generate_args: Dict[str, Any] = {
        "prompt_file": "calculator.prompt",  # Required: Path to the prompt file
        "output": "calculator.py",           # Optional: Output file path
        "strength": 0.7,                     # Optional: Model strength (0.0-1.0)
        "temperature": 0.2,                  # Optional: Generation temperature
        "local": True,                       # Optional: Use local execution
        "force": True,                       # Optional: Overwrite output file if it exists
        "verbose": True,                     # Optional: Enable verbose output
        "quiet": False,                      # Optional: Suppress non-essential output
        "output_cost": "cost.json",          # Optional: File to save cost information
        "review_examples": True              # Optional: Review examples during generation
    }
    
    logger.info("Calling handle_pdd_generate with arguments: %s", generate_args)
    
    # Call the handler function and await the result
    result: types.CallToolResult = await handle_pdd_generate(generate_args)
    
    # Process the result
    if not result.isError:
        logger.info("Generation successful!")
        
        # Access the output text
        output_text = result.content[0].text
        logger.info("First 100 characters of output: %s", output_text[:100])
        
        # Use the generated output (e.g., save to file, process further)
        print("Generator output:")
        print("=" * 40)
        print(output_text)
        print("=" * 40)
    else:
        logger.error("Generation failed!")
        
        # Access the error message
        error_message = result.content[0].text
        logger.error("Error: %s", error_message)

if __name__ == "__main__":
    asyncio.run(main())