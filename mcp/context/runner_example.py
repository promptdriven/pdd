import asyncio
import logging
from pdd_mcp_server.tools.runner import run_pdd_command, PddResult

# Configure logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("pdd_example")

async def main():
    """Asynchronous main function demonstrating PDD CLI command usage."""
    # Example 1: Basic usage - run a simple command
    result = await run_pdd_command(['pdd', 'version'])
    # Handle the result
    if result.success:
        logger.info(f"PDD version command succeeded with output:\n{result.stdout}")
    else:
        logger.error(f"PDD version command failed: {result.stderr}")
    
    # Example 2: Run a command with arguments
    result = await run_pdd_command(['pdd', 'generate', '--project-path', './my_project', 
                                   '--output-dir', './output'])
    # Check the result
    if result.success:
        logger.info("Generation completed successfully")
        logger.info(f"Output: {result.stdout}")
    else:
        logger.error(f"Generation failed with exit code {result.exit_code}")
        logger.error(f"Error message: {result.stderr}")
    
    # Example 3: Run a command with a custom timeout (30 seconds)
    try:
        result = await run_pdd_command(['pdd', 'complex-operation', '--large-dataset'], 
                                      timeout=30)
        if result.success:
            logger.info("Complex operation completed successfully")
        else:
            logger.warning(f"Complex operation failed or timed out: {result.stderr}")
            logger.warning(f"Exit code: {result.exit_code}")
    except FileNotFoundError:
        logger.critical("PDD executable not found in PATH. Please install PDD CLI.")
    
    # Example 4: How to access all results
    result = await run_pdd_command(['pdd', 'analyze', '--project', './source'])
    print(f"Command successful: {result.success}")
    print(f"Exit code: {result.exit_code}")
    print(f"Standard output:\n{result.stdout}")
    print(f"Standard error:\n{result.stderr}")

if __name__ == "__main__":
    asyncio.run(main())