import asyncio
import logging
import os
from pdd_mcp_server.tools.runner import run_pdd_command, PddResult

# Configure logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("pdd_example")

# Define the output directory path
# The output directory is at the root level
OUTPUT_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'output')

async def main():
    """Asynchronous main function demonstrating PDD CLI command usage."""
    # Example 1: Basic usage - run a simple command to check version
    result = await run_pdd_command(['pdd', '--version'])
    # Handle the result
    if result.success:
        logger.info(f"PDD version command succeeded with output:\n{result.stdout}")
    else:
        logger.error(f"PDD version command failed: {result.stderr}")
    
    # Example 2: Run a generate command with proper arguments
    my_prompt_path = os.path.join(OUTPUT_DIR, 'my_prompt.prompt')
    output_path = os.path.join(OUTPUT_DIR, 'generated_api.py')
    result = await run_pdd_command(['pdd',  '--force', 'generate', '--output', output_path, 
                                  my_prompt_path])
    # Check the result
    if result.success:
        logger.info("Generation completed successfully")
        logger.info(f"Output: {result.stdout}")
    else:
        logger.error(f"Generation failed with exit code {result.exit_code}")
        logger.error(f"Error message: {result.stderr}")
    
    # Example 3: Run a test command with a custom timeout (30 seconds)
    try:
        api_prompt_path = os.path.join(OUTPUT_DIR, 'api_prompt.prompt')
        api_path = os.path.join(OUTPUT_DIR, 'api.py')
        test_output_path = os.path.join(OUTPUT_DIR, 'test_generated_api.py')
        result = await run_pdd_command(['pdd', '--force', 'test', '--output', test_output_path,
                                      api_prompt_path, api_path], 
                                      timeout=30)
        if result.success:
            logger.info("Test generation completed successfully")
        else:
            logger.warning(f"Test generation failed or timed out: {result.stderr}")
            logger.warning(f"Exit code: {result.exit_code}")
    except FileNotFoundError:
        logger.critical("PDD executable not found in PATH. Please install PDD CLI.")
    
    # Example 4: Run a fix command with loop option
    buggy_api_path = os.path.join(OUTPUT_DIR, 'buggy_api.py')
    test_weather_api_path = os.path.join(OUTPUT_DIR, 'test_weather_api.py')
    error_output_path = os.path.join(OUTPUT_DIR, 'error_output.log')
    test_fixed_output_path = os.path.join(OUTPUT_DIR, 'test_fixed_api.py')
    fixed_api_output_path = os.path.join(OUTPUT_DIR, 'fixed_api.py')
    result = await run_pdd_command(['pdd',  '--force', 'fix', '--output-test', test_fixed_output_path,
                                  '--output-code', fixed_api_output_path,
                                  api_prompt_path, buggy_api_path,
                                  test_weather_api_path, error_output_path])
    print(f"Command successful: {result.success}")
    print(f"Exit code: {result.exit_code}")
    print(f"Standard output:\n{result.stdout}")
    print(f"Standard error:\n{result.stderr}")

if __name__ == "__main__":
    asyncio.run(main())