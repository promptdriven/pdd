import asyncio
import logging
import mcp.types as types
from typing import Dict, Any

# Import handler functions and utilities
from pdd_mcp_server.tools.handlers import (
    handle_pdd_generate,
    handle_pdd_test,
    handle_pdd_fix,
    get_handler
)

# Set up logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("pdd_handlers_demo")

async def demonstrate_handlers():
    """Demonstrate using different PDD handlers."""
    
    # Example 1: Using handle_pdd_generate directly
    logger.info("=== Example 1: Using handle_pdd_generate ===")
    generate_args = {
        "prompt_file": "my_prompt.pdd",
        "output": "generated_code.py",
        "strength": 0.8,
        "temperature": 0.2,
        "local": True,
        "verbose": True
    }
    
    result = await handle_pdd_generate(generate_args)
    process_result(result, "generate")
    
    # Example 2: Using handle_pdd_test
    logger.info("\n=== Example 2: Using handle_pdd_test ===")
    test_args = {
        "prompt_file": "api_prompt.pdd",
        "code_file": "api.py",
        "output": "test_api.py",
        "language": "python",
        "coverage_report": "coverage.xml",
        "existing_tests": "existing_tests.py",
        "target_coverage": 90,
        "merge": True
    }
    
    result = await handle_pdd_test(test_args)
    process_result(result, "test")
    
    # Example 3: Using handle_pdd_fix
    logger.info("\n=== Example 3: Using handle_pdd_fix ===")
    fix_args = {
        "prompt_file": "api_prompt.pdd",
        "code_file": "buggy_api.py",
        "unit_test_file": "test_api.py",
        "error_file": "error_output.log",
        "output_code": "fixed_api.py",
        "output_test": "updated_tests.py",
        "loop": True,
        "max_attempts": 3
    }
    
    result = await handle_pdd_fix(fix_args)
    process_result(result, "fix")
    
    # Example 4: Using the get_handler function
    logger.info("\n=== Example 4: Using get_handler to find and call a handler dynamically ===")
    tool_name = "pdd-preprocess"
    handler = get_handler(tool_name)
    
    preprocess_args = {
        "prompt_file": "complex_prompt.pdd",
        "output": "processed_prompt.pdd",
        "recursive": True,
        "exclude": ["excluded_file1.txt", "excluded_file2.txt"]
    }
    
    result = await handler(preprocess_args)
    process_result(result, "preprocess")
    
    # Example 5: List all available handlers
    logger.info("\n=== Example 5: Available PDD command handlers ===")
    handler_names = [
        "pdd-generate",
        "pdd-example",
        "pdd-test",
        "pdd-preprocess",
        "pdd-fix",
        "pdd-split",
        "pdd-change",
        "pdd-update",
        "pdd-detect",
        "pdd-conflicts",
        "pdd-crash",
        "pdd-trace",
        "pdd-bug",
        "pdd-auto-deps"
    ]
    for tool_name in handler_names:
        logger.info(f"  - {tool_name}")

def process_result(result: types.CallToolResult, command: str):
    """Process and display the result from a handler call."""
    if result.isError:
        logger.error(f"PDD {command} command failed:")
        logger.error(result.content[0].text)
    else:
        logger.info(f"PDD {command} command succeeded:")
        # Show first 200 chars of output for brevity
        output = result.content[0].text[:200]
        if len(result.content[0].text) > 200:
            output += "..."
        logger.info(output)

if __name__ == "__main__":
    asyncio.run(demonstrate_handlers())