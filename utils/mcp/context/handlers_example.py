import asyncio
import logging
import mcp.types as types
from typing import Dict, Any
import os
import sys
import subprocess
import importlib.util

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

# Path to the output directory
OUTPUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'output')

def ensure_test_files_exist():
    """
    Check if required test files exist, and regenerate them if needed.
    """
    # List of required test files
    required_files = [
        "my_prompt.prompt",
        "api_prompt.prompt",
        "api.py",
        "buggy_api.py",
        "existing_tests.py",
        "test_weather_api.py",
        "error_output.log",
        "coverage.xml",
        "complex_prompt.prompt"
    ]
    
    # Check if all required files exist
    all_files_exist = True
    for file in required_files:
        if not os.path.exists(os.path.join(OUTPUT_DIR, file)):
            logger.warning(f"Required file {file} is missing")
            all_files_exist = False
            break
    
    # If any files are missing, run the regenerate script
    if not all_files_exist:
        logger.info("Some required test files are missing. Running regenerate_test_files.py...")
        
        # Path to the regenerate script
        regenerate_script = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'regenerate_test_files.py')
        
        # Check if the script exists
        if not os.path.exists(regenerate_script):
            logger.error(f"Regenerate script not found at {regenerate_script}")
            sys.exit(1)
            
        try:
            # Method 1: Run the script as a module
            spec = importlib.util.spec_from_file_location("regenerate_module", regenerate_script)
            if spec and spec.loader:
                regenerate_module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(regenerate_module)
                if hasattr(regenerate_module, 'main'):
                    regenerate_module.main()
                    logger.info("Test files regenerated successfully using module import")
                else:
                    logger.warning("No main function found in regenerate script, falling back to subprocess")
                    # Method 2: Run the script as a subprocess
                    subprocess.run([sys.executable, regenerate_script], check=True)
                    logger.info("Test files regenerated successfully using subprocess")
            else:
                # Method 2: Run the script as a subprocess
                subprocess.run([sys.executable, regenerate_script], check=True)
                logger.info("Test files regenerated successfully using subprocess")
                
        except Exception as e:
            logger.error(f"Failed to regenerate test files: {e}")
            sys.exit(1)
    else:
        logger.info("All required test files exist")

async def demonstrate_handlers():
    """Demonstrate using different PDD handlers."""
    
    # Ensure test files exist before running examples
    ensure_test_files_exist()
    
    # Example 1: Using handle_pdd_generate directly
    logger.info("=== Example 1: Using handle_pdd_generate ===")
    generate_args = {
        "prompt_file": os.path.join(OUTPUT_DIR, "my_prompt.prompt"),
        "output": os.path.join(OUTPUT_DIR, "generated_code.py"),
        "strength": 0.3,  # Lower strength for faster processing
        "temperature": 0.0,  # Lower temperature for more deterministic results
        "local": True,  # Run locally instead of in the cloud
        "verbose": True,
        "force": True   # Force overwrite without prompting
    }
    
    result = await handle_pdd_generate(generate_args)
    process_result(result, "generate")
    
    # Example 2: Using handle_pdd_test
    logger.info("\n=== Example 2: Using handle_pdd_test ===")
    test_args = {
        "prompt_file": os.path.join(OUTPUT_DIR, "api_prompt.prompt"),
        "code_file": os.path.join(OUTPUT_DIR, "api.py"),
        "output": os.path.join(OUTPUT_DIR, "test_api.py"),
        "language": "python",
        "coverage_report": os.path.join(OUTPUT_DIR, "coverage.xml"),
        "existing_tests": os.path.join(OUTPUT_DIR, "existing_tests.py"),
        "target_coverage": 80,  # Lower target coverage for faster processing
        "merge": True,
        "local": True,  # Run locally instead of in the cloud
        "force": True   # Force overwrite without prompting
    }
    
    result = await handle_pdd_test(test_args)
    process_result(result, "test")
    
    # Example 3: Using handle_pdd_fix
    logger.info("\n=== Example 3: Using handle_pdd_fix ===")
    fix_args = {
        "prompt_file": os.path.join(OUTPUT_DIR, "api_prompt.prompt"),
        "code_file": os.path.join(OUTPUT_DIR, "buggy_api.py"),
        "unit_test_file": os.path.join(OUTPUT_DIR, "test_weather_api.py"),
        "error_file": os.path.join(OUTPUT_DIR, "error_output.log"),
        "output_code": os.path.join(OUTPUT_DIR, "fixed_api.py"),
        "output_test": os.path.join(OUTPUT_DIR, "updated_tests.py"),
        "local": True,  # Run locally instead of in the cloud
        "strength": 0.3,  # Lower strength for faster processing
        "max_attempts": 2,  # Reduce max attempts from 3 to 2
        "force": True   # Force overwrite without prompting
    }
    
    result = await handle_pdd_fix(fix_args)
    process_result(result, "fix")
    
    # Example 4: Using the get_handler function
    logger.info("\n=== Example 4: Using get_handler to find and call a handler dynamically ===")
    tool_name = "pdd-preprocess"
    handler = get_handler(tool_name)
    
    preprocess_args = {
        "prompt_file": os.path.join(OUTPUT_DIR, "complex_prompt.prompt"),
        "output": os.path.join(OUTPUT_DIR, "processed_prompt.prompt"),
        "local": True,  # Run locally instead of in the cloud
        "xml": True,   # Use XML mode which is faster than recursive mode
        "exclude": [
            "file1",
            "file2"
        ],
        "force": True   # Force overwrite without prompting
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