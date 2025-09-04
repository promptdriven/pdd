# To run this example:
# From project root: python examples/utils_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import sys
import asyncio
import os
import shutil
import time
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Import the necessary components from the edit_file_tool.utils module
from edit_file_tool.utils import (
    # Type Aliases and Constants
    ModelName,
    CacheStatus,
    # Exception Classes
    EditToolError,
    FileOperationError,
    ValidationError,
    APIError,
    # Logging Infrastructure
    setup_logger,
    get_logger,
    sanitize_for_logging,
    # Performance Decorators
    retry,
    timed,
    # Validation Utilities
    validate_file_path,
    check_model_compatibility,
    sanitize_input,
    # Cost Management
    calculate_cost,
    calculate_cost_breakdown,
    format_cost,
    # Cache Strategy
    should_use_cache,
    # System Integration and Formatting
    check_system_compatibility,
    format_metrics,
)

# Setup a logger for this example script
# This demonstrates the first step in using the logging infrastructure.
log = setup_logger(
    "utils_example",
    level='DEBUG', # Use DEBUG to see output from @timed decorator
    log_file="examples/utils_example.log"
)

# --- Helper functions for demonstration ---

# This counter will be used by the mock API call to simulate failures.
# We use a list to make it mutable across function calls.
api_call_attempts = [0]

@retry(max_attempts=3, backoff_factor=0.1, exceptions=(APIError,))
@timed(logger=log)
async def mock_flaky_api_call(fail_for: int) -> dict:
    """
    A mock async function that simulates a network call that might fail.
    It is decorated with @retry and @timed to demonstrate their usage.

    Args:
        fail_for (int): The number of times the function should fail before succeeding.

    Returns:
        dict: A success message once the call succeeds.

    Raises:
        APIError: A simulated API error during failure attempts.
    """
    log.info(f"Attempting mock API call (will fail {fail_for} time(s))...")
    if api_call_attempts[0] < fail_for:
        api_call_attempts[0] += 1
        raise APIError(f"Simulated API failure #{api_call_attempts[0]}")

    log.info("Mock API call successful.")
    return {"status": "success", "data": "some_payload"}


async def demonstrate_utils_module():
    """
    Main function to demonstrate the features of the utils.py module.
    """
    print("=====================================================")
    print("=      Demonstrating edit_file_tool/utils.py      =")
    print("=====================================================")
    print("Log output is being written to examples/utils_example.log\n")

    # --- 1. Logging Demonstration ---
    print("--- 1. Logging & Sanitization ---")
    log.info("This is a standard informational log message.")
    sensitive_data = {
        "user": "test_user",
        "claude_api_key": "sk-ant-xxxxxxxxxxxxxxxxxxxxxxxxxx",
        "session_token": "secret-token-value-12345",
        "details": ["some", "safe", "data"]
    }
    log.warning(
        "Attempting to log sensitive data. It should be sanitized.",
        extra={"data": sanitize_for_logging(sensitive_data)}
    )
    print("Check the console or log file for a sanitized log message.")
    print("Sanitized data for display:", sanitize_for_logging(sensitive_data))

    # --- 2. Validation & Exception Handling ---
    print("\n--- 2. Validation & Exception Handling ---")
    temp_dir = Path("examples/temp_utils_demo")
    try:
        temp_dir.mkdir(exist_ok=True)
        print(f"Created temporary directory: {temp_dir}")

        # a) Successful path validation
        valid_path = temp_dir / "new_file.txt"
        print(f"Validating a safe path for creation: {valid_path}")
        resolved_path = validate_file_path(valid_path, must_exist=False, base_dir=temp_dir)
        print(f"Validation successful. Resolved path: {resolved_path}")

        # b) Handling ValidationError (Directory Traversal)
        malicious_path = "../../../etc/passwd"
        print(f"\nAttempting to validate a malicious path: {malicious_path}")
        try:
            validate_file_path(malicious_path, base_dir=temp_dir)
        except ValidationError as e:
            print(f"SUCCESSFULLY CAUGHT EXPECTED ERROR: {type(e).__name__}")
            print(f"Message: {e.message}")
            log.info(f"Correctly caught expected validation error: {e}")

        # c) Handling FileOperationError (File Not Found)
        non_existent_path = temp_dir / "i_do_not_exist.txt"
        print(f"\nAttempting to validate a non-existent file with must_exist=True: {non_existent_path}")
        try:
            validate_file_path(non_existent_path, must_exist=True, base_dir=temp_dir)
        except FileOperationError as e:
            print(f"SUCCESSFULLY CAUGHT EXPECTED ERROR: {type(e).__name__}")
            print(f"Message: {e.message}")
            log.info(f"Correctly caught expected file operation error: {e}")

        # d) Input Sanitization
        dirty_input = "This is a valid string with a null byte \x00 and a long line of text that will be truncated." * 10
        print("\nSanitizing a long string with control characters...")
        clean_input = sanitize_input(dirty_input, max_length=100)
        print(f"Original length: {len(dirty_input)}, Sanitized length: {len(clean_input)}")
        print(f"Sanitized output: {clean_input}")

    finally:
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
            print(f"\nCleaned up temporary directory: {temp_dir}")

    # --- 3. Cost & Model Management ---
    print("\n--- 3. Cost & Model Management ---")
    model: ModelName = "claude-3-5-sonnet-20240620"
    feature = "text_editor_20250124"
    print(f"Checking if model '{model}' supports feature '{feature}'...")
    is_compatible = check_model_compatibility(model, feature)
    print(f"Result: {is_compatible} (Sonnet 3.5 supports the newer tool version)")

    print("\nCalculating cost for a standard API call...")
    cost = calculate_cost(
        model=model,
        input_tokens=50000,
        output_tokens=10000,
        cache_status="none"
    )
    print(f"Standard call cost: {format_cost(cost)}")

    print("\nCalculating detailed cost breakdown for a cache-read call...")
    breakdown = calculate_cost_breakdown(
        model=model,
        input_tokens=150000, # Larger input, benefits from cache
        output_tokens=5000,
        cache_status="read" # Cheaper input tokens
    )
    print("Cost Breakdown:")
    for key, value in breakdown.items():
        if "cost" in key:
            print(f"  {key}: {format_cost(value)}")
        else:
            print(f"  {key}: {value}")

    # --- 4. Cache Strategy ---
    print("\n--- 4. Cache Strategy ---")
    # a) Small file, should not cache
    small_content = "This is a small file.\nIt has very little content."
    print(f"\nAnalyzing small file ({len(small_content)} bytes)...")
    use_cache_small = should_use_cache("small.txt", small_content)
    print(f"Recommendation for small file: {'Use Cache' if use_cache_small else 'Do Not Cache'}")

    # b) Large file, should always cache
    large_content = "#" * 8192 # 8KB
    print(f"\nAnalyzing large file ({len(large_content)} bytes)...")
    use_cache_large = should_use_cache("large.txt", large_content)
    print(f"Recommendation for large file: {'Use Cache' if use_cache_large else 'Do Not Cache'}")

    # c) Medium file, depends on complexity
    medium_content_simple = "line\n" * 150 # 2100 bytes, but low complexity
    medium_content_complex = ("import os;\nclass MyComplexClass:\n    def __init__(self, name):\n        self.name = name\n" * 20) # ~2KB, but higher complexity
    print(f"\nAnalyzing medium-sized simple file ({len(medium_content_simple)} bytes)...")
    use_cache_medium_simple = should_use_cache("medium_simple.py", medium_content_simple)
    print(f"Recommendation for medium simple file: {'Use Cache' if use_cache_medium_simple else 'Do Not Cache'}")

    print(f"\nAnalyzing medium-sized complex file ({len(medium_content_complex)} bytes)...")
    use_cache_medium_complex = should_use_cache("medium_complex.py", medium_content_complex)
    print(f"Recommendation for medium complex file: {'Use Cache' if use_cache_medium_complex else 'Do Not Cache'}")


    # --- 5. Performance Decorators ---
    print("\n--- 5. Performance Decorators (@retry and @timed) ---")
    print("Calling a function that will fail twice before succeeding...")
    try:
        result = await mock_flaky_api_call(fail_for=2)
        print(f"Function succeeded after retries. Result: {result}")
        print("Check the log file for timing and retry warning messages.")
    except APIError as e:
        print(f"Function failed permanently: {e}")
        log.error(f"The mock API call failed after all retries: {e}")

    # --- 6. System Integration ---
    print("\n--- 6. System Integration ---")
    print("Checking system compatibility...")
    compatibility = check_system_compatibility()
    print(f"Python Version OK: {compatibility['python_version_ok']} ({compatibility['python_version']})")
    print(f"Platform: {compatibility['platform']}")

    print("\nFormatting a sample metrics dictionary...")
    sample_metrics = {
        "total_cost": 0.123456,
        "tokens_processed": 125000,
        "api_latency_avg": 1.23456,
        "cache_hit_rate": 0.75
    }
    formatted_metrics = format_metrics(sample_metrics)
    print(formatted_metrics)

    print("\n=====================================================")
    print("=              Demonstration Complete             =")
    print("=====================================================")


if __name__ == "__main__":
    try:
        asyncio.run(demonstrate_utils_module())
    except Exception as e:
        log.critical(f"An unexpected error occurred during the demonstration: {e}")
        print(f"An unexpected error occurred: {e}")
