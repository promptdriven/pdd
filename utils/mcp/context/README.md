# PDD MCP Server Tools

This directory contains example scripts and tools for interacting with the PDD CLI through MCP.

## Setup

1. Make sure you have the PDD CLI installed and accessible in your PATH.
2. Ensure your `.env` file contains the necessary API keys if you plan to use local mode.

## Test Files

The handlers example uses several test files located in the `/output` directory. These files are automatically regenerated when you run the handler examples if any required files are missing.

### Regenerating Test Files

The test files are regenerated automatically when running the handlers_example.py script if any files are missing. However, if you want to manually regenerate them, you can run:

```bash
python /Users/gregtanaka/pdd/mcp/context/regenerate_test_files.py
```

This will create all the necessary files for the handler examples to work properly.

### Available Test Files

The script generates the following files:

- `my_prompt.prompt`: A simple prompt for a factorial function (used by generate command)
- `api_prompt.prompt`: A prompt for a weather API (used by test and fix commands)
- `api.py`: A working implementation of the weather API
- `buggy_api.py`: A buggy version of the API with intentional errors
- `existing_tests.py`: Basic tests for the API
- `test_weather_api.py`: More comprehensive tests that will fail when run against the buggy API
- `error_output.log`: Error logs from running the tests against the buggy API
- `verify_weather_api.py`: A verification program for the fix command
- `coverage.xml`: A sample coverage report
- `complex_prompt.prompt`: A complex prompt with include directives
- `security_requirements.txt`: Security requirements for inclusion
- `ui_guidelines.txt`: UI guidelines for inclusion

## Using the Handlers Example

The `handlers_example.py` file demonstrates how to use the various PDD CLI commands through MCP. 

To run the example:

```bash
python /Users/gregtanaka/pdd/mcp/context/handlers_example.py
```

The example demonstrates:

1. Generate command: Creates a factorial function from a prompt
2. Test command: Generates tests for a weather API
3. Fix command: Fixes bugs in a buggy weather API
4. Preprocess command: Processes a complex prompt with include directives

### Troubleshooting

If you encounter timeouts:
- The `run_pdd_command` function in `runner.py` has a timeout parameter (default is 900 seconds)
- You can increase this value if needed
- Consider reducing the strength and complexity of the prompts for faster processing

If you're having API key issues:
- Make sure your `.env` file contains the proper API keys
- The `.env` file should be located at the root of the project

## Advanced Configuration

You can modify the `handlers_example.py` file to explore other PDD commands:

- Change the strength and temperature parameters to see different results
- Experiment with different prompts and file paths
- Try different command combinations

For more information about available PDD commands and options, see the README.md at the root of the project. 