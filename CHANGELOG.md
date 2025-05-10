## v0.0.28 (2025-05-10)

### Fix

- update string handling and improve test assertions in CLI

## v0.0.27 (2025-05-10)

### Feat

- add output paths for fixed code and program in verification process
- add output program option to verify command and enhance documentation

### Fix

- correct newline character in program file and enhance test assertions

### Refactor

- enhance logging configuration in llm_invoke_python.prompt
- update logging configuration and example usage in llm_invoke.py
- enhance logging and remove print statements in llm_invoke.py

## v0.0.26 (2025-05-09)

### Fix

- update environment variable for Firebase API key and enhance VSCode launch configuration

## v0.0.25 (2025-04-28)

## v0.0.24 (2025-04-17)

### Feat

- update model configurations and enhance prompt documentation
- enhance verification error handling and output reporting
- implement iterative error fixing loop for code verification
- restructure MCP server and enhance documentation
- introduce `verify` command for functional correctness validation
- enhance pdd-fix functionality with loop mode support
- add fix_verification_errors functionality and example script
- add new guidelines for project standards and best practices
- expand README and server initialization with PDD workflows and concepts
- improve output path handling in bug_main and generate_output_paths
- update handle_pdd_bug function to include additional required parameters
- enhance prompt splitting functionality and update documentation
- enhance JSON kwargs handling in main.py and update tool definitions
- update tool definitions in definitions.py for improved clarity and parameter requirements
- enhance README and definitions with usage guidance for PDD commands
- enhance tool definitions and command handling in PDD MCP server
- update tool definitions to enforce 'force' parameter for file overwrites
- enhance PDD MCP server with improved parameter handling and new test tool
- enhance PDD MCP server with logging improvements and parameter validation
- add initial PDD MCP server structure and tool imports
- enhance PDD MCP server with command-line argument parsing and FastMCP integration
- enhance PDD MCP server functionality and add new tools
- update server example and core server functionality
- enhance PDD command execution and API key management
- add script to regenerate test files for weather API
- enhance handler examples with file existence checks and improved argument handling
- enhance PDD MCP handlers with multiple command implementations
- implement main server functionality and example client for PDD MCP
- add example handler for PDD code generation
- implement core MCP server functionality and tool definitions
- add README.md and prompt file for MCP server implementation
- add PDD theme prompt file for .prompt extension
- update Makefile and enhance VS Code extension for PDD
- add initial VS Code extension for Prompt Driven Development
- enhance ZSH completion script for PDD CLI
- add release target to Makefile for version bump and package upload

### Fix

- update llm_model.csv and regression_analysis_log.prompt for accuracy

### Refactor

- enhance fix_verification_errors functionality and output structure
- remove unused PDD tools and their handlers from definitions and handlers
- simplify parameter guidance in definitions.py
- remove PDD_TEST_TOOL and its handler from PDD MCP server
- update handler examples and result formatting in PDD MCP
- clean up prompt files by removing example references

## v0.0.23 (2025-04-06)

### Feat

- replace 'quiet' parameter with 'verbose' in crash_main for detailed logging
- update main function parameters and enable verbose logging
- add verbose mode to fix_code_loop and related functions for detailed logging
- add verbose mode to fix_error_loop function and update parameters
- implement code generation CLI with prompt file handling and output options
- add clean target to Makefile for removing generated files and update documentation
- add validation for input requirements in update_main function all 5 tests pass
- add verbose option to git_update function and update documentation
- implement CLI for generating and enhancing unit tests with cmd_test_main untested
- add cmd_test_main prompt file for generating unit tests via CLI
- add fix_command for automated error correction in code and unit tests

### Fix

- update command references in cli_python.prompt for code generation
- update prompt file names in tests for consistency 18 of 20 pass

### Refactor

- update output paths for prompt and generated code files
- streamline unit test generation and coverage enhancement processes working
- update file path handling in fix_error_loop and enhance prompt documentation
- update input_strings documentation and loading logic for error files
