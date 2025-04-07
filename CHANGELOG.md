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
