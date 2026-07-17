<!-- pdd-story-prompts: prompts/agentic_fix_python.prompt, prompts/agentic_langtest_python.prompt, prompts/fix_error_loop_python.prompt, prompts/get_run_command_python.prompt, prompts/get_test_command_python.prompt -->
<!-- pdd-story-dev-units: agentic_fix_python.prompt, agentic_langtest_python.prompt, fix_error_loop_python.prompt, get_run_command_python.prompt, get_test_command_python.prompt -->

# User Story: Nested TypeScript tests use the correct runner safely

## Story

As a developer working in a nested JavaScript workspace, I want PDD to run my test with the runner and project that own it, so that verification executes the intended test safely. Package scripts may contain quoted or escaped shell-operator text; those literals must not hide a later real test-runner invocation.
