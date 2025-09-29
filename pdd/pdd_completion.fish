# pdd_completion.fish - Fish shell completion for PDD CLI

# Global options
complete -c pdd -n "__fish_use_subcommand" -l force -d "Overwrite existing files without confirmation"
complete -c pdd -n "__fish_use_subcommand" -l strength -x -d "Set AI model strength (0.0 to 1.0)"
complete -c pdd -n "__fish_use_subcommand" -l time -x -d "Set AI model reasoning time (0.0 to 1.0)"
complete -c pdd -n "__fish_use_subcommand" -l temperature -x -d "Set AI model temperature"
complete -c pdd -n "__fish_use_subcommand" -l verbose -d "Increase output verbosity"
complete -c pdd -n "__fish_use_subcommand" -l quiet -d "Decrease output verbosity"
complete -c pdd -n "__fish_use_subcommand" -l output-cost -r -d "Enable cost tracking and output CSV file"
complete -c pdd -n "__fish_use_subcommand" -l review-examples -d "Review few-shot examples before execution"
complete -c pdd -n "__fish_use_subcommand" -l local -d "Run commands locally"
complete -c pdd -n "__fish_use_subcommand" -l context -r -d "Override .pddrc context"
complete -c pdd -n "__fish_use_subcommand" -l list-contexts -d ".pddrc contexts and exit"
complete -c pdd -n "__fish_use_subcommand" -l help -d "Show help message"
complete -c pdd -n "__fish_use_subcommand" -l version -d "Show version information"

# Commands
complete -c pdd -n "__fish_use_subcommand" -a generate -d "Generate code from prompt file"
complete -c pdd -n "__fish_use_subcommand" -a example -d "Create example from prompt and code"
complete -c pdd -n "__fish_use_subcommand" -a test -d "Generate or enhance unit tests"
complete -c pdd -n "__fish_use_subcommand" -a preprocess -d "Preprocess prompt files"
complete -c pdd -n "__fish_use_subcommand" -a fix -d "Fix errors in code and tests"
complete -c pdd -n "__fish_use_subcommand" -a split -d "Split large prompt files"
complete -c pdd -n "__fish_use_subcommand" -a change -d "Modify prompt based on change prompt"
complete -c pdd -n "__fish_use_subcommand" -a update -d "Update prompt based on modified code"
complete -c pdd -n "__fish_use_subcommand" -a detect -d "Detect prompts needing changes"
complete -c pdd -n "__fish_use_subcommand" -a conflicts -d "Analyze conflicts between prompts"
complete -c pdd -n "__fish_use_subcommand" -a crash -d "Fix code causing program crash"
complete -c pdd -n "__fish_use_subcommand" -a trace -d "Trace code line to prompt"
complete -c pdd -n "__fish_use_subcommand" -a bug -d "Generate unit test from bug report"
complete -c pdd -n "__fish_use_subcommand" -a auto-deps -d "Analyze and insert dependencies from directory or glob"
complete -c pdd -n "__fish_use_subcommand" -a verify -d "Verify functional correctness using LLM judgment"
complete -c pdd -n "__fish_use_subcommand" -a sync -d "Synchronize prompt, code, examples, tests"
complete -c pdd -n "__fish_use_subcommand" -a setup -d "Interactive setup and completion install"
complete -c pdd -n "__fish_use_subcommand" -a install_completion -d "Install shell completion"
complete -c pdd -n "__fish_use_subcommand" -a pytest-output -d "Run pytest and capture structured output"

# Command-specific completions
complete -c pdd -n "__fish_seen_subcommand_from generate" -l output -r -d "Output location for generated code"
complete -c pdd -n "__fish_seen_subcommand_from generate" -l original-prompt -r -d "Original prompt file for incremental generation"
complete -c pdd -n "__fish_seen_subcommand_from generate" -l incremental -d "Force incremental patching"
complete -c pdd -n "__fish_seen_subcommand_from generate" -s e -l env -xa "(env | cut -d= -f1 | sed 's/.*/&=/' | sort -u)" -d "Set template variable (KEY=VALUE) or read KEY from env"
complete -c pdd -n "__fish_seen_subcommand_from generate" -a "(__fish_complete_suffix .prompt)"

complete -c pdd -n "__fish_seen_subcommand_from example" -l output -r -d "Output location for example code"
complete -c pdd -n "__fish_seen_subcommand_from example" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from example" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)"

complete -c pdd -n "__fish_seen_subcommand_from test" -l output -r -d "Output location for test file"
complete -c pdd -n "__fish_seen_subcommand_from test" -l language -x -d "Specify programming language"
complete -c pdd -n "__fish_seen_subcommand_from test" -l coverage-report -r -d "Path to coverage report"
complete -c pdd -n "__fish_seen_subcommand_from test" -l existing-tests -r -d "Path to existing test file"
complete -c pdd -n "__fish_seen_subcommand_from test" -l target-coverage -x -d "Target coverage percentage"
complete -c pdd -n "__fish_seen_subcommand_from test" -l merge -d "Merge new tests with existing"
complete -c pdd -n "__fish_seen_subcommand_from test" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from test" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)"

complete -c pdd -n "__fish_seen_subcommand_from preprocess" -l output -r -d "Output location for preprocessed file"
complete -c pdd -n "__fish_seen_subcommand_from preprocess" -l xml -d "Insert XML delimiters"
complete -c pdd -n "__fish_seen_subcommand_from preprocess" -l recursive -d "Recursively preprocess"
complete -c pdd -n "__fish_seen_subcommand_from preprocess" -l double -d "Double curly brackets"
complete -c pdd -n "__fish_seen_subcommand_from preprocess" -l exclude -x -d "Keys to exclude from doubling"
complete -c pdd -n "__fish_seen_subcommand_from preprocess" -a "(__fish_complete_suffix .prompt)"

complete -c pdd -n "__fish_seen_subcommand_from fix" -l output-test -r -d "Output location for fixed test"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l output-code -r -d "Output location for fixed code"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l output-results -r -d "Output location for fix results"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l loop -d "Enable iterative fixing"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l verification-program -r -d "Verification program path"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l max-attempts -x -d "Maximum fix attempts"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l budget -x -d "Maximum budget for fixing"
complete -c pdd -n "__fish_seen_subcommand_from fix" -l auto-submit -d "Auto-submit if tests pass"
complete -c pdd -n "__fish_seen_subcommand_from fix" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from fix" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)"
complete -c pdd -n "__fish_seen_subcommand_from fix" -a "(__fish_complete_suffix .log)"

complete -c pdd -n "__fish_seen_subcommand_from split" -l output-sub -r -d "Output for sub-prompt file"
complete -c pdd -n "__fish_seen_subcommand_from split" -l output-modified -r -d "Output for modified prompt file"
complete -c pdd -n "__fish_seen_subcommand_from split" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from split" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)" # For INPUT_CODE and EXAMPLE_CODE

complete -c pdd -n "__fish_seen_subcommand_from change" -l output -r -d "Output location for modified prompt"
complete -c pdd -n "__fish_seen_subcommand_from change" -l csv -d "Use CSV for batch changes"
complete -c pdd -n "__fish_seen_subcommand_from change" -l budget -x -d "Maximum budget for change process"
complete -c pdd -n "__fish_seen_subcommand_from change" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from change" -a "(__fish_complete_suffix .csv)" # For the change prompt file if it's a CSV
complete -c pdd -n "__fish_seen_subcommand_from change" -a "(__fish_complete_path)" # For INPUT_CODE directory or file

complete -c pdd -n "__fish_seen_subcommand_from update" -l output -r -d "Output for updated prompt file"
complete -c pdd -n "__fish_seen_subcommand_from update" -l git -d "Use git history for original code"
complete -c pdd -n "__fish_seen_subcommand_from update" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from update" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)" # For MODIFIED_CODE_FILE and INPUT_CODE_FILE

complete -c pdd -n "__fish_seen_subcommand_from detect" -l output -r -d "Output CSV for analysis results"
complete -c pdd -n "__fish_seen_subcommand_from detect" -a "(__fish_complete_suffix .prompt)" # For PROMPT_FILES and CHANGE_FILE

complete -c pdd -n "__fish_seen_subcommand_from conflicts" -l output -r -d "Output CSV for conflict analysis"
complete -c pdd -n "__fish_seen_subcommand_from conflicts" -a "(__fish_complete_suffix .prompt)" # For PROMPT1 and PROMPT2

complete -c pdd -n "__fish_seen_subcommand_from crash" -l output -r -d "Output for fixed code file"
complete -c pdd -n "__fish_seen_subcommand_from crash" -l output-program -r -d "Output for fixed program file"
complete -c pdd -n "__fish_seen_subcommand_from crash" -l loop -d "Enable iterative fixing"
complete -c pdd -n "__fish_seen_subcommand_from crash" -l max-attempts -x -d "Maximum fix attempts"
complete -c pdd -n "__fish_seen_subcommand_from crash" -l budget -x -d "Maximum budget for fixing"
complete -c pdd -n "__fish_seen_subcommand_from crash" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from crash" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)" # For CODE_FILE and PROGRAM_FILE
complete -c pdd -n "__fish_seen_subcommand_from crash" -a "(__fish_complete_suffix .log .txt)" # For ERROR_FILE

complete -c pdd -n "__fish_seen_subcommand_from trace" -l output -r -d "Output for trace analysis results"
complete -c pdd -n "__fish_seen_subcommand_from trace" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from trace" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)" # For CODE_FILE
# No specific completion for CODE_LINE, it's a number

complete -c pdd -n "__fish_seen_subcommand_from bug" -l output -r -d "Output for generated unit test"
complete -c pdd -n "__fish_seen_subcommand_from bug" -l language -x -d "Programming language for unit test"
complete -c pdd -n "__fish_seen_subcommand_from bug" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from bug" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)" # For CODE_FILE and PROGRAM_FILE
complete -c pdd -n "__fish_seen_subcommand_from bug" -a "(__fish_complete_suffix .txt .log)" # For CURRENT_OUTPUT_FILE and DESIRED_OUTPUT_FILE

complete -c pdd -n "__fish_seen_subcommand_from auto-deps" -l output -r -d "Output for modified prompt file"
complete -c pdd -n "__fish_seen_subcommand_from auto-deps" -l csv -r -d "CSV file for dependency info"
complete -c pdd -n "__fish_seen_subcommand_from auto-deps" -l force-scan -d "Force rescanning dependencies"
complete -c pdd -n "__fish_seen_subcommand_from auto-deps" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from auto-deps" -a "(__fish_complete_path)" # For DIRECTORY_PATH

complete -c pdd -n "__fish_seen_subcommand_from verify" -l output-results -r -d "Output for verification results log"
complete -c pdd -n "__fish_seen_subcommand_from verify" -l output-code -r -d "Output for verified code file"
complete -c pdd -n "__fish_seen_subcommand_from verify" -l output-program -r -d "Output for verified program file"
complete -c pdd -n "__fish_seen_subcommand_from verify" -l max-attempts -x -d "Max fix attempts in verification loop"
complete -c pdd -n "__fish_seen_subcommand_from verify" -l budget -x -d "Max budget for verification and fixing"
complete -c pdd -n "__fish_seen_subcommand_from verify" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from verify" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)" # For CODE_FILE and PROGRAM_FILE

# sync command
complete -c pdd -n "__fish_seen_subcommand_from sync" -l max-attempts -x -d "Max attempts for loops"
complete -c pdd -n "__fish_seen_subcommand_from sync" -l budget -x -d "Total budget for sync"
complete -c pdd -n "__fish_seen_subcommand_from sync" -l skip-verify -d "Skip functional verification"
complete -c pdd -n "__fish_seen_subcommand_from sync" -l skip-tests -d "Skip unit test generation"
complete -c pdd -n "__fish_seen_subcommand_from sync" -l target-coverage -x -d "Desired coverage percentage"
complete -c pdd -n "__fish_seen_subcommand_from sync" -l log -d "Show analysis instead of running"

# setup and install_completion have no options
complete -c pdd -n "__fish_seen_subcommand_from setup" -d "Run interactive setup"
complete -c pdd -n "__fish_seen_subcommand_from install_completion" -d "Install shell completion"

# pytest-output command
complete -c pdd -n "__fish_seen_subcommand_from pytest-output" -l json-only -d "Print only JSON"
complete -c pdd -n "__fish_seen_subcommand_from pytest-output" -a "(__fish_complete_suffix .py)"

# File completion for all commands
complete -c pdd -n "__fish_seen_subcommand_from generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps verify" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps verify" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)"
complete -c pdd -n "__fish_seen_subcommand_from generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps verify" -a "(__fish_complete_suffix .log .txt .csv)"

# Help completion
complete -c pdd -n "__fish_seen_subcommand_from help" -a "generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps verify sync setup install_completion pytest-output" -d "Show help for specific command"
