# pdd_completion.fish - Fish shell completion for PDD CLI

# Global options
complete -c pdd -n "__fish_use_subcommand" -l force -d "Overwrite existing files without confirmation"
complete -c pdd -n "__fish_use_subcommand" -l strength -x -d "Set AI model strength (0.0 to 1.0)"
complete -c pdd -n "__fish_use_subcommand" -l temperature -x -d "Set AI model temperature"
complete -c pdd -n "__fish_use_subcommand" -l verbose -d "Increase output verbosity"
complete -c pdd -n "__fish_use_subcommand" -l quiet -d "Decrease output verbosity"
complete -c pdd -n "__fish_use_subcommand" -l output-cost -r -d "Enable cost tracking and output CSV file"
complete -c pdd -n "__fish_use_subcommand" -l review-examples -d "Review few-shot examples before execution"
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
complete -c pdd -n "__fish_use_subcommand" -a auto-deps -d "Analyze and insert dependencies"

# Command-specific completions
complete -c pdd -n "__fish_seen_subcommand_from generate" -l output -r -d "Output location for generated code"
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

# File completion for all commands
complete -c pdd -n "__fish_seen_subcommand_from generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps" -a "(__fish_complete_suffix .prompt)"
complete -c pdd -n "__fish_seen_subcommand_from generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps" -a "(__fish_complete_suffix .py .js .java .cpp .rb .go)"
complete -c pdd -n "__fish_seen_subcommand_from generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps" -a "(__fish_complete_suffix .log .txt .csv)"

# Help completion
complete -c pdd -n "__fish_seen_subcommand_from help" -a "generate example test preprocess fix split change update detect conflicts crash trace bug auto-deps" -d "Show help for specific command"