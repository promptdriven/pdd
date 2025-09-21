#compdef pdd

##
# ZSH Completion for PDD CLI (Prompt-Driven Development)
#
# Save this file as "pdd_completion.zsh" and source it from your ~/.zshrc:
#   source /path/to/pdd_completion.zsh
#
# The script will handle completion initialization automatically.
#
# After installation, typing:
#   pdd <Tab>
# will offer completions for subcommands and options as described in the PDD CLI README.
##

# First, make sure we're using zsh
if [ -z "$ZSH_VERSION" ]; then
   echo >&2 "pdd completion requires zsh."
   return 1
fi

# Add this directory to fpath so ZSH can find our completion function
script_dir=${0:A:h}
fpath=($script_dir $fpath)

# Check if we need to initialize completion system
# Use command -v to check if compdef function exists
if ! command -v compdef >/dev/null 2>&1; then
    autoload -U compinit
    compinit
fi

##
# ZSH Completion for PDD CLI (Prompt-Driven Development)
#
# Save this file as "pdd_completion.zsh" and source it from your ~/.zshrc:
#   autoload -U compinit && compinit
#   fpath=(/path/to/this/file $fpath)
#   source /path/to/pdd_completion.zsh
#
# Or place it in a standard completion directory recognized by ZSH.
#
# After installation, typing:
#   pdd <Tab>
# will offer completions for subcommands and options as described in the PDD CLI README.
##

# 1) Define global options for all commands.
local -a _pdd_global_opts
_pdd_global_opts=(
  '--force[Overwrite existing files without asking for confirmation.]'
  '--strength[Set the strength of the AI model (0.0 to 1.0, default: 0.5)]:strength:(0.0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 1.0)'
  '--time[Controls the reasoning allocation for LLM models (0.0 to 1.0, default: 0.25)]:time:(0.0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 1.0)'
  '--temperature[Set the temperature of the AI model (default: 0.0)]:temperature:(0.0 0.25 0.5 0.75 1.0)'
  '--verbose[Increase output verbosity for more detailed information.]'
  '--quiet[Decrease output verbosity (minimal information).]'
  '--output-cost[Enable cost tracking and output a CSV file with usage details.]:filename:_files'
  '--review-examples[Review and optionally exclude few-shot examples before command execution.]'
  '--local[Run commands locally instead of in the cloud.]'
  '--context[Override automatic .pddrc context]:context-name:_guard'
  '--list-contexts[List available .pddrc contexts and exit]'
  '--help[Show help message and exit.]'
  '--version[Show version and exit.]'
)

##
# Per-subcommand completion functions
##

# Helper: suggest environment variables (KEY and KEY=)
_pdd_env_vars() {
  local -a envs envs_eq
  envs=(${(f)"$(env | cut -d= -f1 | sort -u)"})
  envs_eq=(${envs/%/=})
  _describe -t envvars 'environment variables' envs_eq envs
}

# generate
# Usage: pdd [GLOBAL OPTIONS] generate [OPTIONS] PROMPT_FILE
# Options:
#   --output [LOCATION]
# Args:
#   1: PROMPT_FILE
_pdd_generate() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Specify where to save the generated code.]:filename:_files' \
    '--original-prompt=[The original prompt file used to generate existing code.]:filename:_files' \
    '--incremental[Force incremental patching even if changes are significant.]' \
    '(-e --env)'{-e,--env}'[Set template variable (KEY=VALUE) or read KEY from env]:template variable:_pdd_env_vars' \
    '1:prompt-file:_files' \
    '*:filename:_files'
}

# example
# Usage: pdd [GLOBAL OPTIONS] example [OPTIONS] PROMPT_FILE CODE_FILE
# Options:
#   --output [LOCATION]
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
_pdd_example() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Specify where to save the generated example code.]:filename:_files' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '*:filename:_files'
}

# test
# Usage: pdd [GLOBAL OPTIONS] test [OPTIONS] PROMPT_FILE CODE_FILE
# Options:
#   --output [LOCATION]
#   --language [LANGUAGE]
#   --coverage-report [PATH]
#   --existing-tests [PATH]
#   --target-coverage [FLOAT]
#   --merge
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
_pdd_test() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Specify where to save the generated test file.]:filename:_files' \
    '--language=[Specify the programming language.]:string:_guard' \
    '--coverage-report=[Path to a coverage report file.]:filename:_files' \
    '--existing-tests=[Path to existing test file.]:filename:_files' \
    '--target-coverage=[Desired code coverage percentage (default 90.0)]:float' \
    '--merge[Merge new tests with existing test file when using --existing-tests.]' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '*:filename:_files'
}

# preprocess
# Usage: pdd [GLOBAL OPTIONS] preprocess [OPTIONS] PROMPT_FILE
# Options:
#   --output [LOCATION]
#   --xml
#   --recursive
#   --double
#   --exclude
# Arg:
#   1: PROMPT_FILE
_pdd_preprocess() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the preprocessed prompt file.]:filename:_files' \
    '--xml[Insert XML delimiters instead of normal preprocessing.]' \
    '--recursive[Recursively preprocess all prompt files in the prompt file.]' \
    '--double[Double curly braces in prompt file(s).]' \
    '--exclude=[List of keys to exclude from curly bracket doubling.]:string:_guard' \
    '1:prompt-file:_files' \
    '*:filename:_files'
}

# fix
# Usage: pdd [GLOBAL OPTIONS] fix [OPTIONS] PROMPT_FILE CODE_FILE UNIT_TEST_FILE ERROR_FILE
# Options:
#   --output-test [LOCATION]
#   --output-code [LOCATION]
#   --output-results [LOCATION]
#   --loop
#   --verification-program [PATH]
#   --max-attempts [INT]
#   --budget [FLOAT]
#   --auto-submit
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
#   3: UNIT_TEST_FILE
#   4: ERROR_FILE
_pdd_fix() {
  _arguments -s \
    $_pdd_global_opts \
    '--output-test=[Where to save the fixed unit test file.]:filename:_files' \
    '--output-code=[Where to save the fixed code file.]:filename:_files' \
    '--output-results=[Where to save the fix results.]:filename:_files' \
    '--loop[Enable iterative fixing process.]' \
    '--verification-program=[Path to a Python program that verifies code.]:filename:_files' \
    '--max-attempts=[Maximum fix attempts (default 3)]:int' \
    '--budget=[Maximum cost allowed for fixes (default 5.0)]:float' \
    '--auto-submit[Automatically submit example if all tests pass in fix loop.]' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '3:unit-test-file:_files' \
    '4:error-file:_files' \
    '*:filename:_files'
}

# split
# Usage: pdd [GLOBAL OPTIONS] split [OPTIONS] INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
# Options:
#   --output-sub [LOCATION]
#   --output-modified [LOCATION]
# Args:
#   1: INPUT_PROMPT
#   2: INPUT_CODE
#   3: EXAMPLE_CODE
_pdd_split() {
  _arguments -s \
    $_pdd_global_opts \
    '--output-sub=[Where to save the generated sub-prompt file.]:filename:_files' \
    '--output-modified=[Where to save the modified prompt file.]:filename:_files' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '3:example-code-file:_files' \
    '*:filename:_files'
}

# change
# Usage: pdd [GLOBAL OPTIONS] change [OPTIONS] CHANGE_PROMPT_FILE INPUT_CODE [INPUT_PROMPT_FILE]
# Options:
#   --output [LOCATION]
#   --csv
# Args:
#   1: CHANGE_PROMPT_FILE
#   2: INPUT_CODE (filename or directory)
#   3: INPUT_PROMPT_FILE (optional)
_pdd_change() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the modified prompt file.]:filename:_files' \
    '--csv[Use a CSV file for batch changes (columns: prompt_name, change_instructions).]' \
    '--budget=[Maximum cost allowed for the change process (default 5.0)]:float' \
    '1:change-prompt-file:_files' \
    '2:input-code:_files' \
    '3:optional-prompt-file:_files' \
    '*:filename:_files'
}

# update
# Usage: pdd [GLOBAL OPTIONS] update [OPTIONS] INPUT_PROMPT_FILE MODIFIED_CODE_FILE [INPUT_CODE_FILE]
# Options:
#   --output [LOCATION]
#   --git
# Args:
#   1: INPUT_PROMPT_FILE
#   2: MODIFIED_CODE_FILE
#   3: INPUT_CODE_FILE (optional)
_pdd_update() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the updated prompt file.]:filename:_files' \
    '--git[Use git history to find the original code file.]' \
    '1:prompt-file:_files' \
    '2:modified-code-file:_files' \
    '3:original-code-file:_files' \
    '*:filename:_files'
}

# detect
# Usage: pdd [GLOBAL OPTIONS] detect [OPTIONS] PROMPT_FILES... CHANGE_FILE
# Options:
#   --output [LOCATION]
# Args:
#   (multiple) PROMPT_FILES
#   (final) CHANGE_FILE
_pdd_detect() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the CSV file with analysis results.]:filename:_files' \
    '*:prompt-files:_files' \
    ':change-file:_files'
}

# conflicts
# Usage: pdd [GLOBAL OPTIONS] conflicts [OPTIONS] PROMPT1 PROMPT2
# Options:
#   --output [LOCATION]
# Args:
#   1: PROMPT1
#   2: PROMPT2
_pdd_conflicts() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the conflict analysis CSV file.]:filename:_files' \
    '1:prompt-file1:_files' \
    '2:prompt-file2:_files' \
    '*:filename:_files'
}

# crash
# Usage: pdd [GLOBAL OPTIONS] crash [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE
# Options:
#   --output [LOCATION]
#   --output-program [LOCATION]
#   --loop
#   --max-attempts [INT]
#   --budget [FLOAT]
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
#   3: PROGRAM_FILE
#   4: ERROR_FILE
_pdd_crash() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the fixed code file.]:filename:_files' \
    '--output-program=[Where to save the fixed program file.]:filename:_files' \
    '--loop[Enable iterative fixing process.]' \
    '--max-attempts=[Maximum fix attempts.]:int' \
    '--budget=[Maximum cost allowed for fixes (default 5.0)]:float' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '3:program-file:_files' \
    '4:error-file:_files' \
    '*:filename:_files'
}

# trace
# Usage: pdd [GLOBAL OPTIONS] trace [OPTIONS] PROMPT_FILE CODE_FILE CODE_LINE
# Options:
#   --output [LOCATION]
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
#   3: CODE_LINE
_pdd_trace() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the trace analysis results.]:filename:_files' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '3:code-line: ' \
    '*:filename:_files'
}

# bug
# Usage: pdd [GLOBAL OPTIONS] bug [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE CURRENT_OUTPUT_FILE DESIRED_OUTPUT_FILE
# Options:
#   --output [LOCATION]
#   --language [LANGUAGE]
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
#   3: PROGRAM_FILE
#   4: CURRENT_OUTPUT_FILE
#   5: DESIRED_OUTPUT_FILE
_pdd_bug() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the generated unit test.]:filename:_files' \
    '--language=[Programming language for the unit test (default: Python)]:string:_guard' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '3:program-file:_files' \
    '4:current-output-file:_files' \
    '5:desired-output-file:_files' \
    '*:filename:_files'
}

# auto-deps
# Usage: pdd [GLOBAL OPTIONS] auto-deps [OPTIONS] PROMPT_FILE DIRECTORY_PATH
# Options:
#   --output [LOCATION]
#   --csv [FILENAME]
#   --force-scan
# Args:
#   1: PROMPT_FILE
#   2: DIRECTORY_PATH (directory or glob pattern)
_pdd_auto_deps() {
  _arguments -s \
    $_pdd_global_opts \
    '--output=[Where to save the modified prompt file with dependencies inserted.]:filename:_files' \
    '--csv=[CSV file for dependency info (default: project_dependencies.csv).]:filename:_files' \
    '--force-scan[Force rescanning of all potential dependency files.]' \
    '1:prompt-file:_files' \
    '2:directory-or-glob:_files -/' \
    '*:filename:_files'
}

# verify
# Usage: pdd [GLOBAL OPTIONS] verify [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE
# Options:
#   --output-results [LOCATION]
#   --output-code [LOCATION]
#   --output-program [LOCATION]
#   --max-attempts [INT]
#   --budget [FLOAT]
# Args:
#   1: PROMPT_FILE
#   2: CODE_FILE
#   3: PROGRAM_FILE
_pdd_verify() {
  _arguments -s \
    $_pdd_global_opts \
    '--output-results=[Where to save verification and fixing results log.]:filename:_files' \
    '--output-code=[Where to save the successfully verified code file.]:filename:_files' \
    '--output-program=[Where to save the successfully verified program file.]:filename:_files' \
    '--max-attempts=[Maximum fix attempts in verification loop (default 3)]:int' \
    '--budget=[Maximum cost for verification and fixing (default 5.0)]:float' \
    '1:prompt-file:_files' \
    '2:code-file:_files' \
    '3:program-file:_files' \
    '*:filename:_files'
}

# sync
# Usage: pdd [GLOBAL OPTIONS] sync [OPTIONS] BASENAME
# Options:
#   --max-attempts [INT]
#   --budget [FLOAT]
#   --skip-verify
#   --skip-tests
#   --target-coverage [FLOAT]
#   --log
# Arg:
#   1: BASENAME
_pdd_sync() {
  _arguments -s \
    $_pdd_global_opts \
    '--max-attempts=[Maximum attempts for iterative loops (default 3)]:int' \
    '--budget=[Maximum total cost for sync (default 10.0)]:float' \
    '--skip-verify[Skip the functional verification step]' \
    '--skip-tests[Skip unit test generation and fixing]' \
    '--target-coverage=[Desired code coverage percentage]:float' \
    '--log[Show analysis instead of executing operations]' \
    '1:basename: ' \
    '*: :'
}

# setup (no options)
_pdd_setup() {
  _arguments -s $_pdd_global_opts
}

# install_completion (no options)
_pdd_install_completion() {
  _arguments -s $_pdd_global_opts
}

# pytest-output
# Usage: pdd [GLOBAL OPTIONS] pytest-output [OPTIONS] TEST_FILE
# Options:
#   --json-only
# Arg:
#   1: TEST_FILE
_pdd_pytest_output() {
  _arguments -s \
    $_pdd_global_opts \
    '--json-only[Print only JSON to stdout]' \
    '1:test-file:_files' \
    '*:filename:_files'
}

##
# Main PDD completion dispatcher
##
_pdd() {
  local context="$curcontext" state line
  typeset -A opt_args

  # List of known subcommands with descriptions
  local -a _pdd_subcommands
  _pdd_subcommands=(
    'generate:Create runnable code from a prompt file'
    'example:Create an example file from an existing code file and the prompt'
    'test:Generate or enhance unit tests for a given code file'
    'preprocess:Preprocess prompt files and save the results'
    'fix:Fix errors in code and unit tests'
    'split:Split large complex prompt files'
    'change:Modify an input prompt file based on change instructions'
    'update:Update the original prompt file based on modified code'
    'detect:Analyze prompt files and a change description to see which need updating'
    'conflicts:Analyze two prompt files for conflicts'
    'crash:Fix errors in a code module and its calling program'
    'trace:Find the prompt file line number associated with a code line'
    'bug:Generate a unit test based on incorrect vs desired outputs'
    'auto-deps:Analyze a prompt and include deps from a directory or glob'
    'verify:Verify functional correctness using LLM judgment and iteratively fix'
    'sync:Synchronize prompt, code, examples, tests with analysis'
    'setup:Interactive setup and completion install'
    'install_completion:Install shell completion for current shell'
    'pytest-output:Run pytest and capture structured output'
  )

  # If there's no subcommand yet (i.e., user typed only "pdd " or "pdd -<Tab>"), offer global opts or subcommands.
  if (( CURRENT == 2 )); then
    _arguments -s \
      $_pdd_global_opts \
      '1: :->subcmds' && return 0
    # Show subcommands if user hasn't typed an option that consumes the argument.
    _describe -t subcommands 'pdd subcommand' _pdd_subcommands
    return
  fi

  # If the user typed a known subcommand, dispatch to that subcommand's completion function.
  case $words[2] in
    generate)
      _pdd_generate
      ;;
    example)
      _pdd_example
      ;;
    test)
      _pdd_test
      ;;
    preprocess)
      _pdd_preprocess
      ;;
    fix)
      _pdd_fix
      ;;
    split)
      _pdd_split
      ;;
    change)
      _pdd_change
      ;;
    update)
      _pdd_update
      ;;
    detect)
      _pdd_detect
      ;;
    conflicts)
      _pdd_conflicts
      ;;
    crash)
      _pdd_crash
      ;;
    trace)
      _pdd_trace
      ;;
    bug)
      _pdd_bug
      ;;
    auto-deps)
      _pdd_auto_deps
      ;;
    verify)
      _pdd_verify
      ;;
    sync)
      _pdd_sync
      ;;
    setup)
      _pdd_setup
      ;;
    install_completion)
      _pdd_install_completion
      ;;
    pytest-output)
      _pdd_pytest_output
      ;;
    # If the subcommand is unknown or not typed yet, fall back to showing the list of subcommands.
    *)
      _describe -t subcommands 'pdd subcommand' _pdd_subcommands
      ;;
  esac
}

# Register the _pdd function as a completion for pdd command
# Use command -v to safely check if compdef is available again
# (in case something went wrong with the initialization)
if command -v compdef >/dev/null 2>&1; then
  compdef _pdd pdd
else
  echo >&2 "Warning: Could not register pdd completion. Make sure ZSH completion system is working."
fi

# End of pdd_completion.zsh
