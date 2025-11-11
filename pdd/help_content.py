"""
Rich help content for all PDD CLI commands.

This module contains the detailed documentation for each command that will be
displayed when users run --help. Content is organized with quick reference at
the top, followed by detailed information.
"""

# --- SYNC Command Help ---
SYNC_HELP = """
PRIMARY COMMAND - Automatically execute the complete PDD workflow loop for a given basename.

This command implements the entire synchronized cycle from the whitepaper, intelligently
determining what steps are needed and executing them in the correct order with real-time
visual feedback and sophisticated state management.

\b
USAGE:
    pdd [GLOBAL OPTIONS] sync [OPTIONS] BASENAME

IMPORTANT: Sync frequently overwrites generated files to keep outputs up to date. In most
real runs, include the global --force flag to allow overwrites without interactive confirmation:

    pdd --force sync BASENAME

    pdd --force sync BASENAME

\b
DESCRIPTION:
The sync command is the recommended starting point for most PDD workflows. It automatically
detects what files exist and executes the appropriate workflow:

\b
  1. auto-deps   - Find and inject relevant dependencies into the prompt if needed

\b
  2. generate    - Create or update the code module from the prompt

\b
  3. example     - Generate usage example if it doesn't exist or is outdated

\b
  4. crash       - Fix any runtime errors to make code executable

\b
  5. verify      - Run functional verification against prompt intent (unless --skip-verify)

\b
  6. test        - Generate comprehensive unit tests if they don't exist (unless --skip-tests)

\b
  7. fix         - Resolve any bugs found by unit tests

\b
  8. update      - Back-propagate any learnings to the prompt file

\b
Language Detection:
The sync command automatically detects the programming language by scanning for existing
prompt files matching the pattern {basename}_{language}.prompt in the prompts directory.

Examples:

\b
  • factorial_calculator_python.prompt → generates factorial_calculator.py

\b
  • factorial_calculator_typescript.prompt → generates factorial_calculator.ts

\b
  • factorial_calculator_javascript.prompt → generates factorial_calculator.js

If multiple development language prompt files exist for the same basename, sync will process
all of them.

\b
Real-time Progress Animation:
The sync command provides live visual feedback showing:

\b
  • Current operation being executed

\b
  • File status indicators with color coding (Green: up-to-date, Yellow: processing, 
    Red: errors, Blue: analyzing)

\b
  • Running cost totals and time elapsed

\b
  • Progress through the workflow steps

\b
Advanced Decision Making:

\b
  • Fingerprint-based Change Detection: Uses content hashes and timestamps to detect changes

\b
  • LLM-powered Conflict Resolution: For complex scenarios with multiple file changes

\b
  • Persistent State Tracking: Maintains sync history in .pdd/meta/ directory

\b
  • Smart Lock Management: Prevents concurrent sync operations

\b
ARGUMENTS:
  BASENAME    The base name for the prompt file (e.g., "factorial_calculator" for 
              "factorial_calculator_python.prompt")

\b
EXAMPLES:
  Complete workflow with progress animation:
    $ pdd --force sync factorial_calculator

\b
  Advanced sync with higher budget and custom coverage:
    $ pdd --force sync --budget 15.0 --target-coverage 95.0 data_processor

\b
  Quick sync without verification:
    $ pdd --force sync --skip-verify --budget 5.0 web_scraper

\b
  View comprehensive sync log with decision analysis:
    $ pdd sync --log factorial_calculator

\b
  Context-aware examples:
    $ cd backend && pdd --force sync calculator     # Uses backend context settings
    $ cd frontend && pdd --force sync dashboard     # Uses frontend context
    $ pdd --context backend --force sync calculator # Explicit context override

\b
THE .PDD DIRECTORY:
PDD uses a .pdd directory in your project root to store metadata and configuration:
  • .pdd/meta/       - Contains fingerprint files, run reports, and sync logs
  • .pdd/locks/      - Stores lock files to prevent concurrent operations
  • .pdd/llm_model.csv - Project-specific LLM model configuration (optional)

This directory should typically be added to version control (except for lock files).

\b
SEE ALSO:
  pdd generate --help   - Generate code from prompts
  pdd test --help       - Generate unit tests
  pdd fix --help        - Fix errors in code
  pdd verify --help     - Verify functional correctness
  pdd update --help     - Update prompts from code changes
"""

# --- GENERATE Command Help ---
GENERATE_HELP = """
Create runnable code from a prompt file with support for parameterized prompts.

This command produces the full implementation code that fulfills all requirements in the prompt.
When changes are detected between the current prompt and its last committed version, it can
automatically perform incremental updates rather than full regeneration.

\b
USAGE:
    pdd [GLOBAL OPTIONS] generate [OPTIONS] PROMPT_FILE

\b
DESCRIPTION:
The generate command is your primary tool for converting prompts into code. It supports:

\b
  • Parameterized prompts: Use -e/--env to pass variables for multi-variant generation

\b
  • Incremental updates: Automatically detects changes and patches existing code when possible

\b
  • Git integration: Compares current prompt with last committed version

\b
  • Template variables: Use $VAR or ${VAR} in prompts and output paths

\b
Parameter Variables (-e/--env):
Pass key=value pairs to parameterize a prompt so one prompt can generate multiple variants:

\b
  • Syntax: -e KEY=VALUE or --env KEY=VALUE (repeatable)

\b
  • Docker-style env fallback: -e KEY reads VALUE from the current process environment

\b
  • Precedence: Values passed with -e/--env override same-named OS environment variables

\b
Templating:
Prompt files and --output values may reference variables using $VAR or ${VAR}:

\b
  • In prompt content: $VAR and ${VAR} are replaced only when VAR was provided

\b
  • In output path: PDD expands $VAR/${VAR} using the same variable set

\b
  • Unknowns: Placeholders without a provided value are left unchanged

\b
Git Integration:

\b
  • When changes are detected between current and committed prompt, considers incremental 
    generation

\b
  • Both current prompt and code files are staged with git add after incremental updates

\b
  • Full regeneration happens for new files or when existing output is deleted

\b
ARGUMENTS:
  PROMPT_FILE    The filename of the prompt file used to generate the code (or use 
                 --template NAME instead)

\b
EXAMPLES:
  Basic generation with automatic change detection:
    $ pdd generate --output src/calculator.py calculator_python.prompt

\b
  Parameterized generation (Python module):
    $ pdd generate -e MODULE=orders --output 'src/${MODULE}.py' prompts/module_python.prompt

\b
  Generate multiple files from same prompt:
    $ pdd generate -e MODULE=orders --output 'src/${MODULE}.py' prompts/module_python.prompt
    $ pdd generate -e MODULE=payments --output 'src/${MODULE}.py' prompts/module_python.prompt
    $ pdd generate -e MODULE=customers --output 'src/${MODULE}.py' prompts/module_python.prompt

\b
  Multiple variables:
    $ pdd generate -e MODULE=orders -e PACKAGE=core \\
        --output 'src/${PACKAGE}/${MODULE}.py' prompts/module_python.prompt

\b
  Docker-style env fallback:
    $ export MODULE=orders
    $ pdd generate -e MODULE --output 'src/${MODULE}.py' prompts/module_python.prompt

\b
  Force incremental patching:
    $ pdd generate --incremental --output src/calculator.py calculator_python.prompt

\b
  Using a template:
    $ pdd generate --template architecture/architecture_json \\
        -e PRD_FILE=docs/specs.md --output architecture.json

\b
BUILT-IN TEMPLATES:
PDD includes curated templates for common use cases:

  • architecture/architecture_json: Universal architecture generator (requires -e PRD_FILE=...)

\b
  List available templates:
    $ pdd templates list

\b
  View template details:
    $ pdd templates show architecture/architecture_json

\b
  Copy template to your project:
    $ pdd templates copy architecture/architecture_json --to prompts/

\b
SEE ALSO:
  pdd sync --help       - Complete workflow automation
  pdd example --help    - Generate usage examples
  pdd update --help     - Update prompts from code changes
  pdd templates list    - List available templates
"""

# --- EXAMPLE Command Help ---
EXAMPLE_HELP = """
Create a compact example demonstrating how to use functionality defined in a prompt.

Similar to a header file or API documentation, this produces minimal, token-efficient code
that shows the interface without implementation details.

\b
USAGE:
    pdd [GLOBAL OPTIONS] example [OPTIONS] PROMPT_FILE CODE_FILE

\b
DESCRIPTION:
The example command generates concise usage demonstrations that serve multiple purposes:

\b
  • Dependency references: Examples serve as lightweight interface references for other prompts

\b
  • Sanity checks: Example programs are used for crash and verify commands

\b
  • Auto-deps integration: The auto-deps command scans example files to identify dependencies

Examples are more token-efficient than including full implementations in other prompts,
making them ideal for reusable references.

\b
ARGUMENTS:
  PROMPT_FILE    The filename of the prompt file that generated the code
  CODE_FILE      The filename of the existing code file

\b
EXAMPLES:
  Generate an example:
    $ pdd example --output examples/factorial_calculator_example.py \\
        factorial_calculator_python.prompt \\
        src/factorial_calculator.py

\b
  Use with default output path:
    $ export PDD_EXAMPLE_OUTPUT_PATH=examples/
    $ pdd example factorial_calculator_python.prompt src/factorial_calculator.py

\b
PROVIDING COMMAND-SPECIFIC CONTEXT:
The example command can be guided by project-specific context files. If a file named
context/example.prompt exists in the current working directory, its content is
automatically included in the internal prompt.

This allows you to provide:

\b
  • Required import statements

\b
  • Project-specific patterns

\b
  • Coding conventions

Example context file (context/example.prompt):
    Please ensure all examples follow the project's import style:
    from my_module import function_name
    
    Include a main() function wrapper for all examples.

\b
SEE ALSO:
  pdd generate --help   - Generate code from prompts
  pdd auto-deps --help  - Analyze and insert dependencies
  pdd crash --help      - Fix runtime errors using examples
  pdd verify --help     - Verify correctness using examples
"""

# --- TEST Command Help ---
TEST_HELP = """
Generate or enhance unit tests for a given code file and its corresponding prompt file.

Test organization: For each target <basename>, PDD maintains a single test file that
accumulates tests over time rather than being regenerated from scratch.

\b
USAGE:
    pdd [GLOBAL OPTIONS] test [OPTIONS] PROMPT_FILE CODE_FILE

\b
DESCRIPTION:
The test command helps you build comprehensive test suites by:

\b
  • Generating initial tests: Creating test files from prompts and code

\b
  • Improving coverage: Analyzing coverage reports and adding targeted tests

\b
  • Merging tests: Integrating new tests with existing test files

\b
  • Maintaining consistency: Following project conventions and existing test patterns

\b
Test Accumulation Strategy:
New tests accumulate in the same file over time. When augmenting tests, PDD can merge
additions into the existing file using the --merge option, preserving your manually
written tests and comments.

\b
Coverage Analysis Strategy:
When coverage options are provided, the test command will:

\b
  1. Analyze the coverage report to identify:
     - Uncovered lines and branches
     - Partially tested conditions
     - Missing edge cases

\b
  2. Generate additional test cases prioritizing:
     - Complex uncovered code paths
     - Error conditions
     - Boundary values
     - Integration points

\b
  3. Maintain consistency with:
     - Existing test style and patterns
     - Project's testing conventions
     - Original prompt's intentions

\b
ARGUMENTS:
  PROMPT_FILE    The filename of the prompt file that generated the code
  CODE_FILE      The filename of the code file to be tested

\b
EXAMPLES:
  Generate initial unit tests:
    $ pdd test --output tests/test_factorial_calculator.py \\
        factorial_calculator_python.prompt \\
        src/factorial_calculator.py

\b
  Generate tests to improve coverage:
    $ pdd test --coverage-report coverage.xml \\
        --existing-tests tests/test_calculator.py \\
        --output tests/test_calculator_enhanced.py \\
        calculator_python.prompt \\
        src/calculator.py

\b
  Improve coverage and merge with existing tests:
    $ pdd test --coverage-report coverage.xml \\
        --existing-tests tests/test_calculator.py \\
        --merge \\
        --target-coverage 95.0 \\
        calculator_python.prompt \\
        src/calculator.py

\b
PROVIDING COMMAND-SPECIFIC CONTEXT:
The test command can be guided by project-specific context files. If a file named
context/test.prompt exists in the current working directory, its content is
automatically included in the internal prompt.

Example context file (context/test.prompt):
    Please ensure all tests use the 'unittest' framework and import the main module as:
    from my_module import *
    
    Follow these conventions:
    - Use descriptive test names starting with test_
    - Include docstrings for complex test cases
    - Use setUp() and tearDown() methods when appropriate

\b
SEE ALSO:
  pdd sync --help       - Complete workflow with automatic test generation
  pdd fix --help        - Fix errors found by tests
  pdd generate --help   - Generate code from prompts
"""

# Add more command help content as needed...

# --- FIX Command Help ---
FIX_HELP = """
Fix errors in code and unit tests based on error messages and the original prompt file.

This command can operate in single-fix mode or iterative loop mode with automatic
verification and budget controls.

\b
USAGE:
    pdd [GLOBAL OPTIONS] fix [OPTIONS] PROMPT_FILE CODE_FILE UNIT_TEST_FILE ERROR_FILE

\b
DESCRIPTION:
The fix command analyzes test failures and runtime errors to automatically correct both
the code under test and the test file itself. It can:

\b
  • Fix unit test errors based on error messages

\b
  • Iterate through multiple fix attempts

\b
  • Verify fixes using a verification program

\b
  • Track costs and respect budget limits

\b
  • Auto-submit examples when all tests pass

\b
Iterative Fixing with --loop:
When using the --loop option, fix will:

\b
  1. Analyze the error messages

\b
  2. Apply fixes to code and/or tests

\b
  3. Run the verification program

\b
  4. Repeat until errors are resolved, max attempts reached, or budget exhausted

The process creates timestamped intermediate versions for each iteration, allowing you
to track the fixing process and roll back if needed.

\b
ARGUMENTS:
  PROMPT_FILE      The filename of the prompt file that generated the code under test
  CODE_FILE        The filename of the code file to be fixed
  UNIT_TEST_FILE   The filename of the unit test file
  ERROR_FILE       File containing unit test runtime error messages (optional with --loop)

\b
OUTPUTS:
When using --loop, the command returns:

\b
  • Success status (boolean)

\b
  • Total number of fix attempts made

\b
  • Total cost of all fix attempts

\b
  • Timestamped intermediate files for each iteration

\b
EXAMPLES:
  Basic fix operation:
    $ pdd fix --output-test tests/test_calculator_fixed.py \\
        --output-code src/calculator_fixed.py \\
        --output-results results/calculator_fix_results.log \\
        calculator_python.prompt \\
        src/calculator.py \\
        tests/test_calculator.py \\
        errors.log

\b
  Iterative fixing with verification:
    $ pdd fix --loop \\
        --verification-program examples/calculator_example.py \\
        --max-attempts 5 \\
        --budget 10.0 \\
        calculator_python.prompt \\
        src/calculator.py \\
        tests/test_calculator.py \\
        errors.log

\b
  With auto-submit on success:
    $ pdd fix --loop \\
        --verification-program examples/calculator_example.py \\
        --auto-submit \\
        calculator_python.prompt \\
        src/calculator.py \\
        tests/test_calculator.py

\b
SEE ALSO:
  pdd sync --help    - Complete workflow with automatic fixing
  pdd test --help    - Generate unit tests
  pdd crash --help   - Fix runtime errors
  pdd verify --help  - Verify functional correctness
"""

# --- UPDATE Command Help ---
UPDATE_HELP = """
Update the original prompt file based on modified code.

IMPORTANT: By default, this command overwrites the original prompt file to maintain
the core PDD principle of "prompts as source of truth."

\b
USAGE:
    pdd [GLOBAL OPTIONS] update [OPTIONS] INPUT_PROMPT_FILE MODIFIED_CODE_FILE [INPUT_CODE_FILE]

\b
DESCRIPTION:
The update command implements the code-to-prompt flow, ensuring that prompts remain
synchronized with code changes. This maintains prompts as the authoritative source of
truth in the PDD workflow.

\b
Git Integration:
When using the --git option, the command automatically finds the original code from
git history, eliminating the need to specify INPUT_CODE_FILE manually.

\b
Default Behavior - In-Place Updates:
Unlike most PDD commands, update overwrites the original prompt file by default to
ensure prompts remain in their canonical location. Use --output to save to a different
location if needed.

\b
ARGUMENTS:
  INPUT_PROMPT_FILE    The filename of the prompt file that generated the original code
  MODIFIED_CODE_FILE   The filename of the code that was modified
  INPUT_CODE_FILE      Optional: The filename of the original code (not needed with --git)

\b
EXAMPLES:
  Overwrite original prompt (default behavior):
    $ pdd update factorial_calculator_python.prompt \\
        src/modified_factorial_calculator.py \\
        src/original_factorial_calculator.py

\b
  Save to different location:
    $ pdd update --output updated_factorial_calculator_python.prompt \\
        factorial_calculator_python.prompt \\
        src/modified_factorial_calculator.py \\
        src/original_factorial_calculator.py

\b
  Using git integration:
    $ pdd update --git \\
        factorial_calculator_python.prompt \\
        src/modified_factorial_calculator.py

\b
WORKFLOW INTEGRATION:
The update command is typically used:

\b
  • After manually editing generated code

\b
  • As the final step in the sync workflow to back-propagate learnings

\b
  • When code changes need to be reflected in the authoritative prompts

\b
SEE ALSO:
  pdd sync --help      - Complete workflow with automatic updates
  pdd generate --help  - Generate code from prompts
  pdd change --help    - Modify prompts based on change instructions
"""

# --- PREPROCESS Command Help ---
PREPROCESS_HELP = """
Preprocess prompt files by handling includes, comments, and other directives.

This command processes XML-like tags and other special syntax in prompt files,
preparing them for use with LLM models.

\b
USAGE:
    pdd [GLOBAL OPTIONS] preprocess [OPTIONS] PROMPT_FILE

\b
DESCRIPTION:
The preprocess command transforms prompt files by:

\b
  • Processing <include> tags to inject file contents

\b
  • Executing <shell> commands and embedding output

\b
  • Scraping <web> URLs and including markdown content

\b
  • Removing <pdd> comment tags

\b
  • Handling triple backtick includes with angle brackets

\b
  • Optionally inserting XML delimiters for structure

\b
  • Doubling curly brackets for template engines

\b
SUPPORTED TAGS:

\b
  1. <include>: Include file contents directly
     <include>./path/to/file.txt</include>

\b
  2. <pdd>: Comments removed from output
     <pdd>This won't appear in preprocessed output</pdd>

\b
  3. <shell>: Execute shell commands and include output
     <shell>ls -la</shell>

\b
  4. <web>: Scrape webpage and include markdown content
     <web>https://example.com</web>

\b
Triple Backtick Includes:
Alternative include syntax using code blocks:

    ```
    <./path/to/file.txt>
    ```

This will be recursively processed until no more angle brackets remain.

\b
Curly Bracket Handling:
When using the --double option:

\b
  • Single curly brackets are doubled if not already doubled

\b
  • Already doubled brackets are preserved

\b
  • Nested brackets are properly handled

\b
  • Special handling for code blocks (JSON, JavaScript, TypeScript, Python)

\b
Use --exclude to specify keys that should NOT be doubled. Only applies when the
entire string inside braces exactly matches an excluded key.

Example with --exclude model:

\b
  • {model} remains {model} (exact match)

\b
  • {model_name} becomes {{model_name}} (not exact match)

\b
  • {api_model} becomes {{api_model}} (not exact match)

\b
ARGUMENTS:
  PROMPT_FILE    The filename of the prompt file to preprocess

\b
EXAMPLES:
  Basic preprocessing:
    $ pdd preprocess --output preprocessed/calculator_preprocessed.prompt \\
        calculator_python.prompt

\b
  Recursive preprocessing with XML delimiters:
    $ pdd preprocess --xml --recursive \\
        --output preprocessed/main_preprocessed.prompt \\
        main_python.prompt

\b
  Double curly brackets with exclusions:
    $ pdd preprocess --double \\
        --exclude model,temperature \\
        --output preprocessed/template_preprocessed.prompt \\
        template_python.prompt

\b
  Full preprocessing with all options:
    $ pdd preprocess --recursive \\
        --double \\
        --exclude model,temperature,api_key \\
        --output preprocessed/full_preprocessed.prompt \\
        factorial_calculator_python.prompt

\b
PROVIDING COMMAND-SPECIFIC CONTEXT:
Some PDD commands (like test and example) automatically look for context files
during preprocessing:

\b
  • context/test.prompt - Included by the test command

\b
  • context/example.prompt - Included by the example command

These files are incorporated using the <include> mechanism to provide project-specific
guidance.

\b
SEE ALSO:
  pdd generate --help  - Generate code from prompts (uses preprocessing)
  pdd test --help      - Generate tests (uses context files)
  pdd example --help   - Generate examples (uses context files)
"""

# --- SPLIT Command Help ---
SPLIT_HELP = """
Split large complex prompt files into smaller, more manageable prompt files.

This command helps refactor monolithic prompts by extracting functionality into
separate modules with proper dependency management.

\b
USAGE:
    pdd [GLOBAL OPTIONS] split [OPTIONS] INPUT_PROMPT INPUT_CODE EXAMPLE_CODE

\b
DESCRIPTION:
The split command refactors large prompts by:

\b
  • Extracting a portion of functionality into a new sub-prompt

\b
  • Creating a modified version of the original prompt that references the sub-prompt

\b
  • Maintaining proper dependencies between prompts

\b
  • Using example code as the interface specification

This is the prompt-level equivalent of code refactoring - breaking down large
modules into smaller, reusable components.

\b
ARGUMENTS:
  INPUT_PROMPT    The filename of the large prompt file to be split
  INPUT_CODE      The filename of the code generated from the input prompt
  EXAMPLE_CODE    The filename of example code serving as the sub-module interface

\b
EXAMPLES:
  Basic split operation:
    $ pdd split --output-sub prompts/sub_data_processing.prompt \\
        --output-modified prompts/modified_main_pipeline.prompt \\
        data_processing_pipeline_python.prompt \\
        src/data_pipeline.py \\
        examples/pipeline_interface.py

\b
  With environment variables:
    $ export PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH=prompts/modules/
    $ export PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH=prompts/
    $ pdd split data_processing_pipeline_python.prompt \\
        src/data_pipeline.py \\
        examples/pipeline_interface.py

\b
SEE ALSO:
  pdd generate --help  - Generate code from prompts
  pdd example --help   - Create interface examples
  pdd auto-deps --help - Manage dependencies
"""

# --- CHANGE Command Help ---
CHANGE_HELP = """
Modify an input prompt file based on a change prompt and the corresponding input code.

This command supports both single-prompt changes and batch operations via CSV files.

\b
USAGE:
    pdd [GLOBAL OPTIONS] change [OPTIONS] CHANGE_PROMPT_FILE INPUT_CODE [INPUT_PROMPT_FILE]

\b
DESCRIPTION:
The change command modifies prompts based on change instructions, supporting:

\b
  • Single prompt changes: Apply changes to one prompt at a time

\b
  • Batch changes via CSV: Process multiple prompts in one operation

\b
  • Code-aware modifications: Uses existing code to inform changes

\b
  • Budget controls: Set maximum costs for change operations

\b
ARGUMENTS:
  CHANGE_PROMPT_FILE    File containing instructions on how to modify the prompt (or CSV file with --csv)
  INPUT_CODE            The code file generated from the prompt (or directory with --csv)
  INPUT_PROMPT_FILE     Optional: The prompt file to modify (not needed with --csv)

\b
CSV FORMAT:
When using --csv, the CSV file should have these columns:

\b
  • prompt_name: Name of the prompt file (e.g., calculator_python.prompt)

\b
  • change_instructions: Description of changes to make

The command expects prompts to follow the <basename>_<language>.prompt convention
and looks for corresponding code files in the INPUT_CODE directory.

\b
EXAMPLES:
  Single prompt change:
    $ pdd change --output modified_factorial_calculator_python.prompt \\
        changes_factorial.prompt \\
        src/factorial_calculator.py \\
        factorial_calculator_python.prompt

\b
  Batch change using CSV:
    $ pdd change --csv --output modified_prompts/ \\
        changes_batch.csv \\
        src/

\b
  With budget control:
    $ pdd change --budget 10.0 \\
        --output modified_calculator_python.prompt \\
        changes.prompt \\
        src/calculator.py \\
        calculator_python.prompt

\b
SEE ALSO:
  pdd update --help    - Update prompts from code changes
  pdd detect --help    - Detect which prompts need changes
  pdd generate --help  - Generate code from modified prompts
"""

# --- AUTO-DEPS Command Help ---
AUTO_DEPS_HELP = """
Analyze and insert needed dependencies into a prompt file.

This command automatically discovers and includes relevant dependencies by scanning
example files and analyzing the prompt's requirements.

\b
USAGE:
    pdd [GLOBAL OPTIONS] auto-deps [OPTIONS] PROMPT_FILE

\b
DESCRIPTION:
The auto-deps command enhances prompts by:

\b
  • Scanning example files for potential dependencies

\b
  • Analyzing the prompt's requirements and context

\b
  • Intelligently selecting relevant dependencies

\b
  • Inserting appropriate <include> directives

\b
  • Maintaining prompt modularity and reusability

This automates the dependency management aspect of prompt engineering, similar to
how package managers handle code dependencies.

\b
ARGUMENTS:
  PROMPT_FILE    The filename of the prompt file to analyze and enhance

\b
HOW IT WORKS:

\b
  1. Example Scanning: Searches for example files in examples/**/*.py and similar patterns

\b
  2. Content Analysis: Examines imports, API usage, and patterns in each example

\b
  3. Relevance Scoring: Uses LLM to determine which examples are relevant to the prompt

\b
  4. Dependency Injection: Inserts appropriate <include> tags for selected dependencies

\b
  5. Deduplication: Ensures each dependency is included only once

\b
EXAMPLES:
  Basic dependency analysis:
    $ pdd auto-deps --output prompts/calculator_with_deps_python.prompt \\
        prompts/calculator_python.prompt

\b
  With custom output path:
    $ export PDD_AUTO_DEPS_OUTPUT_PATH=prompts/enhanced/
    $ pdd auto-deps calculator_python.prompt

\b
INTEGRATION WITH SYNC:
The sync command automatically runs auto-deps as its first step, ensuring
prompts always have up-to-date dependencies before code generation.

\b
SEE ALSO:
  pdd sync --help      - Automatic workflow including auto-deps
  pdd example --help   - Generate examples that auto-deps can discover
  pdd generate --help  - Generate code from dependency-enhanced prompts
"""

# --- VERIFY Command Help ---
VERIFY_HELP = """
Verify functional correctness by running a program and judging its output against the prompt's intent.

This command uses LLM judgment to determine if code behaves as specified in the prompt,
beyond just passing unit tests.

\b
USAGE:
    pdd [GLOBAL OPTIONS] verify [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE

\b
DESCRIPTION:
The verify command provides functional verification by:

\b
  • Running a verification program (typically an example)

\b
  • Capturing the program's output

\b
  • Using LLM to judge if output matches prompt intent

\b
  • Iteratively fixing issues until verification passes

\b
  • Tracking costs and attempts

This complements unit testing by verifying the overall behavior and user experience
described in the prompt.

\b
ARGUMENTS:
  PROMPT_FILE     The prompt file describing the intended behavior
  CODE_FILE       The code file being verified
  PROGRAM_FILE    The program to run for verification (typically an example file)

\b
VERIFICATION PROCESS:

\b
  1. Execute: Run the verification program

\b
  2. Capture: Record all output (stdout, stderr, exit code)

\b
  3. Judge: LLM compares output against prompt intent

\b
  4. Report: Detailed success/failure with reasoning

\b
  5. Fix (with --loop): Automatically correct issues and retry

\b
EXAMPLES:
  Basic verification:
    $ pdd verify prompt.prompt code.py example.py

\b
  Verification with iterative fixing:
    $ pdd verify --loop \\
        --max-attempts 5 \\
        --budget 10.0 \\
        --output-results results/verification.log \\
        calculator_python.prompt \\
        src/calculator.py \\
        examples/calculator_example.py

\b
WHEN TO USE:

\b
  • Verifying user-facing behavior matches specifications

\b
  • Checking output format and content quality

\b
  • Ensuring examples demonstrate correct usage

\b
  • Complementing unit tests with end-to-end checks

\b
SEE ALSO:
  pdd sync --help   - Automatic workflow including verification
  pdd test --help   - Generate and run unit tests
  pdd crash --help  - Fix runtime errors
  pdd fix --help    - Fix errors found by tests
"""

# --- CRASH Command Help ---
CRASH_HELP = """
Fix errors in a code module and its calling program that caused a crash.

This command addresses runtime errors by fixing both the implementation and
the program that invokes it.

\b
USAGE:
    pdd [GLOBAL OPTIONS] crash [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE

\b
DESCRIPTION:
The crash command handles runtime errors by:

\b
  • Analyzing crash error messages

\b
  • Fixing the code module that crashed

\b
  • Fixing the calling program if needed

\b
  • Running verification to ensure fixes work

\b
  • Iterating until the crash is resolved

This is particularly useful for fixing errors discovered when running examples
or integration tests.

\b
ARGUMENTS:
  PROMPT_FILE     The prompt file for the code module
  CODE_FILE       The code file that crashed
  PROGRAM_FILE    The program that called the code (typically an example)
  ERROR_FILE      File containing the error messages (optional with --loop)

\b
EXAMPLES:
  Basic crash fix:
    $ pdd crash prompt.prompt code.py program.py errors.log

\b
  Iterative crash fixing:
    $ pdd crash --loop \\
        --max-attempts 5 \\
        --budget 10.0 \\
        calculator_python.prompt \\
        src/calculator.py \\
        examples/calculator_example.py

\b
INTEGRATION WITH SYNC:
The sync command automatically runs crash after generate to ensure
the generated code is runnable before proceeding to testing.

\b
SEE ALSO:
  pdd sync --help    - Automatic workflow including crash fixing
  pdd verify --help  - Verify functional correctness
  pdd fix --help     - Fix unit test errors
"""

# You can continue adding help content for other commands...
# For brevity, I'm showing the pattern with these key commands.
