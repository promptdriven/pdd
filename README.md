# PDD (Prompt-Driven Development) Command Line Interface

## Introduction

PDD (Prompt-Driven Development) is a versatile tool for generating code, creating examples, running unit tests, and managing prompt files. It leverages AI models to streamline the development process, allowing developers to work more efficiently with prompt-driven code generation.

## Basic Installation

Install PDD using pip:
```bash
pip install pdd-cli
```

Verify installation:
```bash
pdd --version
```

## Advanced Installation Options

### Virtual Environment Installation
```bash
# Create virtual environment
python -m venv pdd-env

# Activate environment
# On Windows:
pdd-env\Scripts\activate
# On Unix/MacOS:
source pdd-env/bin/activate

# Install PDD
pip install pdd-cli
```

## Cloud vs Local Execution

PDD commands can be run either in the cloud or locally. By default, all commands run in the cloud mode, which provides several advantages:

- No need to manage API keys locally
- Access to more powerful models
- Shared examples and improvements across the PDD community
- Automatic updates and improvements
- Better cost optimization

### Cloud Authentication

When running in cloud mode (default), PDD uses GitHub Single Sign-On (SSO) for authentication. On first use, you'll be prompted to authenticate:

1. PDD will open your default browser to the GitHub login page
2. Log in with your GitHub account
3. Authorize PDD Cloud to access your GitHub profile
4. Once authenticated, you can return to your terminal to continue using PDD

The authentication token is securely stored locally and automatically refreshed as needed.

### Local Mode Requirements

When running in local mode with the `--local` flag, you'll need to set up API keys for the language models:

```bash
# For OpenAI
export OPENAI_API_KEY=your_api_key_here

# For Anthropic
export ANTHROPIC_API_KEY=your_api_key_here

# For other supported providers (LiteLLM supports multiple LLM providers)
export PROVIDER_API_KEY=your_api_key_here
```

Add these to your `.bashrc`, `.zshrc`, or equivalent for persistence.

PDD's local mode uses LiteLLM for interacting with language models, providing:

- Support for multiple model providers (OpenAI, Anthropic, Google/Vertex AI, and more)
- Automatic model selection based on strength settings
- Response caching for improved performance
- Smart token usage tracking and cost estimation
- Interactive API key acquisition when keys are missing

When keys are missing, PDD will prompt for them interactively and securely store them in your local `.env` file.

### Local Model Configuration

PDD uses a CSV file to configure model selection and capabilities. This configuration is loaded from:

1. User-specific configuration: `~/.pdd/llm_model.csv` (takes precedence if it exists)
2. Project-specific configuration: `<PROJECT_ROOT>/data/llm_model.csv`

The CSV includes columns for:
- `provider`: The LLM provider (e.g., "openai", "anthropic", "google")
- `model`: The LiteLLM model identifier (e.g., "gpt-4", "claude-3-opus-20240229")
- `input`/`output`: Costs per million tokens
- `coding_arena_elo`: ELO rating for coding ability
- `api_key`: The environment variable name for the required API key
- `structured_output`: Whether the model supports structured JSON output
- `reasoning_type`: Support for reasoning capabilities ("none", "budget", or "effort")

For proper model identifiers to use in your custom configuration, refer to the [LiteLLM Model List](https://docs.litellm.ai/docs/providers) documentation. LiteLLM typically uses model identifiers in the format `provider/model_name` (e.g., "openai/gpt-4", "anthropic/claude-3-opus-20240229").

## Post-Installation Setup

1. Enable tab completion:
```bash
pdd install_completion
```

2. Configure environment variables (optional):
```bash
# Add to .bashrc, .zshrc, or equivalent
export PDD_AUTO_UPDATE=true
export PDD_GENERATE_OUTPUT_PATH=/path/to/generated/code/
export PDD_TEST_OUTPUT_PATH=/path/to/tests/
```

## Troubleshooting Common Installation Issues

1. **Command not found**
   ```bash
   # Add to PATH if needed
   export PATH="$HOME/.local/bin:$PATH"
   ```

2. **Permission errors**
   ```bash
   # Install with user permissions
   pip install --user pdd-cli
   ```

## Version

Current version: 0.0.27

To check your installed version, run:
```
pdd --version
```
PDD includes an auto-update feature to ensure you always have access to the latest features and security patches. You can control this behavior using an environment variable (see "Auto-Update Control" section below).

## Supported Programming Languages

PDD supports a wide range of programming languages, including but not limited to:
- Python
- JavaScript
- Java
- C++
- Ruby
- Go

The specific language is often determined by the prompt file's naming convention or specified in the command options.

## Prompt File Naming Convention

Prompt files in PDD follow this specific naming format:
```
<basename>_<language>.prompt
```
Where:
- `<basename>` is the base name of the file or project
- `<language>` is the programming language or context of the prompt file

Examples:
- `factorial_calculator_python.prompt` (basename: factorial_calculator, language: python)
- `responsive_layout_css.prompt` (basename: responsive_layout, language: css)
- `data_processing_pipeline_python.prompt` (basename: data_processing_pipeline, language: python)

## Prompt-Driven Development Philosophy

### Core Concepts

Prompt-Driven Development (PDD) inverts traditional software development by treating prompts as the primary artifact - not code. This paradigm shift has profound implications:

1. **Prompts as Source of Truth**: 
   In traditional development, source code is the ground truth that defines system behavior. In PDD, the prompts are authoritative, with code being a generated artifact.

2. **Natural Language Over Code**:
   Prompts are written primarily in natural language, making them more accessible to non-programmers and clearer in expressing intent.

3. **Regenerative Development**:
   When changes are needed, you modify the prompt and regenerate code, rather than directly editing the code. This maintains the conceptual integrity between requirements and implementation.

4. **Intent Preservation**:
   Prompts capture the "why" behind code in addition to the "what" - preserving design rationale in a way that comments often fail to do.

### Mental Model

To work effectively with PDD, adopt these mental shifts:

1. **Prompt-First Thinking**:
   Always start by defining what you want in a prompt before generating any code.

2. **Bidirectional Flow**:
   - Prompt → Code: The primary direction (generation)
   - Code → Prompt: Secondary but crucial (keeping prompts in sync with code changes)

3. **Modular Prompts**:
   Just as you modularize code, you should modularize prompts into self-contained units that can be composed.

4. **Integration via Examples**:
   Modules integrate through their examples, which serve as interfaces, allowing for token-efficient references.

### PDD Workflows: Conceptual Understanding

Each workflow in PDD addresses a fundamental development need:

1. **Initial Development Workflow**
   - **Purpose**: Creating functionality from scratch
   - **Conceptual Flow**: Define dependencies → Generate implementation → Create interfaces → Ensure runtime functionality → Verify correctness
   
   This workflow embodies the prompt-to-code pipeline, moving from concept to tested implementation.

2. **Code-to-Prompt Update Workflow**
   - **Purpose**: Maintaining prompt as source of truth when code changes
   - **Conceptual Flow**: Sync code changes to prompt → Identify impacts → Propagate changes
   
   This workflow ensures the information flow from code back to prompts, preserving prompts as the source of truth.

3. **Debugging Workflows**
   - **Purpose**: Resolving different types of issues
   - **Conceptual Types**:
     - **Context Issues**: Addressing misunderstandings in prompt interpretation
     - **Runtime Issues**: Fixing execution failures
     - **Logical Issues**: Correcting incorrect behavior
     - **Traceability Issues**: Connecting code problems back to prompt sections
   
   These workflows recognize that different errors require different resolution approaches.

4. **Refactoring Workflow**
   - **Purpose**: Improving prompt organization and reusability
   - **Conceptual Flow**: Extract functionality → Ensure dependencies → Create interfaces
   
   This workflow parallels code refactoring but operates at the prompt level.

5. **Multi-Prompt Architecture Workflow**
   - **Purpose**: Coordinating systems with multiple prompts
   - **Conceptual Flow**: Detect conflicts → Resolve incompatibilities → Regenerate code → Update interfaces → Verify system
   
   This workflow addresses the complexity of managing multiple interdependent prompts.

6. **Enhancement Phase**: Use Feature Enhancement when adding capabilities to existing modules.

### Workflow Selection Principles

The choice of workflow should be guided by your current development phase:

1. **Creation Phase**: Use Initial Development when building new functionality.

2. **Maintenance Phase**: Use Code-to-Prompt Update when existing code changes.

3. **Problem-Solving Phase**: Choose the appropriate Debugging workflow based on the issue type:
   - Preprocess → Generate for prompt interpretation issues
   - Crash for runtime errors
   - Bug → Fix for logical errors
   - Trace for locating problematic prompt sections

4. **Restructuring Phase**: Use Refactoring when prompts grow too large or complex.

5. **System Design Phase**: Use Multi-Prompt Architecture when coordinating multiple components.

6. **Enhancement Phase**: Use Feature Enhancement when adding capabilities to existing modules.

### PDD Design Patterns

Effective PDD employs these recurring patterns:

1. **Dependency Injection via Auto-deps**:
   Automatically including relevant dependencies in prompts.

2. **Interface Extraction via Example**:
   Creating minimal reference implementations for reuse.

3. **Bidirectional Traceability**:
   Maintaining connections between prompt sections and generated code.

4. **Test-Driven Prompt Fixing**:
   Using tests to guide prompt improvements when fixing issues.

5. **Hierarchical Prompt Organization**:
   Structuring prompts from high-level architecture to detailed implementations.

## Basic Usage

```
pdd [GLOBAL OPTIONS] COMMAND [OPTIONS] [ARGS]...
```

## Command Overview

Here is a brief overview of the main commands provided by PDD. Click the command name to jump to its detailed section:

- **[`generate`](#1-generate)**: Creates runnable code from a prompt file.
- **[`example`](#2-example)**: Generates a compact example showing how to use functionality defined in a prompt.
- **[`test`](#3-test)**: Generates or enhances unit tests for a code file and its prompt.
- **[`preprocess`](#4-preprocess)**: Preprocesses prompt files, handling includes, comments, and other directives.
- **[`fix`](#5-fix)**: Fixes errors in code and unit tests based on error messages and the original prompt.
- **[`split`](#6-split)**: Splits large prompt files into smaller, more manageable ones.
- **[`change`](#7-change)**: Modifies a prompt file based on instructions in a change prompt.
- **[`update`](#8-update)**: Updates the original prompt file based on modified code.
- **[`detect`](#9-detect)**: Analyzes prompts to determine which ones need changes based on a description.
- **[`conflicts`](#10-conflicts)**: Finds and suggests resolutions for conflicts between two prompt files.
- **[`crash`](#11-crash)**: Fixes errors in a code module and its calling program that caused a crash.
- **[`trace`](#12-trace)**: Finds the corresponding line number in a prompt file for a given code line.
- **[`bug`](#13-bug)**: Generates a unit test based on observed vs. desired program outputs.
- **[`auto-deps`](#14-auto-deps)**: Analyzes and inserts needed dependencies into a prompt file.
- **[`verify`](#15-verify)**: Verifies functional correctness by running a program and judging its output against the prompt's intent using an LLM.

## Global Options

These options can be used with any command:

- `--force`: Overwrite existing files without asking for confirmation.
- `--strength FLOAT`: Set the strength of the AI model (0.0 to 1.0, default is 0.5).
  - 0.0: Cheapest available model
  - 0.5: Default base model  
  - 1.0: Most powerful model (highest ELO rating)
- `--temperature FLOAT`: Set the temperature of the AI model (default is 0.0).
- `--verbose`: Increase output verbosity for more detailed information.
- `--quiet`: Decrease output verbosity for minimal information.
- `--output-cost PATH_TO_CSV_FILE`: Enable cost tracking and output a CSV file with usage details.
- `--review-examples`: Review and optionally exclude few-shot examples before command execution.
- `--local`: Run commands locally instead of in the cloud.

## Auto-Update Control

PDD automatically updates itself to ensure you have the latest features and security patches. However, you can control this behavior using the `PDD_AUTO_UPDATE` environment variable:

```bash
# Disable auto-updates
export PDD_AUTO_UPDATE=false

# Enable auto-updates (default behavior)
export PDD_AUTO_UPDATE=true
```

For persistent settings, add this environment variable to your shell's configuration file (e.g., `.bashrc` or `.zshrc`).

This is particularly useful in:
- Production environments where version stability is crucial
- CI/CD pipelines where consistent behavior is required
- Version-sensitive projects that require specific PDD versions

## AI Model Information

PDD uses a large language model to generate and manipulate code. The `--strength` and `--temperature` options allow you to control the model's output:

- Strength: Determines how powerful/expensive a model should be used. Higher values (closer to 1.0) result in high performance models with better capabilities (selected by ELO rating), while lower values (closer to 0.0) select more cost-effective models.
- Temperature: Controls the randomness of the output. Higher values increase diversity but may lead to less coherent results, while lower values produce more focused and deterministic outputs.

When running in local mode, PDD uses LiteLLM to select and interact with language models based on a configuration file that includes:
- Input and output costs per million tokens
- ELO ratings for coding ability
- Required API key environment variables
- Structured output capability flags
- Reasoning capabilities (budget-based or effort-based)

## Output Cost Tracking

PDD includes a feature for tracking and reporting the cost of operations. When enabled, it generates a CSV file with usage details for each command execution.

### Usage

To enable cost tracking, use the `--output-cost` option with any command:

```
pdd --output-cost PATH_TO_CSV_FILE [COMMAND] [OPTIONS] [ARGS]...
```

The `PATH_TO_CSV_FILE` should be the desired location and filename for the CSV output.

### Cost Calculation and Presentation

PDD calculates costs based on the AI model usage for each operation. Costs are presented in USD (United States Dollars) and are calculated using the following factors:

1. Model strength: Higher strength settings generally result in higher costs.
2. Input size: Larger inputs (e.g., longer prompts or code files) typically incur higher costs.
3. Operation complexity: Some operations (like `fix` and `crash` with multiple iterations) may be more costly than simpler operations.

The exact cost per operation is determined by the LiteLLM integration using the provider's current pricing model. PDD uses an internal pricing table that is regularly updated to reflect the most current rates.

### CSV Output

The generated CSV file includes the following columns:
- timestamp: The date and time of the command execution
- model: The AI model used for the operation
- command: The PDD command that was executed
- cost: The estimated cost of the operation in USD (e.g., 0.05 for 5 cents). This will be zero for local models or operations that do not use a LLM.
- input_files: A list of input files involved in the operation
- output_files: A list of output files generated or modified by the operation

This comprehensive output allows for detailed tracking of not only the cost and type of operations but also the specific files involved in each PDD command execution.

### Environment Variable

You can set a default location for the cost output CSV file using the environment variable:

- **`PDD_OUTPUT_COST_PATH`**: Default path for the cost tracking CSV file.

If this environment variable is set, the CSV file will be saved to the specified path by default, unless overridden by the `--output-cost` option. For example, if `PDD_OUTPUT_COST_PATH=/path/to/cost/reports/`, the CSV file will be saved in that directory with a default filename.

### Cost Budgeting

For commands that support it (like the `fix` command), you can set a maximum budget using the `--budget` option. This helps prevent unexpected high costs, especially for operations that might involve multiple AI model calls.

Example:
```
pdd [GLOBAL OPTIONS] fix --budget 5.0 [OTHER OPTIONS] [ARGS]...
```
This sets a maximum budget of $5.00 for the fix operation.

## Commands

Here are the main commands provided by PDD:

### 1. generate

Create runnable code from a prompt file. This command produces the full implementation code that fulfills all requirements in the prompt.

```bash
# Cloud execution (default)
pdd generate [OPTIONS] PROMPT_FILE

# Local execution
pdd --local generate [OPTIONS] PROMPT_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file used to generate the code.

Options:
- `--output LOCATION`: Specify where to save the generated code. The default file name is `<basename>.<language_file_extension>`. If an environment variable `PDD_GENERATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

**When to use**: Choose this command when implementing new functionality from scratch or creating comprehensive implementation details. Use this when you need the complete functional code that other code can use.

Example:
```
pdd [GLOBAL OPTIONS] generate --output src/factorial_calculator.py factorial_calculator_python.prompt 
```

### 2. example

Create a compact example demonstrating how to use functionality defined in a prompt. Similar to a header file or API documentation, this produces minimal, token-efficient code that shows the interface without implementation details.

```
pdd [GLOBAL OPTIONS] example [OPTIONS] PROMPT_FILE CODE_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file that generated the code.
- `CODE_FILE`: The filename of the existing code file.

Options:
- `--output LOCATION`: Specify where to save the generated example code. The default file name is `<basename>_example.<language_file_extension>`. If an environment variable `PDD_EXAMPLE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

**When to use**: Choose this command when creating reusable references that other prompts can efficiently import. This produces token-efficient examples that are easier to reuse across multiple prompts compared to including full implementations.

Example:
```
pdd [GLOBAL OPTIONS] example --output examples/factorial_calculator_example.py factorial_calculator_python.prompt src/factorial_calculator.py
```

### 3. test

Generate or enhance unit tests for a given code file and its corresponding prompt file.

```
pdd [GLOBAL OPTIONS] test [OPTIONS] PROMPT_FILE CODE_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file that generated the code.
- `CODE_FILE`: The filename of the code file to be tested.

Options:
- `--output LOCATION`: Specify where to save the generated test file. The default file name is `test_<basename>.<language_file_extension>`.
- `--language`: Specify the programming language. Defaults to the language specified by the prompt file name.
- `--coverage-report PATH`: Path to the coverage report file for existing tests. When provided, generates additional tests to improve coverage.
- `--existing-tests PATH`: Path to the existing unit test file. Required when using --coverage-report.
- `--target-coverage FLOAT`: Desired code coverage percentage to achieve (default is 90.0).
- `--merge`: When used with --existing-tests, merges new tests with existing test file instead of creating a separate file.

#### Providing Command-Specific Context

While prompts are the primary source of instructions, some PDD commands (like `test` and `example`) can be further guided by project-specific context files. These commands may automatically look for conventional files (e.g., `context/test.prompt`, `context/example.prompt`) in the current working directory during their internal prompt preprocessing phase.

If found, the content of these context files is included (using the `<include>` mechanism described in the `preprocess` section) into the internal prompt used by the command. This allows you to provide specific instructions tailored to your project, such as:

- Specifying required import statements.
- Suggesting preferred testing frameworks or libraries.
- Providing project-specific coding conventions or patterns.

**Example:** Creating a file named `context/test.prompt` with the content:
```
Please ensure all tests use the 'unittest' framework and import the main module as 'from my_module import *'.
```
could influence the output of the `pdd test` command when run in the same directory.

**Note:** This feature relies on the internal implementation of specific PDD commands incorporating the necessary `<include>` tags for these conventional context files. It is primarily used by `test` and `example` but may be adopted by other commands in the future. Check the specific command documentation or experiment to confirm if a command utilizes this pattern.

#### Basic Examples:

1. Generate initial unit tests:
```
pdd [GLOBAL OPTIONS] test --output tests/test_factorial_calculator.py factorial_calculator_python.prompt src/factorial_calculator.py
```

2. Generate additional tests to improve coverage:
```
pdd [GLOBAL OPTIONS] test --coverage-report coverage.xml --existing-tests tests/test_calculator.py --output tests/test_calculator_enhanced.py calculator_python.prompt src/calculator.py
```

3. Improve coverage and merge with existing tests:
```
pdd [GLOBAL OPTIONS] test --coverage-report coverage.xml --existing-tests tests/test_calculator.py --merge --target-coverage 95.0 calculator_python.prompt src/calculator.py
```

#### Coverage Analysis Strategy

When coverage options are provided, the test command will:
1. Analyze the coverage report to identify:
   - Uncovered lines and branches
   - Partially tested conditions
   - Missing edge cases

2. Generate additional test cases prioritizing:
   - Complex uncovered code paths
   - Error conditions
   - Boundary values
   - Integration points

3. Maintain consistency with:
   - Existing test style and patterns
   - Project's testing conventions
   - Original prompt's intentions

### 4. preprocess

Preprocess prompt files and save the results.

```
pdd [GLOBAL OPTIONS] preprocess [OPTIONS] PROMPT_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file to preprocess.

Options:
- `--output LOCATION`: Specify where to save the preprocessed prompt file. The default file name is `<basename>_<language>_preprocessed.prompt`.
- `--xml`: Automatically insert XML delimiters for long and complex prompt files to structure the content better. With this option prompts are only preprocessed to insert in XML delimiters, but not preprocessed otherwise.
- `--recursive`: Recursively preprocess all prompt files in the prompt file.
- `--double`: Curly brackets will be doubled.
- `--exclude`: List of keys to exclude from curly bracket doubling.

#### XML-like Tags

PDD supports the following XML-like tags in prompt files:

1. **`include`**: Includes the content of the specified file in the prompt. The tag is replaced directly with the file content.
   ```xml
   <include>./path/to/file.txt</include>
   ```
   This mechanism is also used internally by some commands (like `test` and `example`) to automatically incorporate project-specific context files if they exist in conventional locations (e.g., `context/test.prompt`). See 'Providing Command-Specific Context' for details.

2. **`pdd`**: Indicates a comment that will be removed from the preprocessed prompt, including the tags themselves.
   ```xml
   <pdd>This is a comment that won't appear in the preprocessed output</pdd>
   ```

3. **`shell`**: Executes shell commands and includes their output in the prompt, removing the shell tags.
   ```xml
   <shell>ls -la</shell>
   ```

4. **`web`**: Scrapes a web page and includes its markdown content in the prompt, removing the web tags.
   ```xml
   <web>https://example.com</web>
   ```

#### Triple Backtick Includes

PDD supports two ways of including external content:

1. **Triple backtick includes**: Replaces angle brackets in triple backticks with the content of the specified file.
   ````
   ```
   <./path/to/file.txt>
   ```
   This will be recursively processed until there are no more angle brackets in triple backticks.

2. **XML include tags**: As described above.

#### Curly Bracket Handling

When using the `--double` option:

- Single curly brackets are doubled if they're not already doubled
- Already doubled brackets are preserved
- Nested curly brackets are properly handled
- Special handling is applied for code blocks (JSON, JavaScript, TypeScript, Python)
- Multiline variables with curly brackets receive special handling

Use the `--exclude` option to specify keys that should be excluded from curly bracket doubling. This option **only applies** if the **entire string** inside a pair of single curly braces **exactly matches** one of the excluded keys.

For example, with `--exclude model`:
- `{model}` remains `{model}` (excluded due to exact match).
- `{model_name}` is doubled, as 'model_name' is not an exact match for 'model'.
- `{api_model}` is doubled, not an exact match.
- Braces containing other content, even if related to the key (e.g., `var={key}_value`), will generally still follow doubling rules unless the inner `{key}` itself is excluded.

Example command usage:
```
pdd [GLOBAL OPTIONS] preprocess --output preprocessed/factorial_calculator_python_preprocessed.prompt --recursive --double --exclude model,temperature factorial_calculator_python.prompt
```

### 5. fix

Fix errors in code and unit tests based on error messages and the original prompt file.

```
pdd [GLOBAL OPTIONS] fix [OPTIONS] PROMPT_FILE CODE_FILE UNIT_TEST_FILE ERROR_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file that generated the code under test.
- `CODE_FILE`: The filename of the code file to be fixed.
- `UNIT_TEST_FILE`: The filename of the unit test file.
- `ERROR_FILE`: The filename containing the unit test runtime error messages. Optional and does not need to exist when used with the `--loop` command.

Options:
- `--output-test LOCATION`: Specify where to save the fixed unit test file. The default file name is `test_<basename>_fixed.<language_file_extension>`. If an environment variable `PDD_FIX_TEST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-code LOCATION`: Specify where to save the fixed code file. The default file name is `<basename>_fixed.<language_file_extension>`. If an environment variable `PDD_FIX_CODE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-results LOCATION`: Specify where to save the results of the error fixing process. The default file name is `<basename>_fix_results.log`. If an environment variable `PDD_FIX_RESULTS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--loop`: Enable iterative fixing process.
  - `--verification-program PATH`: Specify the path to a Python program that verifies if the code still runs correctly.
  - `--max-attempts INT`: Set the maximum number of fix attempts before giving up (default is 3).
  - `--budget FLOAT`: Set the maximum cost allowed for the fixing process (default is $5.0).
- `--auto-submit`: Automatically submit the example if all unit tests pass during the fix loop.

When the `--loop` option is used, the fix command will attempt to fix errors through multiple iterations. It will use the specified verification program to check if the code runs correctly after each fix attempt. The process will continue until either the errors are fixed, the maximum number of attempts is reached, or the budget is exhausted.

Outputs:
- Fixed unit test file
- Fixed code file
- Results file containing the LLM model's output with unit test results.
- Print out of results when using '--loop' containing:
  - Success status (boolean)
  - Total number of fix attempts made
  - Total cost of all fix attempts
- This will also create intermediate versions of the unit test and code files for the different iterations with timestamp-based naming (e.g., `basename_1_0_3_0_20250402_124442.py`, `standalone_test_1_0_3_0_20250402_124442.py`).

Example:
```
pdd [GLOBAL OPTIONS] fix --output-test tests/test_factorial_calculator_fixed.py --output-code src/factorial_calculator_fixed.py --output-results results/factorial_fix_results.log factorial_calculator_python.prompt src/factorial_calculator.py tests/test_factorial_calculator.py errors.log
```
In this example, `factorial_calculator_python.prompt` is the prompt file that originally generated the code under test.

### 6. split

Split large complex prompt files into smaller, more manageable prompt files.

```
pdd [GLOBAL OPTIONS] split [OPTIONS] INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
```

Arguments:
- `INPUT_PROMPT`: The filename of the large prompt file to be split.
- `INPUT_CODE`: The filename of the code generated from the input prompt.
- `EXAMPLE_CODE`: The filename of the example code that serves as the interface to the sub-module prompt file.

Options:
- `--output-sub LOCATION`: Specify where to save the generated sub-prompt file. The default file name is `sub_<basename>.prompt`. If an environment variable `PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-modified LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd [GLOBAL OPTIONS] split --output-sub prompts/sub_data_processing.prompt --output-modified prompts/modified_main_pipeline.prompt data_processing_pipeline_python.prompt src/data_pipeline.py examples/pipeline_interface.py 
```

### 7. change

Modify an input prompt file based on a change prompt and the corresponding input code.

```
pdd [GLOBAL OPTIONS] change [OPTIONS] CHANGE_PROMPT_FILE INPUT_CODE [INPUT_PROMPT_FILE]
```

Arguments:
- `CHANGE_PROMPT_FILE`: The filename containing the instructions on how to modify the input prompt file.
- `INPUT_CODE`: The filename of the code that was generated from the input prompt file, or the directory containing the code files when used with the '--csv' option.
- `INPUT_PROMPT_FILE`: (Optional) The filename of the prompt file that will be modified. Not required when using the '--csv' option.

Options:
- `--output LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_CHANGE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--csv`: Use a CSV file for the change prompts instead of a single change prompt file. The CSV file should have columns: `prompt_name` and `change_instructions`. When this option is used, `INPUT_PROMPT_FILE` is not needed, and `INPUT_CODE` should be the directory where the code files are located. The command expects prompt names in the CSV to follow the `<basename>_<language>.prompt` convention. For each `prompt_name` in the CSV, it will look for the corresponding code file (e.g., `<basename>.<language_extension>`) within the specified `INPUT_CODE` directory. Output files will overwrite existing files unless `--output LOCATION` is specified. If `LOCATION` is a directory, the modified prompt files will be saved inside this directory using the default naming convention otherwise, if a csv filename is specified the modified prompts will be saved in that CSV file with columns 'prompt_name' and 'modified_prompt'.

Example (single prompt change):
```
pdd [GLOBAL OPTIONS] change --output modified_factorial_calculator_python.prompt changes_factorial.prompt src/factorial_calculator.py factorial_calculator_python.prompt
```

Example (batch change using CSV):
```
pdd [GLOBAL OPTIONS] change --csv --output modified_prompts/ changes_batch.csv src/
```

### 8. update

Update the original prompt file based on the modified code and optionally the original code.

```
pdd [GLOBAL OPTIONS] update [OPTIONS] INPUT_PROMPT_FILE MODIFIED_CODE_FILE [INPUT_CODE_FILE]
```

Arguments:
- `INPUT_PROMPT_FILE`: The filename of the prompt file that generated the original code.
- `MODIFIED_CODE_FILE`: The filename of the code that was modified by the user.
- `INPUT_CODE_FILE`: (Optional) The filename of the original code that was generated from the input prompt file. This argument is not required when using the `--git` option.

Options:
- `--output LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_UPDATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--git`: Use git history to find the original code file, eliminating the need for the `INPUT_CODE_FILE` argument.

Example:
```
pdd [GLOBAL OPTIONS] update --output updated_factorial_calculator_python.prompt factorial_calculator_python.prompt src/modified_factorial_calculator.py src/original_factorial_calculator.py
```

Example using the `--git` option:
```
pdd [GLOBAL OPTIONS] update --git --output updated_factorial_calculator_python.prompt factorial_calculator_python.prompt src/modified_factorial_calculator.py
```

### 9. detect

Analyze a list of prompt files and a change description to determine which prompts need to be changed.

```
pdd [GLOBAL OPTIONS] detect [OPTIONS] PROMPT_FILES... CHANGE_FILE
```

Arguments:
- `PROMPT_FILES`: A list of filenames of prompts that may need to be changed.
- `CHANGE_FILE`: Filename whose content describes the changes that need to be analyzed and potentially applied to the prompts.

Options:
- `--output LOCATION`: Specify where to save the CSV file containing the analysis results. The default file name is `<change_file_basename>_detect.csv`.  If an environment variable `PDD_DETECT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd [GLOBAL OPTIONS] detect --output detect_results.csv factorial_calculator_python.prompt data_processing_python.prompt web_scraper_python.prompt changes_description.prompt
```

### 10. conflicts

Analyze two prompt files to find conflicts between them and suggest how to resolve those conflicts.

```
pdd [GLOBAL OPTIONS] conflicts [OPTIONS] PROMPT1 PROMPT2
```

Arguments:
- `PROMPT1`: First prompt in the pair of prompts we are comparing.
- `PROMPT2`: Second prompt in the pair of prompts we are comparing.

Options:
- `--output LOCATION`: Specify where to save the CSV file containing the conflict analysis results. The default file name is `<prompt1_basename>_<prompt2_basename>_conflict.csv`.  If an environment variable `PDD_CONFLICTS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd [GLOBAL OPTIONS] conflicts --output conflicts_analysis.csv data_processing_module_python.prompt data_visualization_module_python.prompt 
```

Both the `detect` and `conflicts` commands generate a csv file with the following columns: `prompt_name` and `change_instructions`. This csv file can be used as input for the `change --csv` command.

### 11. crash

Fix errors in a code module and its calling program that caused a program to crash.

```
pdd [GLOBAL OPTIONS] crash [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE
```

Arguments:
- `PROMPT_FILE`: Filename of the prompt file that generated the code module.
- `CODE_FILE`: Filename of the code module that caused the crash and will be modified so it runs properly.
- `PROGRAM_FILE`: Filename of the program that was running the code module. This file will also be modified if necessary to fix the crash.
- `ERROR_FILE`: Filename of the file containing the errors from the program run.

Options:
- `--output LOCATION`: Specify where to save the fixed code file. The default file name is `<basename>_fixed.<language_extension>`. If an environment variable `PDD_CRASH_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-program LOCATION`: Specify where to save the fixed program file. The default file name is `<program_basename>_fixed.<language_extension>`.
- `--loop`: Enable iterative fixing process.
  - `--max-attempts INT`: Set the maximum number of fix attempts before giving up (default is 3).
  - `--budget FLOAT`: Set the maximum cost allowed for the fixing process (default is $5.0).

When the `--loop` option is used, the crash command will attempt to fix errors through multiple iterations. It will use the program to check if the code runs correctly after each fix attempt. The process will continue until either the errors are fixed, the maximum number of attempts is reached, or the budget is exhausted.

Example:
```
pdd [GLOBAL OPTIONS] crash --output fixed_data_processor.py --output-program fixed_main_pipeline.py data_processing_module_python.prompt crashed_data_processor.py main_pipeline.py crash_errors.log
```

Example with loop option:
```
pdd [GLOBAL OPTIONS] crash --loop --max-attempts 5 --budget 10.0 --output fixed_data_processor.py --output-program fixed_main_pipeline.py data_processing_module_python.prompt crashed_data_processor.py main_pipeline.py crash_errors.log
```

### 12. trace

Fine the associated line number between a prompt file and the generated code.

```
pdd [GLOBAL OPTIONS] trace [OPTIONS] PROMPT_FILE CODE_FILE CODE_LINE
```

Arguments:
- `PROMPT_FILE`: Filename of the prompt file that generated the code.
- `CODE_FILE`: Filename of the code file to be analyzed.
- `CODE_LINE`: Line number in the code file that the debugger trace line is on.

Options:
- `--output LOCATION`: Specify where to save the trace analysis results. The default file name is `<basename>_trace_results.log`.

Example:
```
pdd [GLOBAL OPTIONS] trace --output trace_results.log factorial_calculator_python.prompt src/factorial_calculator.py
```

This will print out the line number in the prompt file for the associated the code line.

### 13. bug

Generate a unit test based on observed and desired outputs, given the original prompt and code.

```
pdd [GLOBAL OPTIONS] bug [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE CURRENT_OUTPUT_FILE DESIRED_OUTPUT_FILE
```

Arguments:
- `PROMPT_FILE`: Filename of the prompt file that generated the code.
- `CODE_FILE`: Filename of the code file being tested.
- `PROGRAM_FILE`: Filename of the program used to run the code under test.
- `CURRENT_OUTPUT_FILE`: File containing the current (incorrect) output of the program.
- `DESIRED_OUTPUT_FILE`: File containing the desired (correct) output of the program.

Options:
- `--output LOCATION`: Specify where to save the generated unit test. The default file name is `test_<basename>_bug.<language_extension>`.
- `--language`: Specify the programming language for the unit test (default is "Python").

Example:
```
pdd [GLOBAL OPTIONS] bug --output tests/test_factorial_calculator_bug.py factorial_calculator_python.prompt src/factorial_calculator.py main_program.py current_output.txt desired_output.txt
```

### 14. auto-deps

Analyze a prompt file and a directory of potential dependencies to determine and insert needed dependencies into the prompt.

```
pdd [GLOBAL OPTIONS] auto-deps [OPTIONS] PROMPT_FILE DIRECTORY_PATH
```

Arguments:
- `PROMPT_FILE`: Filename of the prompt file that needs dependencies analyzed and inserted.
- `DIRECTORY_PATH`: Path to the directory containing potential dependency files (should include glob patterns, e.g., "context/*_example.py").

Options:
- `--output LOCATION`: Specify where to save the modified prompt file with dependencies inserted. The default file name is `<basename>_with_deps.prompt`. If an environment variable `PDD_AUTO_DEPS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--csv FILENAME`: Specify the CSV file that contains or will contain dependency information. Default is "project_dependencies.csv". If the environment variable`PDD_AUTO_DEPS_CSV_PATH` is set, that path will be used unless overridden by this option.
- `--force-scan`: Force rescanning of all potential dependency files even if they exist in the CSV file.

The command maintains a CSV file with the following columns:
- `full_path`: The full path to the dependency file
- `file_summary`: A concise summary of the file's content and purpose
- `date`: Timestamp of when the file was last analyzed

Example:
```
pdd [GLOBAL OPTIONS] auto-deps --output prompts/data_pipeline_with_deps.prompt --csv project_deps.csv data_processing_pipeline_python.prompt "context/*_example.py"
```

### 15. verify

Verifies the functional correctness of generated code by executing a specified program (often the output of the `example` command) and using an LLM to judge the program's output against the original prompt's intent. No separate expected output file is needed; the LLM determines if the behavior aligns with the prompt requirements. If verification fails, it iteratively attempts to fix the code based on the judged discrepancy, similar to how `fix` and `crash` operate with their respective error signals.

```bash
pdd [GLOBAL OPTIONS] verify [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE
```

Arguments:
- `PROMPT_FILE`: Filename of the prompt file that generated the code being verified.
- `CODE_FILE`: Filename of the code file to be verified and potentially fixed.
- `PROGRAM_FILE`: Filename of the executable program to run for verification (e.g., the example script generated by `pdd example`). The output of this program run will be judged by the LLM.

Options:
- `--output-results LOCATION`: Specify where to save the verification and fixing results log. This log typically contains the final status (pass/fail), number of attempts, total cost, and potentially LLM reasoning or identified issues. Default: `<basename>_verify_results.log`. If an environment variable `PDD_VERIFY_RESULTS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-code LOCATION`: Specify where to save the successfully verified (and potentially fixed) code file. Default: `<basename>_verified.<language_extension>`. If an environment variable `PDD_VERIFY_CODE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-program LOCATION`: Specify where to save the successfully verified (and potentially fixed) program file. The default file name is `<program_basename>_verified.<language_extension>`. If an environment variable `PDD_VERIFY_PROGRAM_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--max-attempts INT`: Set the maximum number of fix attempts within the verification loop before giving up (default is 3).
- `--budget FLOAT`: Set the maximum cost allowed for the entire verification and iterative fixing process (default is $5.0).

The command operates iteratively if the initial run of `PROGRAM_FILE` produces output judged incorrect by the LLM based on the `PROMPT_FILE`. After each fix attempt on `CODE_FILE`, `PROGRAM_FILE` is re-run, and its output is re-evaluated. This continues until the output is judged correct, `--max-attempts` is reached, or the `--budget` is exhausted. Intermediate code files may be generated during the loop, similar to the `fix` command.

Outputs:
- Verified (and potentially fixed) code file at `--output-code` location upon success.
- Verified (and potentially fixed) program file at `--output-program` location upon success.
- Results log file at `--output-results` location detailing the process and outcome.
- Potentially intermediate code files generated during the fixing loop (timestamp-based naming).

Example:
```bash
# Verify calc.py by running examples/run_calc.py, judging its output against prompts/calc_py.prompt
# Attempt to fix up to 5 times with a $2.50 budget if verification fails.
pdd verify --max-attempts 5 --budget 2.5 --output-code src/calc_verified.py --output-results results/calc_verify.log prompts/calc_py.prompt src/calc.py examples/run_calc.py
```

**When to use**: Use `verify` after `generate` and `example` for an initial round of functional validation and automated fixing based on *LLM judgment of program output against the prompt*. This helps ensure the code produces results aligned with the prompt's intent for a key scenario before proceeding to more granular unit testing (`test`) or fixing specific runtime errors (`crash`) or unit test failures (`fix`).

## Example Review Process

When the global `--review-examples` option is used with any command, PDD will present potential few-shot examples that might be used for the current operation. The review process follows these steps:

1. PDD displays the inputs (but not the outputs) of potential few-shot examples.
2. For each example, you can choose to:
   - Accept the example (it will be used in the operation)
   - Exclude the example (it won't be used in this or future operations)
   - Skip the example (it won't be used in this operation but may be presented again in the future)
3. After reviewing all presented examples, PDD will proceed with the command execution using the accepted examples.

This feature allows you to have more control over the examples used in PDD operations, potentially improving the quality and relevance of the generated outputs.

## Automatic Example Submission

When using the `fix` command with the `--auto-submit` option, PDD will automatically submit the example to the PDD Cloud platform if all unit tests pass during the fix loop. This feature helps to continuously improve the platform's example database with successful fixes.

## Output Location Specification

For all commands that generate or modify files, the `--output` option (or its variant, such as `--output-sub` or `--output-modified` for the `split` command) allows flexible specification of the output location:

1. **Filename only**: If you provide just a filename (e.g., `--output result.py`), the file will be created in the current working directory.
2. **Full path**: If you provide a full path (e.g., `--output /home/user/projects/result.py`), the file will be created at that exact location.
3. **Directory**: If you provide a directory name (e.g., `--output ./generated/`), a file with an automatically generated name will be created in that directory.
4. **Environment Variable**: If the `--output` option is not provided, and an environment variable specific to the command is set, PDD will use the path specified by this variable. Otherwise, it will use default naming conventions and save the file in the current working directory.
5. **No Output Location**: If no output location is specified and no environment variable is set, the file will be saved in the current working directory with a default name given the command.

## Multi-Command Chaining

PDD supports multi-command chaining, allowing you to execute multiple commands in a single line. Commands will be executed in the order they are specified. This feature enables you to perform complex workflows efficiently, combining various PDD operations into a single, streamlined process.

Basic syntax for multi-command chaining:
```
pdd [GLOBAL OPTIONS] COMMAND1 [OPTIONS] [ARGS]... [COMMAND2 [OPTIONS] [ARGS]...]...
```

## Getting Help

PDD provides comprehensive help features:

1. **General Help**:
   ```
   pdd --help
   ```
   Displays a list of available commands and options.

2. **Command-Specific Help**:
   ```
   pdd COMMAND --help
   ```
   Provides detailed help for a specific command, including available options and usage examples.

## Additional Features

- **Tab Completion**: PDD supports tab completion for commands and options in compatible shells. You can install tab completion by running:
  ```
  pdd install_completion
  ```
- **Colorized Output**: PDD provides colorized output for better readability in compatible terminals.


## Environment Variables

PDD uses several environment variables to customize its behavior:

### Core Environment Variables

- **`PDD_PATH`**: Points to the root directory of PDD. This is automatically set during pip installation to the directory where PDD is installed. You typically don't need to set this manually.
- **`PDD_AUTO_UPDATE`**: Controls whether PDD automatically updates itself (default: true).

### Output Path Variables

- **`PDD_GENERATE_OUTPUT_PATH`**: Default path for the `generate` command.
- **`PDD_EXAMPLE_OUTPUT_PATH`**: Default path for the `example` command.
- **`PDD_TEST_OUTPUT_PATH`**: Default path for the unit test file.
- **`PDD_TEST_COVERAGE_TARGET`**: Default target coverage percentage.
- **`PDD_PREPROCESS_OUTPUT_PATH`**: Default path for the `preprocess` command.
- **`PDD_FIX_TEST_OUTPUT_PATH`**: Default path for the fixed unit test files in the `fix` command.
- **`PDD_FIX_CODE_OUTPUT_PATH`**: Default path for the fixed code files in the `fix` command.
- **`PDD_FIX_RESULTS_OUTPUT_PATH`**: Default path for the results file generated by the `fix` command.
- **`PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH`**: Default path for the sub-prompts generated by the `split` command.
- **`PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH`**: Default path for the modified prompts generated by the `split` command.
- **`PDD_CHANGE_OUTPUT_PATH`**: Default path for the modified prompts generated by the `change` command.
- **`PDD_UPDATE_OUTPUT_PATH`**: Default path for the updated prompts generated by the `update` command.
- **`PDD_OUTPUT_COST_PATH`**: Default path for the cost tracking CSV file.
- **`PDD_DETECT_OUTPUT_PATH`**: Default path for the CSV file generated by the `detect` command.
- **`PDD_CONFLICTS_OUTPUT_PATH`**: Default path for the CSV file generated by the `conflicts` command.
- **`PDD_CRASH_OUTPUT_PATH`**: Default path for the fixed code file generated by the `crash` command.
- **`PDD_CRASH_PROGRAM_OUTPUT_PATH`**: Default path for the fixed program file generated by the `crash` command.
- **`PDD_TRACE_OUTPUT_PATH`**: Default path for the trace analysis results generated by the `trace` command.
- **`PDD_BUG_OUTPUT_PATH`**: Default path for the unit test file generated by the `bug` command.
- **`PDD_AUTO_DEPS_OUTPUT_PATH`**: Default path for the modified prompt files generated by the `auto-deps` command.
- **`PDD_AUTO_DEPS_CSV_PATH`**: Default path and filename for the CSV file used by the auto-deps command to store dependency information. If set, this overrides the default "project_dependencies.csv" filename.
- **`PDD_VERIFY_RESULTS_OUTPUT_PATH`**: Default path for the results log file generated by the `verify` command.
- **`PDD_VERIFY_CODE_OUTPUT_PATH`**: Default path for the verified code file generated by the `verify` command upon success.
- **`PDD_VERIFY_PROGRAM_OUTPUT_PATH`**: Default path for the verified program file generated by the `verify` command upon success.


### Model Configuration (`llm_model.csv`)

PDD uses a CSV file (`llm_model.csv`) to store information about available AI models, their costs, capabilities, and required API key names. When running commands locally (e.g., using the `update_model_costs.py` utility or potentially local execution modes if implemented), PDD determines which configuration file to use based on the following priority:

1.  **User-specific:** `~/.pdd/llm_model.csv` - If this file exists, it takes precedence over any project-level configuration. This allows users to maintain a personal, system-wide model configuration.
2.  **Project-specific:** `<PROJECT_ROOT>/data/llm_model.csv` - If the user-specific file is not found, PDD looks for the file within the `data` directory of the determined project root (based on `PDD_PATH` or auto-detection).

This tiered approach allows for both shared project configurations and individual user overrides.
*Note: This file-based configuration primarily affects local operations and utilities. Cloud execution modes likely rely on centrally managed configurations.*


These environment variables allow you to set default output locations for each command. If an environment variable is set and the corresponding `--output` option is not used in the command, PDD will use the path specified by the environment variable. This can help streamline your workflow by reducing the need to specify output paths for frequently used commands.

For example, if you set `PDD_GENERATE_OUTPUT_PATH=/path/to/generated/code/`, all files created by the `generate` command will be saved in that directory by default, unless overridden by the `--output` option in the command line.

To set these environment variables, you can add them to your shell configuration file (e.g., `.bashrc` or `.zshrc`) or set them before running PDD commands:

```bash
export PDD_GENERATE_OUTPUT_PATH=/path/to/generated/code/
export PDD_TEST_OUTPUT_PATH=/path/to/tests/
# ... set other variables as needed

pdd generate factorial_calculator_python.prompt  # Output will be saved in /path/to/generated/code/
```

This feature allows for more flexible and customized setups, especially in team environments or when working across multiple projects with different directory structures.

## Error Handling

PDD provides informative error messages when issues occur during command execution. Common error scenarios include:

- Invalid input files or formats
- Insufficient permissions to read/write files
- AI model-related errors (e.g., API failures)
- Syntax errors in generated code

When an error occurs, PDD will display a message describing the issue and, when possible, suggest steps to resolve it.

## Cloud Features

When running in cloud mode (default), PDD provides additional features:

1. **Shared Examples**: Access to a growing database of community-contributed examples
2. **Automatic Updates**: Latest improvements and bug fixes are automatically available
3. **Cost Optimization**: Smart model selection and caching to minimize costs
4. **Usage Analytics**: Track your team's usage and costs through the PDD Cloud dashboard
5. **Collaboration**: Share prompts and generated code with team members

To access the PDD Cloud dashboard: https://promptdriven.ai/

Here you can:
- View usage statistics
- Manage team access
- Configure default settings
- Access shared examples
- Track costs

## Troubleshooting

Here are some common issues and their solutions:

1. **Command not found**: Ensure PDD is properly installed and added to your system's PATH.

2. **Permission denied errors**: Check that you have the necessary permissions to read input files and write to output locations.

3. **AI model not responding**: Verify your internet connection and check the status of the AI service.

4. **Unexpected output**: Try adjusting the `--strength` and `--temperature` parameters to fine-tune the AI model's behavior.

5. **High costs**: Use the `--output-cost` option to track usage and set appropriate budgets for the `fix` command's `--budget` option.

6. **Dependency scanning issues**: If the `auto-deps` command fails to identify relevant dependencies:
   - Check that the file paths and glob patterns are correct
   - Use the `--force-scan` option to ensure all files are re-analyzed
   - Verify the CSV file format and content
   - Check file permissions for the dependency directory

7. **Command Timeout**:
   - Check internet connection
   - Try running with `--local` flag to compare
   - If persistent, check PDD Cloud status page

If you encounter persistent issues, consult the PDD documentation or post an issue on GitHub for assistance.

## Security Considerations

When using PDD, keep the following security considerations in mind:

1. **Code Execution**: PDD generates and modifies code. Always review generated code before execution, especially in production environments.

2. **Data Privacy**: Avoid using sensitive data in prompts or code files, as this information may be processed by the AI model.

3. **API Keys**: If PDD requires API keys for AI model access, store these securely and never include them in version control systems.

4. **Input Validation**: PDD assumes input files are trustworthy. Implement proper input validation if using PDD in a multi-user or networked environment.

5. **Output Handling**: Treat output files with the same security considerations as you would any other code or configuration files in your project.

6. **Dependency Analysis**: When using the `auto-deps` command, be cautious with untrusted dependency files and verify the generated summaries before including them in your prompts.

When using PDD in cloud mode:

1. **Authentication**: 
   - PDD uses GitHub SSO for secure authentication
   - Tokens are stored securely in your system's credential manager
   - No need to manage API keys manually

2. **Data Privacy**:
   - All data is encrypted in transit and at rest
   - Prompts and generated code are associated only with your account
   - You can delete your data at any time through the dashboard

3. **Team Access**:
   - Manage team member access through GitHub organizations
   - Set up fine-grained permissions for different commands
   - Track usage per team member

Additionally:
- Consider disabling auto-updates in production environments using `PDD_AUTO_UPDATE=false`
- Implement a controlled update process for production systems
- Review changelogs before manually updating PDD in sensitive environments

## Workflow Integration

PDD can be integrated into various development workflows. Here are the conceptual models for key workflow patterns:

### Initial Development

**Conceptual Flow**: `auto-deps → generate → example → crash → verify → test → fix`

**Purpose**: Create new functionality from scratch with proper testing and verification.

**Process**:
1. Identify and inject dependencies for your prompt (`auto-deps`).
2. Generate full implementation code from the prompt (`generate`).
3. Create reusable interface examples (`example`).
4. Ensure the code runs without crashing and fix runtime errors (`crash`).
5. Run the example and use an LLM to check if the output aligns with the prompt's intent, attempting iterative fixes if necessary (`verify`).
6. Generate comprehensive unit tests for the implementation (`test`).
7. Fix any issues revealed by the unit tests (`fix`).

**Key Insight**: This workflow follows a progression from concept to verified implementation, ensuring the code runs (`crash`) before checking functional output (`verify`) and detailed unit testing (`test`).

### Code-to-Prompt Update

**Conceptual Flow**: `update → detect → change`

**Purpose**: Maintain prompt as source of truth after code changes.

**Process**:
1. Synchronize direct code changes back to the original prompt
2. Detect other prompts that might be affected by these changes
3. Apply necessary changes to dependent prompts

**Key Insight**: This bidirectional flow ensures prompts remain the source of truth even when code changes happen first.

### Refactoring

**Conceptual Flow**: `split → auto-deps → example`

**Purpose**: Break large prompts into modular components.

**Process**:
1. Extract specific functionality from a large prompt into a separate prompt
2. Ensure the new prompt has all dependencies it needs
3. Create interface examples for the extracted functionality

**Key Insight**: Just as code should be modular, prompts benefit from decomposition into focused, reusable components.

### Debugging Workflows

#### Prompt Context Issues
**Conceptual Flow**: `preprocess → generate`

**Purpose**: Resolve issues with prompt interpretation or preprocessing.

**Process**:
1. Examine how the prompt is being preprocessed
2. Regenerate code with improved prompt clarity

#### Runtime Crash Debugging
**Conceptual Flow**: `generate → example → crash`

**Purpose**: Fix code that fails to execute.

**Process**:
1. Generate initial code from prompt
2. Create examples and test programs
3. Fix runtime errors to make code executable

#### Logical Bug Fixing
**Conceptual Flow**: `bug → fix`

**Purpose**: Correct code that runs but produces incorrect results.

**Process**:
1. Generate test cases that demonstrate the bug
2. Fix the code to pass the tests

#### Debugger-Guided Analysis
**Conceptual Flow**: `trace → [edit prompt]`

**Purpose**: Identify which prompt sections produce problematic code.

**Process**:
1. Locate the relationship between code lines and prompt sections
2. Update relevant prompt sections

### Multi-Prompt Architecture

**Conceptual Flow**: `conflicts/detect → change → generate → example → test`

**Purpose**: Coordinate multiple prompts derived from higher-level requirements.

**Process**:
1. Identify conflicts or dependencies between prompts
2. Harmonize the prompts to work together
3. Regenerate code from updated prompts
4. Update interface examples after changes
5. Verify system integration with tests

**Key Insight**: Complex systems require coordination between prompts, just as they do between code modules.

### Feature Enhancement

**Conceptual Flow**: `change → generate → example → test → fix`

**Purpose**: Add new capabilities to existing functionality.

**Process**:
1. Modify prompts to describe new features
2. Regenerate code with enhanced functionality
3. Update examples to demonstrate new features
4. Test to verify correct implementation
5. Fix any issues that arise

**Key Insight**: Feature additions should flow from prompt changes rather than direct code modifications.

### Critical Dependencies

When using these workflows, remember these crucial tool dependencies:

- 'generate' must be done before 'example' or 'test'
- 'crash' is used to fix runtime errors and make code runnable
- 'fix' requires runnable code created/verified by 'crash'
- 'test' must be created before using 'fix'
- Always update 'example' after major prompt interface changes

For detailed command examples for each workflow, see the respective command documentation sections.

## Integrations

PDD offers integrations to streamline its use within your development environment:

### VS Code Extension

A dedicated VS Code extension (`utils/vscode_prompt`) provides syntax highlighting, snippets, and potentially other features for working with `.prompt` files directly within the editor. Refer to the [extension's README](utils/vscode_prompt/README.md) for installation and usage details.

### MCP Server (for Agentic Clients)

The `pdd-mcp-server` (`utils/mcp`) acts as a bridge using the Model Context Protocol (MCP). This allows agentic clients like Cursor, Claude Desktop, Continue.dev, and others to invoke `pdd-cli` commands programmatically. See the [MCP Server README](utils/mcp/README.md) for configuration and usage instructions.

## Utilities

### Update LLM Model Data (`pdd/update_model_costs.py`)

This script automatically updates the `llm_model.csv` file. **It prioritizes updating the user-specific configuration at `~/.pdd/llm_model.csv` if it exists.** Otherwise, it targets the file specified by the `--csv-path` argument (defaulting to `<PROJECT_ROOT>/data/llm_model.csv`).

It uses the `litellm` library to:
*   Fetch and fill in missing input/output costs for listed models (converting per-token costs to per-million-token costs).
*   Compare existing costs against LiteLLM data and report mismatches (without overwriting).
*   Check and update the `structured_output` flag (True/False) based on `litellm.supports_response_schema`.
*   Validate model identifiers using `litellm` before processing.

**Usage:**

```bash
conda activate pdd
# The script will automatically check ~/.pdd/llm_model.csv first.
# If not found, it will use the path given by --csv-path (or the default project path).
python pdd/update_model_costs.py [--csv-path path/to/your/project/llm_model.csv]
```

*Note: The `max_reasoning_tokens` column requires manual maintenance.*

## Conclusion

PDD (Prompt-Driven Development) CLI provides a comprehensive set of tools for managing prompt files, generating code, creating examples, running tests, and handling various aspects of prompt-driven development. By leveraging the power of AI models and iterative processes, PDD aims to streamline the development workflow and improve code quality.

The various commands and options allow for flexible usage, from simple code generation to complex workflows involving multiple steps. The ability to track costs, manage output locations through environment variables, and chain multiple commands further enhances the tool's utility in different development environments.

With the consistent argument order placing prompt files first, PDD emphasizes its prompt-driven nature and provides a more intuitive interface for users. This consistency across commands should make the tool easier to learn and use effectively.

As you become more familiar with PDD, you can create more complex workflows by chaining multiple commands and utilizing the full range of options available. Always refer to the latest documentation and use the built-in help features to make the most of PDD in your development process.

Remember to stay mindful of security considerations, especially when working with generated code or sensitive data. Regularly update PDD to access the latest features and improvements.

Happy coding with PDD!