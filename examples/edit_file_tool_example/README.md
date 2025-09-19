# PDD-Powered Project Generation: Simplified Sync Approach

This document demonstrates using PDD (Prompt-Driven Development) to automatically generate the `edit-file-tool` project using a streamlined **`pdd sync`** workflow. This example shows how an entire working Python project can be generated from prompts using PDD's simplified sync command.

## Core Concepts

The approach uses **`pdd sync`** as the primary command with a straightforward workflow:

- **`prompts/{component}_python.prompt`**: Your component specification - the source of truth
- **`pdd sync {component} --force`**: The single command that handles the complete workflow
- **Simple Execution**: Streamlined process that runs sync with force flag to ensure regeneration
- **Clean Workflow**: Setup → Generate Prompts → Build Components → Test

## The PDD Sync Command: Simplified Approach

The **`pdd sync`** command is the primary workflow command for PDD. It executes the complete development cycle in a streamlined manner.

### What Sync Does

When you run `pdd sync {component} --force`, it automatically handles:

1. **Dependency Analysis**: Identifies and includes necessary project dependencies
2. **Code Generation**: Creates or updates the main code module from the prompt  
3. **Example Creation**: Generates usage examples showing the interface
4. **Runtime Validation**: Ensures the code executes without errors
5. **Functional Verification**: Validates behavior matches prompt intent
6. **Test Generation**: Creates comprehensive unit tests
7. **Bug Fixing**: Resolves any issues found during testing
8. **Documentation Updates**: Updates prompts based on learnings

### Key Features

- **Force Regeneration**: The `--force` flag ensures clean rebuilds
- **Automatic Workflow**: Complete pipeline from prompt to tested code
- **Simple Execution**: One command handles the entire process
- **Integrated Testing**: Built-in test generation and validation

## How to Build the Project

Follow these streamlined steps to generate the `edit-file-tool` using the sync-first approach.

### Prerequisites

- You have `pdd` installed and configured (e.g., via `infisical run -- pdd`)
- You have Python and `pytest` installed
- You are in the `examples/edit_file_tool_example` directory

### Step 1: Set Up the Directory Structure

Create the required folders for the project:

```bash
make setup
```

This creates the `edit_file_tool/`, `tests/`, `logs/`, `cost_reports/`, and `prompts/` directories.

### Step 2: Generate the Project Blueprint

Generate the `tool_ordered.json` file that defines the components and build order:

```bash
make tool_list
```

This creates `tool.json` and `tool_ordered.json` using PDD generation commands.

### Step 3: Generate Component Prompts

Create customized prompts for each component:

```bash
make prompts
```

This runs `prompts_script.py` to create refined prompts in `prompts/edit_file_tool_prompts/`.

**Important**: Review the generated prompts before proceeding to catch any issues early.

### Step 4: Build All Components with Sync

This is the main step where **`pdd sync`** generates and tests all code:

```bash
make build_all_components
```

or simply:

```bash
make all
```

Each component goes through the complete sync workflow automatically.

### Building Individual Components

Build or rebuild a single component:

```bash
make component utils.py
```

For a clean rebuild (deleting existing files first):

```bash
make component utils.py --clean
```

Or call the workflow directly:

```bash
python Scripts/PDD_workflow.py utils --clean
```

## PDD_workflow.py: Simplified Implementation

The `PDD_workflow.py` script provides a streamlined wrapper around the `pdd sync` command:

### Core Functionality

```python
EXECUTION_MODE = 'execute'      # Set to 'print' to show commands without executing
ENABLE_LOGGING = False          # Set to True to create sync log files
ENABLE_COST_TRACKING = False    # Set to True to enable cost tracking
USE_INFISICAL = False           # Set to True to use infisical wrapper
```

### Key Operations

1. **Validates** that the prompt file exists (`prompts/{component}_python.prompt`)
2. **Executes** `pdd --local --force sync {component}` 
3. **Creates** command log file for tracking (`make_creation/{component}/cmd_{component}.txt`)
4. **Cleans up** temporary files generated during sync process
5. **Ensures** proper package structure with `__init__.py`

### Generated Files

For each component, the workflow creates:

- **`edit_file_tool/{component}.py`**: Main implementation code
- **`examples/{component}_example.py`**: Usage examples  
- **`tests/test_{component}.py`**: Comprehensive unit tests
- **Command logs**: Track what commands were executed

## Makefile Integration

The `Makefile` provides a streamlined build system for the PDD workflow:

### Core Targets

- **`make setup`**: Creates directory structure (edit_file_tool/, tests/, logs/, etc.)
- **`make arch_list`**: Generates architecture.json component specifications
- **`make prompts`**: Creates component prompts from architecture.json  
- **`make build_all_components`**: Builds all components using PDD sync
- **`make all`**: Complete workflow (setup → arch_list → prompts → build_all_components)

### Component Building

- **`make component <filename>`**: Builds specific component (automatically cleans first)
- **`make component <file1> <file2>`**: Builds multiple specified components
- **`make component all`**: Alternative way to build all components

### Configuration Variables

Control the build process with these make variables:

```bash
# PDD execution mode
make USE_INFISICAL=no USE_LOCAL=yes component utils    # Direct pdd --local
make USE_INFISICAL=yes USE_LOCAL=no component utils    # infisical run -- pdd

# Component building options  
make CLEAN_COMPONENTS=yes component utils              # Enable --clean flag
make CLEAN_COMPONENTS=no component utils               # Disable --clean flag

# Combined configuration
make USE_INFISICAL=no USE_LOCAL=yes CLEAN_COMPONENTS=yes component utils
```

### Build Process

The Makefile integrates with `Scripts/PDD_workflow.py` to:
1. Validate prompt files exist
2. Execute `pdd sync` with appropriate flags
3. Clean up temporary files
4. Create command execution logs

## Makefile Commands Reference

### Essential Commands

#### `make all`
**Complete project build pipeline**
```bash
make all
```
Executes: setup → arch_list → prompts → build_all_components

#### `make setup`
**Create project directory structure**
```bash
make setup
```
Creates: edit_file_tool/, tests/, logs/, cost_reports/, prompts/, examples/

#### `make arch_list`
**Generate component architecture specification**
```bash
make arch_list
```
- Generates `pdd/architecture.json` from `prompts/architecture_json.prompt`
- Creates cost tracking in `cost_reports/tool_track.csv`
- Logs output to `logs/architecture_json.log`

#### `make prompts`
**Generate component prompts from architecture**
```bash
make prompts
```
- Requires `pdd/architecture.json` (run `make arch_list` first)
- Executes `Scripts/prompts_script.py`
- Creates individual `{component}_python.prompt` files in `prompts/`

#### `make architecture`
**Display available components**
```bash
make architecture
```
Shows list of components from `pdd/architecture.json` with their purposes

### Component Building

#### `make component <name>`
**Build specific component(s)**
```bash
# Single component
make component cli

# Multiple components
make component cli utils core

# All components (alternative to build_all_components)
make component all
```
- Automatically cleans component before building
- Uses `Scripts/PDD_workflow.py` with `--clean` flag
- Builds specified components only

#### `make build_all_components`
**Build all components with confirmation**
```bash
make build_all_components
```
- Shows list of components to be built
- Requires user confirmation (press 'y' to proceed)
- Builds all components from `pdd/architecture.json`

### Component Management

#### `make component-delete <name>`
**Delete specific component(s)**
```bash
# Basic deletion with confirmation
make component-delete cli

# Multiple components
make component-delete cli utils

# Dry run (preview what would be deleted)
make DRY_RUN=yes component-delete cli

# Force delete without confirmation
make FORCE_DELETE=yes component-delete cli
```

### Cleaning Commands

#### `make clean`
**Remove generated files (keep directories)**
```bash
make clean
```
Removes contents of: edit_file_tool/, tests/, logs/, cost_reports/, examples/

#### `make clean-all`
**Complete project reset**
```bash
make clean-all
```
- Removes entire directories: edit_file_tool/, tests/
- Removes `pdd/architecture.json`
- Preserves logs/ and cost_reports/ (commented out)

### Testing

#### `make test`
**Run all unit tests**
```bash
make test
```
Executes all `test_*.py` files in tests/ directory using pytest

### Advanced Commands

#### `make infisical-component <name>`
**Build components with Infisical secrets**
```bash
make infisical-component utils
```
Uses Infisical for secret management during component building

#### `make infisical-run COMMAND="..."`
**Run any command with Infisical secrets**
```bash
make infisical-run COMMAND="pdd sync utils"
```

### Configuration Examples

#### PDD Execution Mode
```bash
# Local PDD without Infisical
make USE_INFISICAL=no USE_LOCAL=yes component cli

# Cloud PDD with Infisical
make USE_INFISICAL=yes USE_LOCAL=no component cli

# Direct PDD (no Infisical, cloud mode)
make USE_INFISICAL=no USE_LOCAL=no component cli
```

#### Component Building Options
```bash
# Build without cleaning first
make CLEAN_COMPONENTS=no component cli

# Build with tagging enabled
make ENABLE_TAGGING=yes component cli
```

### Common Workflows

#### First-time setup
```bash
make setup
make arch_list
make prompts
# Review generated prompts in prompts/ directory
make build_all_components
```

#### Rebuild specific component
```bash
make component cli
```

#### Clean rebuild of entire project
```bash
make clean
make all
```

#### Development cycle
```bash
# Modify prompts/cli_python.prompt
make component cli
# Test changes
make test
```

## Understanding the Nine PDD Commands

While **`pdd sync`** is the primary command that orchestrates everything, it's helpful to understand the individual commands that make up the complete workflow:

### 1. auto-deps
- **Purpose**: Analyzes project dependencies and injects relevant context into prompts
- **When sync uses it**: First step to enhance prompts with necessary imports and references

### 2. generate  
- **Purpose**: Creates the main implementation code from prompts
- **When sync uses it**: Core code generation phase, with incremental updates when possible

### 3. example
- **Purpose**: Generates compact usage examples showing the component interface
- **When sync uses it**: After code generation to create reusable interface demonstrations

### 4. crash
- **Purpose**: Detects and fixes runtime errors to make code executable
- **When sync uses it**: Ensures generated code actually runs without throwing exceptions

### 5. verify
- **Purpose**: Validates that code behavior matches the prompt's intended functionality
- **When sync uses it**: Functional verification before detailed testing begins

### 6. test
- **Purpose**: Generates comprehensive unit tests for the component
- **When sync uses it**: Creates thorough test coverage for the verified code

### 7. fix
- **Purpose**: Resolves bugs and issues found by unit tests
- **When sync uses it**: Iteratively fixes code until all tests pass

### 8. update
- **Purpose**: Back-propagates improvements and learnings to the original prompt
- **When sync uses it**: Final step to enhance prompts based on development insights

### 9. Manual Commands (used outside sync)
- **preprocess**: Handles prompt preprocessing with includes and templating
- **split**: Breaks large prompts into smaller, manageable components
- **change**: Modifies prompts based on change instructions
- **detect**: Analyzes which prompts need updates based on requirements
- **conflicts**: Identifies and resolves conflicts between prompts

**Key Insight**: You rarely need to run these individual commands manually. The `sync` command intelligently orchestrates them based on your project's current state and needs. However, you are able to if you wish, just run `pdd (cmd_you_want) --help` for more information

## Project Structure and Key Files

### Directory Organization

```
PDD_user_experience_test_manual/
├── prompts/                                # Component specifications (source of truth)
│   └── {component}_python.prompt          # Individual component prompts
├── edit_file_tool/                         # Generated Python package
│   ├── __init__.py                         # Package initialization
│   ├── cli.py                             # Command-line interface
│   ├── editor_tool.py                     # Core editing implementation
│   └── {component}.py                     # Other generated modules
├── tests/                                  # Generated unit tests
│   └── test_{component}.py                # Comprehensive test suites
├── examples/                               # Usage demonstrations
│   └── {component}_example.py             # Token-efficient interface examples
├── make_creation/{component}/              # Build tracking
│   ├── cmd_{component}.txt                # Command execution logs
│   └── cost_{component}.csv               # Optional cost tracking
├── Scripts/                                # Build automation
│   ├── PDD_workflow.py                    # Component build wrapper
│   └── prompts_script.py                 # Prompt generation
└── project_dependencies.csv               # Dependency analysis cache
```

### Key File Explanations

- **project_dependencies.csv**: Used by PDD's `auto-deps` command to cache analysis of potential dependency files. Contains file paths, summaries, and analysis dates to avoid re-scanning unchanged files.

- **prompts/ folder**: Contains the source-of-truth specifications for each component. These `{component}_python.prompt` files drive the entire generation process.

- **edit_file_tool/ folder**: The actual generated Python package - not documentation, but working code that can be imported and used.

- **tests/ folder**: Generated unit tests with high coverage, created automatically by PDD to validate the generated code.

- **examples/ folder**: Token-efficient usage demonstrations that show how to use each component's interface, designed for reuse in other prompts.

## Using the Generated Edit File Tool

**Important**: The `edit_file_tool/` directory contains actual working Python code, not documentation. This is the generated implementation that demonstrates PDD's capabilities.

### Command Line Interface

The tool provides a CLI through `cli.py`:

```bash
# Basic usage
python edit_file_tool/cli.py <file_path> "<edit_instructions>"

# With options
python edit_file_tool/cli.py myfile.py "Add a docstring to the main function" --verbose

# Specify model
python edit_file_tool/cli.py myfile.py "Refactor this code" --model claude-3-sonnet-20240229
```

### Core Components

- **`cli.py`**: Command-line interface using Click library
  - Handles argument parsing and validation
  - Manages API key validation
  - Provides user-friendly error messages and cost reporting

- **`editor_tool.py`**: Core file editing implementation  
  - Provides secure file operations (view, str_replace, insert, create, undo_edit)
  - Includes path validation to prevent directory traversal
  - Implements backup system for undo functionality

### Environment Setup

The tool requires:
```bash
export ANTHROPIC_API_KEY=your_api_key_here
# Optional: Override default model
export EDIT_FILE_TOOL_MODEL=claude-3-opus-20240229
```

This demonstrates how PDD can generate complete, working applications from prompts - not just code snippets, but full CLI tools with proper error handling, security validation, and user experience.

## PDD Sync Benefits

### Streamlined Development

**Traditional Approach** (manual command orchestration):
- Required running multiple individual PDD commands per component
- Manual coordination between generate, example, test, fix phases
- Error-prone transitions between steps
- Time-consuming manual oversight

**PDD Sync Approach** (automated workflow):
- Single `pdd sync {component} --force` command
- Automatic execution of complete pipeline
- Built-in error handling and recovery
- Simplified workflow management

### Key Advantages

- **Complete Automation**: One command handles the entire development cycle
- **Consistent Results**: Standardized workflow ensures reliability
- **Force Regeneration**: `--force` flag ensures clean rebuilds
- **Integrated Testing**: Automatic test generation and validation
- **Working Code**: Generates production-ready applications, not just snippets

## Simplified Development Workflow

1. **Initial Setup**: `make setup` to create directory structure
2. **Generate Architecture**: `make arch_list` to create component specifications  
3. **Create Prompts**: `make prompts` to generate component prompts from architecture
4. **Review Prompts**: Manually inspect generated prompts in `prompts/` directory
5. **Build Project**: `make all` to build all components, or `make component <name>` for individual components
6. **Test & Validate**: Run generated tests and verify the working edit file tool
7. **Iterate**: Modify prompts and rebuild individual components as needed

### Simplified Tips

- **Always review prompts**: Check `prompts/` directory before building to ensure quality
- **Clean rebuilds**: The workflow automatically cleans components before rebuilding  
- **One command builds all**: `make all` handles the complete setup → prompts → build pipeline
- **Individual updates**: Use `make component <name>` to rebuild specific components
- **Track commands**: Check `make_creation/{component}/cmd_{component}.txt` for execution history
- **Test real functionality**: The generated `edit_file_tool/` is working code you can actually use

## Cost Tracking (Optional)

The workflow supports optional cost tracking:

- **Enable in Workflow**: Set `ENABLE_COST_TRACKING = True` in `PDD_workflow.py`
- **Cost Reports**: Saved to `make_creation/{component}/cost_{component}.csv`
- **Command Tracking**: All executed commands logged for audit trail
- **PDD Built-in**: Uses PDD's native `--output-cost` functionality

Enable cost tracking:
```python
# In Scripts/PDD_workflow.py
ENABLE_COST_TRACKING = True     # Enable cost tracking
```

This simplified approach demonstrates how PDD sync can generate complete working applications from prompts with minimal configuration and maximum automation.