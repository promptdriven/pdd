# PDD (Prompt-Driven Development) Command Line Interface

![PDD-CLI Version](https://img.shields.io/badge/pdd--cli-v0.0.88-blue) [![Discord](https://img.shields.io/badge/Discord-join%20chat-7289DA.svg?logo=discord&logoColor=white)](https://discord.gg/Yp4RTh8bG7)

## Introduction

Pdd-cli is a complete AI toolchain for generating and maintaining codebases **reliably and repeatably** using the prompt-driven approach.

Unique to this approach, **each PDD prompt is a mini-spec of a single output file**.  PDD fully generates one entire code file at a time, giving you tight control and ensuring each output file is reliably re-generated from its prompt.   

By contrast, prompts in typical AI coding tools are instead incremental patch requests, and these tools will unpredictably update any combination of files in response to a  prompt.   PDD is an excellent complement to such tools - for long-lived codebases and tasks that are repeatedly rebuilt as they evolve, use PDD; for more incremental, one-off, or ephemeral tasks, use agentic coders, such as Claude, Codex, etc.


<p align="center">
  <img src="docs/videos/handpaint_demo.gif" alt="PDD Handpaint Demo" />
</p>

Noteworthy among its many features, PDD accumulates unit and regression tests, as it detects and fixes bugs, and updates your prompts automatically whenever needed.    In short, it endeavors to fully upport the entire prompt-driven approach.
<br>


## Prerequisites before installing pdd-cli

* MacOS: xcode cli tools, and either uv or pip  [see instructions](README-INSTALL-PREREQS.md)
* Linux: uv or pip [see instructions](README-INSTALL-PREREQS.md)
* Windows: [click here](SETUP_WITH_WINDOWS.md) for complete Windows installation instructions

## Quick Installation

### uv (recommended)
```bash
uv tool install pdd-cli
```

### pip (alternate method)
```bash
pip install pdd-cli
```


### Then run pdd to check:
```bash
pdd --version
```
<br> 

From here your pdd installation is complete.   For the most convenience, set up your LLM API keys, as below:<br><br><br>

## Configure your API keys & shell

```bash
# Creates api-env and llm_model.csv config files in ~/.pdd, updates shell init.
# It also writes a starter prompt (success_python.prompt) for you to try.   

# Re-run this any time to update keys or reinstall completions.   

pdd setup
```
```bash
# Reload your shell so the new completion and environment hooks are available:

. ~/.zshrc  # or ". ~/.bashrc" / or fish equivalent
```


(If you skip this step, PDD commands will print a reminder banner so you can finish onboarding later.)

<br><br>
## Then try it out:
```bash
pdd generate success_python.prompt
```
(**Extra credit!!!** -- Build the various examples included in pdd repo, under **pdd/examples/**.  <br>
  Just do `git clone https://github.com/promptdriven/pdd.git`)
<br><br>

## Next steps:

* Review [PDD Basic Concepts](README-CONCEPTS.md) to understand the concepts behind the prompt-driven approach.

* Start incorporating individual [Prompt-Driven Workflows](README-WORKFLOWS.md) into your development cycle.

* [Join the PDD Discord Community](http://tinyurl.com/pdd-discord), and [Contribute to PDD](CONTRIBUTING.md).

## Going deeper
* [PDD Command Reference](README-COMMANDS.md) 
* [Troubleshooting](README-TROUBLESHOOTING.md)
* [Advanced Configuration for Your Project](README-ADVANCED-CONFIGURATION.md)
* [PDD Cloud](README-CLOUD.md)
* [Security Considerations](README-SECURITY.md)
* [Gemini API key instructions](SETUP_WITH_GEMINI.md)

## Whitepaper

For a detailed explanation of the concepts, architecture, and benefits of Prompt-Driven Development, please refer to our full whitepaper. This document provides an in-depth look at the PDD philosophy, its advantages over traditional development, and includes benchmarks and case studies.

[Read the Full Whitepaper with Benchmarks](docs/whitepaper_with_benchmarks/whitepaper_w_benchmarks.md)

Also see the Prompt‑Driven Development Doctrine for core principles and practices: [docs/prompt-driven-development-doctrine.md](docs/prompt-driven-development-doctrine.md)


## Patents

One or more patent applications covering aspects of the PDD workflows and systems are pending. This notice does not grant any patent rights; rights are as specified in the [LICENSE](LICENSE).

## MacOS Only Prerequisite - Python 3.0+
1. **Install Xcode Command Line Tools** (required for Python compilation):
   ```bash
   xcode-select --install
   ```

2. **Install Homebrew** (recommended package manager for macOS):
   ```bash
   /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
   ```
   
   After installation, add Homebrew to your PATH:
   ```bash
   echo 'eval "$(/opt/homebrew/bin/brew shellenv)"' >> ~/.zprofile && eval "$(/opt/homebrew/bin/brew shellenv)"
   ```

3. **Install Python** (if not already installed):
   ```bash
   # Check if Python is installed
   python3 --version
   
   # If Python is not found, install it via Homebrew
   brew install python
   ```
   
   **Note**: macOS comes with Python 2.7 by default (deprecated), but PDD requires Python 3.8 or higher. The `brew install python` command installs the latest Python 3 version.



## MacOS & Linux Prerequisites

#### Option 1: uv
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

#### Option 2: pip 
(after installing python via your preferred method, and ensuring that installed python is in your search path)
```bash
python3 -m ensurepip --upgrade
# PDD Fundamental Concepts and Practices
- [The Big Ideas](#the-big-ideas)
- [Adopt These Practices](#adopt-practices)
- [Conclusion](#conclusion)


<a name="the-big-ideas"></a>
# The Big Ideas

Prompt-Driven Development (PDD) treats prompts as the primary artifact - not code. This paradigm shift has profound implications:

- **Prompts as Source of Truth**<BR> 
   - In PDD, the prompts are authoritative, with code being a generated artifact, technically disposable.  By contrast, in traditional development, source code is the ground truth that defines system behavior. 

- **One Prompt per Output File**<br>
   - Each prompt is a natural-language mini-specification of a target output file.  This laser-focuses the LLM on the single target, reducing issues such as hallucination.
   
   - PDD's archtitecture and features gives the user precise control over what is in-context for each file generation - the main prompt, included modular prompt snippets describing dependencies, coding style preferences, etc.   
   
   - At the same time it eliminates from context irrelevant code snippets, chat history, etc. which confuses the models within tools such as Claude, Codex, etc.  Further, it uses fewer tokens, resulting in lower API costs (often 1/5 the cost of thos other tools)

- **Natural Language Over Code**<br>
   -   Prompts are written primarily in natural language, making them more accessible to non-programmers and clearer in expressing intent.

- **Regenerative Development**<br>
   - When changes are needed, you modify the prompt and fully regenerate the code, rather than directly editing the code. This maintains the conceptual integrity between requirements and implementation.

- **Intent Preservation**<br>
   - Natural language prompts capture the "why" behind code in addition to the "what" - preserving design rationale in a way that comments often fail to do.

<br>

<a name="adopt-practices"></a>
# Adopt These Practices

### 1. Prompts First:
   Always start by defining what you want in a prompt before generating any code.
   <br><br>
   Use tools like Cursor, ChatGPT, and even Claude Code as your co-pilot in this process.   You can also use these tools also to convert your product artifacts (PRDs, specs, design docs, etc.) into prompts, and keep them up to date, though we recommend an interim step (architecture.json) which we describe elsewhere.


### 2. Keep Prompts and Code in Sync:
   - Prompt → Code<br>
    Your "daily driver" - code generation with `pdd generate`
   
   - Code → Prompt<br>
    `pdd update` incorporates direct code changes into the original prompts.    Such changes may originate from PDD's automated test-diagnose-fix loops, from direct edits by a user, or changes with tools such as Claude.   Alternately, `pdd sync` will detect and invoke `pdd update` for prompts which are out of date.

### 3. Integrate Code Files via "Examples":
   "Examples" in PDD terminology are separate files of runnable code, showing how to use a specific target output file - they describe the interface for that code file.<br>
   
   Use `pdd example` to generate examples for any code file which will be used by another.<br>

   Then, in prompts for those other code files, `<include>` those examples as dependencies in your prompts.   `pdd auto-deps` will add `<include>` directives for these dependencies to a prompt file - and further, `pdd sync` will figure out which files need which dependencies, and apply `pdd auto-deps` for you.

   Examples are valuable artifacts which should be versioned in your project repository, along side your prompts.

### 4. Shape and Define Correct Code Behavior with Tests:
   PDD ensures correct code using tests which accumulate over the life of your project.   PDD's workflows using `pdd fix`, `pdd crash`, and `pdd verify` utilize these accumulated tests to test, verify and correct output code; `pdd sync` will also invoke these tools automatically.
   
   Generate unit tests with `pdd test`, and as bugs are found generate regression tests with `pdd bug`.   `Pdd sync` will also invoke `pdd test` and `pdd bug` when necessary.

   Tests, like examples, are valuable artifacts which should be versioned in your project repository, along side your prompts.


### 5. Modularize Prompts:
   Just as you modularize code, you should modularize prompts into self-contained units that can be composed.  Specifically, the PDD `<include>` tag directive enables you to incorporate modular units into any/all prompts.  
   <br>
   For example, you might want a single prompt unit describing your coding style preferences, which you then `<include>` in all your code prompt files.   
   
   Use `pdd auto-deps` to analyze dependencies between prompts/code, and automatically insert include directives for examples from each dependency into your prompt file(s).

<br>

<a name="conclusion"></a>
## Conclusion

Beyond the concepts and PDD commands mentioned above, PDD CLI provides a comprehensive set of tools for managing prompt files, generating code, creating examples, running tests, and handling various aspects of prompt-driven development. By leveraging the power of AI models and iterative processes, PDD aims to streamline the development workflow and improve code quality.

The various commands and options allow for flexible usage, from simple code generation to complex workflows involving multiple steps. The ability to track costs and manage output locations through environment variables further enhances the tool's utility in different development environments.

As you become more familiar with PDD, you can compose richer workflows by chaining commands in shell scripts, task runners, or CI pipelines while leveraging the full range of options available. Always refer to the latest documentation and use the built-in help features to make the most of PDD in your development process.

Remember to stay mindful of security considerations, especially when working with generated code or sensitive data. Regularly update PDD to access the latest features and improvements.

Happy coding with PDD!



# Prompt-Driven Workflows
Refer to these workflows as needed throughout your Prompt-Driven product development lifecycle.

Each workflow in PDD addresses a fundamental development need:

"Daily-driver" workflows

* [Initial Development Workflow](#initial-development) - build up your PDD codebase
* [Feature Enhancement](#feature-enhancement) - enhance a feature
* [Code-to-Prompt Update](#code-to-prompt-update) - sync direct code changes back to your prompt base
* [Prompt Refactoring](#prompt-refactoring) - reorganize prompts for maintainabliity and reusability
* [Multi-Prompt Architecture](#multi-prompt-architecture) - coordinating systems with multiple prompts

Debugging Workflows

* [Prompt Context Issues](#prompt-context-issues) - resolve issues with misunderstandings in prompt interpretation or preprocessing
* [Runtime Crash Debugging](#runtime-crash-debugging) - fix code that fails to execute
* [Logical Bug Fixing](#logical-bug-fixing) - correct code that runs but produces incorrect results
* [Debugger Guided Analysis](#debugger-guided-analysis) - identify which prompt sections produce problematic code

More
* [Critical Dependencies](#critical-dependencies) - important constraints / requirements for any workflow
* [Workflow Selection Principles](#workflow-selection-principles) - how to choose a workflow depending on your development phase
<br>
<br>
----


<a name="initial-development"></a>
### Initial Development

**Purpose**: Create new functionality from scratch with proper testing and verification.

**Conceptual Flow**: Define dependencies → Generate implementation → Create interfaces → Ensure runtime functionality → Verify correctness

**Command Flow**: `auto-deps → generate → example → crash → verify → test → fix`

**Process**:
1. Identify and inject dependencies for your prompt (`auto-deps`).
2. Generate full implementation code from the prompt (`generate`).
3. Create reusable interface examples (`example`).
4. Ensure the code runs without crashing and fix runtime errors (`crash`).
5. Run the example and use an LLM to check if the output aligns with the prompt's intent, attempting iterative fixes if necessary (`verify`).
6. Generate comprehensive unit tests for the implementation (`test`).
7. Fix any issues revealed by the unit tests (`fix`).

**Key Insight**: This workflow follows a progression from concept to verified implementation, ensuring the code runs (`crash`) before checking functional output (`verify`) and detailed unit testing (`test`).

---

<a name="feature-enhancement"></a>
### Feature Enhancement

Use when adding capabilities to existing modules.

**Purpose**: Add new capabilities to existing functionality.

**Command Flow**: `change → generate → example → test → fix`

**Process**:
1. Modify prompts to describe new features
2. Regenerate code with enhanced functionality
3. Update examples to demonstrate new features
4. Test to verify correct implementation
5. Fix any issues that arise

**Key Insight**: Feature additions should flow from prompt changes rather than direct code modifications.

---

<a name="code-to-prompt-update"></a>
### Code-to-Prompt Update

This workflow ensures the information flow from code back to prompts, preserving prompts as the source of truth.

**Conceptual Flow**: Sync code changes to prompt → Identify impacts → Propagate changes

**Command Flow**: `update → detect → change`

**Purpose**: Maintain prompt as source of truth after code changes.

**Process**:
1. Synchronize direct code changes back to the original prompt
2. Detect other prompts that might be affected by these changes
3. Apply necessary changes to dependent prompts

**Key Insight**: This bidirectional flow ensures prompts remain the source of truth even when code changes happen first.

---
<a name="prompt-refactoring"></a>
### Prompt Refactoring

This workflow parallels code refactoring but operates at the prompt level.

**Purpose**: Break large prompts into modular components, improving organization and reusability.

**Conceptual Flow**: Extract functionality → Ensure dependencies → Create interfaces

**Command Flow**: `split → auto-deps → example`


**Process**:
1. Extract specific functionality from a large prompt into a separate prompt
2. Ensure the new prompt has all dependencies it needs
3. Create interface examples for the extracted functionality

**Key Insight**: Just as code should be modular, prompts benefit from decomposition into focused, reusable components.

---

### Debugging Workflows

<a name="prompt-context-issues"></a>
#### Prompt Context Issues

**Purpose**: Resolve issues with misunderstandings in prompt interpretation or preprocessing.

**Comamnd Flow**: `preprocess → generate`

**Process**:
1. Examine how the prompt is being preprocessed
2. Regenerate code with improved prompt clarity

---

<a name="runtime-crash-debugging"></a>
#### Runtime Crash Debugging

**Runtime Issues**: Fix code that fails to execute.

**Command Flow**: `generate → example → crash`

**Process**:
1. Generate initial code from prompt
2. Create examples and test programs
3. Fix runtime errors to make code executable

---

<a name="logical-bug-fixing"></a>
#### Logical Bug Fixing

**Purpose**: Correct code that runs but produces incorrect results.

**Command Flow**: `bug → fix`

**Process**:
1. Generate test cases that demonstrate the bug
2. Fix the code to pass the tests

---

<a name="debugger-guided-analysis"></a>
#### Debugger-Guided Analysis

**Traceability Issues**: Connecting code problems back to prompt sections - Identify which prompt sections produce problematic code.

**Command Flow**: `trace → [edit prompt]`

**Process**:
1. Locate the relationship between code lines and prompt sections
2. Update relevant prompt sections



---

**Multi-Prompt Architecture Workflow**

**Purpose**: Coordinating systems with multiple prompts
**Conceptual Flow**: Detect conflicts → Resolve incompatibilities → Regenerate code → Update interfaces → Verify system
   
This workflow addresses the complexity of managing multiple interdependent prompts.


--- 

<a name="multi-prompt-architecture"></a>
### Multi-Prompt Architecture

**Command Flow**: `conflicts/detect → change → generate → example → test`

**Purpose**: Coordinate multiple prompts derived from higher-level requirements.

**Process**:
1. Identify conflicts or dependencies between prompts
2. Harmonize the prompts to work together
3. Regenerate code from updated prompts
4. Update interface examples after changes
5. Verify system integration with tests

**Key Insight**: Complex systems require coordination between prompts, just as they do between code modules.

--- 



<a name="critical-dependencies"></a>
### Critical Dependencies

When using these workflows, remember these crucial tool dependencies:

- 'generate' must be done before 'example' or 'test'
- 'crash' is used to fix runtime errors and make code runnable
- 'fix' requires runnable code created/verified by 'crash'
- 'test' must be created before using 'fix'
- Always update 'example' after major prompt interface changes

For detailed command examples for each workflow, see the respective command documentation sections.

---


<a name="workflow-selection-principles"></a>
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

## Configuration

PDD supports multiple configuration methods to customize its behavior for different project structures and contexts.

### Configuration Priority

PDD resolves configuration settings in the following order (highest to lowest priority):

1. **Command-line options** (e.g., `--output`, `--strength`)
2. **Context-specific settings** (from `.pddrc` file) - see [Project Configuration File( (.pddrc))](#project-configuration-file-pddrc) immediately below.
3. **Global environment variables** (e.g., `PDD_GENERATE_OUTPUT_PATH`) - see [Environment Variables](#environment-variables) below
4. **Built-in defaults**

<a name="project-configuration-file-pddrc"></a>
## Project Configuration File (.pddrc)

**Recommended for multi-context projects** (e.g., monorepos with backend/frontend)

Create a `.pddrc` file in your project root to define different contexts with their own settings:

```yaml
# .pddrc - committed to version control
version: "1.0"
contexts:
  backend:
    paths: ["backend/**", "api/**", "server/**"]
    defaults:
      generate_output_path: "backend/src/"
      test_output_path: "backend/tests/"
      example_output_path: "backend/examples/"
      default_language: "python"
      target_coverage: 90.0
      strength: 0.8
  
  frontend:
    paths: ["frontend/**", "web/**", "ui/**"]
    defaults:
      generate_output_path: "frontend/src/"
      test_output_path: "frontend/__tests__/"
      example_output_path: "frontend/examples/"
      default_language: "typescript"
      target_coverage: 85.0
      strength: 0.7
  
  shared:
    paths: ["shared/**", "common/**", "lib/**"]
    defaults:
      generate_output_path: "shared/lib/"
      test_output_path: "shared/tests/"
      default_language: "python"
      target_coverage: 95.0
  
  # Fallback for unmatched paths
  default:
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
      default_language: "python"
      target_coverage: 90.0
      strength: 0.5
```

**Context Detection**:
PDD automatically detects the appropriate context based on:
1. **Current directory path**: Matches against the `paths` patterns in each context
2. **Manual override**: Use `--context CONTEXT_NAME` to specify explicitly
3. **Fallback**: Uses `default` context if no path matches

**Available Context Settings**:
- `generate_output_path`: Where generated code files are saved
- `test_output_path`: Where test files are saved
- `example_output_path`: Where example files are saved
- `default_language`: Default programming language for the context
- `target_coverage`: Default test coverage target
- `strength`: Default AI model strength (0.0-1.0)
- `temperature`: Default AI model temperature
- `budget`: Default budget for iterative commands
- `max_attempts`: Default maximum attempts for fixing operations

**Usage Examples**:
```bash
# Auto-detect context from current directory
cd backend && pdd --force sync calculator     # Uses backend context
cd frontend && pdd --force sync dashboard     # Uses frontend context

# Explicit context override
pdd --context backend sync calculator
pdd --context frontend sync dashboard

# List available contexts
pdd --list-contexts
```

<a name="environment-variables"></a>
## Environment Variables

PDD uses several environment variables to customize its behavior:

#### Core Environment Variables

- **`PDD_PATH`**: Points to the root directory of PDD. This is automatically set during pip installation to the directory where PDD is installed. You typically don't need to set this manually.
- **`PDD_AUTO_UPDATE`**: Controls whether PDD automatically updates itself (default: true).
- **`PDD_CONFIG_PATH`**: Override the default `.pddrc` file location (default: searches upward from current directory).
- **`PDD_DEFAULT_CONTEXT`**: Default context to use when no context is detected (default: "default").
- **`PDD_DEFAULT_LANGUAGE`**: Global default programming language when not specified in context (default: "python").

#### Output Path Variables

**Note**: When using `.pddrc` configuration, context-specific settings take precedence over these global environment variables.

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
- **`PDD_VERIFY_CODE_OUTPUT_PATH`**: Default path for the final code file generated by the `verify` command.
- **`PDD_VERIFY_PROGRAM_OUTPUT_PATH`**: Default path for the final program file generated by the `verify` command.


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



### Migration from Environment Variables to .pddrc

If you're currently using environment variables, you can migrate to `.pddrc` configuration:

```bash
# Before: Environment variables
export PDD_GENERATE_OUTPUT_PATH=backend/src/
export PDD_TEST_OUTPUT_PATH=backend/tests/
export PDD_DEFAULT_LANGUAGE=python

# After: .pddrc file
contexts:
  default:
    defaults:
      generate_output_path: "backend/src/"
      test_output_path: "backend/tests/" 
      default_language: "python"
```

The `.pddrc` approach is recommended for team projects as it ensures consistent configuration across all team members and can be version controlled.


## Model Configuration (`llm_model.csv`)

PDD uses a CSV file (`llm_model.csv`) to store information about available AI models, their costs, capabilities, and required API key names. When running commands locally (e.g., using the `update_model_costs.py` utility or potentially local execution modes if implemented), PDD determines which configuration file to use based on the following priority:

1.  **User-specific:** `~/.pdd/llm_model.csv` - If this file exists, it takes precedence over any project-level configuration. This allows users to maintain a personal, system-wide model configuration.
2.  **Project-specific:** `<PROJECT_ROOT>/.pdd/llm_model.csv` - If the user-specific file is not found, PDD looks for the file within the `.pdd` directory of the determined project root (based on `PDD_PATH` or auto-detection).
3.  **Package default:** If neither of the above exist, PDD falls back to the default configuration bundled with the package installation.

This tiered approach allows for both shared project configurations and individual user overrides, while ensuring PDD works out-of-the-box without requiring manual configuration.


The CSV includes columns for:
- `provider`: The LLM provider (e.g., "openai", "anthropic", "google")
- `model`: The LiteLLM model identifier (e.g., "gpt-4", "claude-3-opus-20240229")
- `input`/`output`: Costs per million tokens
- `coding_arena_elo`: ELO rating for coding ability
- `api_key`: The environment variable name for the required API key
- `structured_output`: Whether the model supports structured JSON output
- `reasoning_type`: Support for reasoning capabilities ("none", "budget", or "effort")

For a concrete, up-to-date reference of supported models and example rows, see the bundled CSV in this repository: [pdd/data/llm_model.csv](pdd/data/llm_model.csv).

For proper model identifiers to use in your custom configuration, refer to the [LiteLLM Model List](https://docs.litellm.ai/docs/providers) documentation. LiteLLM typically uses model identifiers in the format `provider/model_name` (e.g., "openai/gpt-4", "anthropic/claude-3-opus-20240229").

(*Note: This file-based configuration primarily affects local operations and utilities. Cloud execution modes likely rely on centrally managed configurations.*)

---



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

# PDD Cloud
- [What is PDD Cloud?](#what-is-pdd-cloud)
- [PDD Cloud Automated Grounding](#automated-grounding)
- [Accessing the PDD Cloud Dashboard](#accessing-the-pdd-cloud-dashboard)
- [PDD-CLI Cloud Authentication](#pdd-cli-cloud-authentication-usually-one-time-only)
- [PDD-CLI Local Mode (non-cloud)](#pdd-cli-local-mode)

<a name="what-is-pdd-cloud"></a>
## What is PDD Cloud?

PDD Cloud maximizes ease-of-use and reliability of code generation using its proprietary **PDD Context Memory** technology.   

Currently in invite-only Beta testing, PDD Cloud is not enabled for most users.  Your PDD Commands will default to local-only execution.

#### When in general release, PDD Cloud will offer:



#### 1. **The best available code generation**
- correctness, reproducibility, and reliability are all built-in
- built-in **PDD Context Memory** - your code improves the more you use PDD


#### 2. **Hands-free setup and operation**
- no need to manage API keys locally
- built-in access to PDD-optimized selection of the most appropriate model for each task
- automatic updates, bug fixes, and other improvements


#### 3. **Automatic cost optimization**
- built-in automatic smart model selection and smart caching to minimize LLM API costs

#### 4. **Usage Analytics**
- track your team's usage and costs through the PDD Cloud dashboard

#### 5. **Collaboration**: 
- share prompts and generated code with team members
- access community **PDD Context Memory** to further strengthen your project reliability, and reduce development time

<br><br>

<a name="automated-grounding"></a>
## PDD Cloud Automated Grounding
PDD Cloud includes Automated Grounding, which dramatically improves code output quality, and reduces your time spent creating overly-granular prompt details.   

PDD Cloud maintains the history of your prompts and output code.  This history of an output file captures everything you have ever specified about that code file.  Automatic Grounding selects the best portions of that history to inject into prompts during `pdd generate`.   The result is stable outputs over time.

Without Automatic Grounding, you may experience issues such as these:
    - function signatures change when you re-generate
    - features decompose into different functions and objects each time you generate
    - etc.
As a result, you will spend more time iterating on prompt details in order to control the LLM generation, along with time spent re-generating and re-testing.

But with PDD Cloud, Automatic Generation remembers the most relevant and salient characteristics described in the prompt/code history, and selects the best ones to guide the LLM in creating correct and stable outputs, as described.

For a more detailed treatment, see [Automated Grounding](docs/prompting_guide.md#automated-grounding)


---

<a name="accessing-the-pdd-cloud-dashboard"></a>
### Accessing the PDD Cloud Dashboard

Once in general public release, you will access the PDD Cloud dashboard here at: https://promptdriven.ai/

There you will first need to authenticate with your GitHub credentials.

In the dashbaord, you can
- View usage statistics
- Manage team access
- Configure default settings
- Control access to the community shared **Memory Recall** spaces
- Track costs

<br>

--- 
<a name="pdd-cli-cloud-authentication-usually-one-time-only"></a>
### PDD-CLI Cloud Authentication (usually one-time only)

When running in cloud mode, PDD uses GitHub Single Sign-On (SSO) for authentication. On first use, you'll be prompted to authenticate:

1. PDD will open your default browser to the GitHub login page
2. Log in with your GitHub account
3. Authorize PDD Cloud to access your GitHub profile
4. Once authenticated, you can return to your terminal to continue using PDD

The authentication token is securely stored locally and automatically refreshed as needed.

---

<a name="pdd-cli-local-mode"></a>
### PDD-CLI Local Mode

When PDD Cloud is publicly available, cloud execution will be default for all PDD commands; the --local flag is necessary to run in local mode.

When running in local mode with the `--local` flag, you'll need to set up API keys for the language models.  

As in the installation instructions,  it's typically most convenient to run `pdd setup` to set up these keys and associated environment variables.   

For those users who prefer to set up and manage their environment differently, without `pdd setup`, ensure your API keys are set as environment variables, in the shell(s) where you are running PDD-CLI commands.   Some examples, which vary depending on which LLM providers you choose to use:

```bash
# For OpenAI
export OPENAI_API_KEY=your_api_key_here

# For Anthropic
export ANTHROPIC_API_KEY=your_api_key_here

# For other supported providers (LiteLLM supports multiple LLM providers)
export PROVIDER_API_KEY=your_api_key_here
```
Add these to your `.bashrc`, `.zshrc`, or equivalent for persistence.

#### how PDD accesses these keys

PDD's local mode uses LiteLLM (version 1.75.5 or higher) for interacting with language models, providing:

- Support for multiple model providers (OpenAI, Anthropic, Google/Vertex AI, and more)
- Automatic model selection based on strength settings
- Response caching for improved performance
- Smart token usage tracking and cost estimation
- Interactive API key acquisition when keys are missing

### Important Note: 
When keys are missing from the shell environment, PDD commands will prompt for them interactively and securely store them in your local `.env` file.  



## General Security Considerations
When using PDD, keep the following security considerations in mind:

1. **Code Execution**: PDD generates and modifies code. Always review generated code before execution, especially in production environments.

2. **Data Privacy**: Avoid using sensitive data in prompts or code files, as this information may be processed by the AI model.

3. **API Keys**: If PDD requires API keys for AI model access, store these securely and never include them in version control systems.

4. **Input Validation**: PDD assumes input files are trustworthy. Implement proper input validation if using PDD in a multi-user or networked environment.

5. **Output Handling**: Treat output files with the same security considerations as you would any other code or configuration files in your project.

6. **Dependency Analysis**: When using the `auto-deps` command, be cautious with untrusted dependency files and verify the generated summaries before including them in your prompts.

7. **PDD Features and Behavior Are Still Rapidly Evolving**:
   - Consider disabling auto-updates in production environments using `PDD_AUTO_UPDATE=false`
   - Implement a controlled update process for production systems
   - Review changelogs before manually updating PDD in sensitive environments


## PDD Cloud Security
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

8. **Sync-Specific Issues**:
   - **"Another sync is running"**: Check for stale locks in `.pdd/locks/` directory and remove if process no longer exists
   - **Complex conflict resolution problems**: Use `pdd --verbose sync --dry-run basename` to see detailed LLM reasoning and decision analysis
   - **State corruption or unexpected behavior**: Delete `.pdd/meta/{basename}_{language}.json` to reset fingerprint state
   - **Animation display issues**: Sync operations work in background; animation is visual feedback only and doesn't affect functionality
   - **Fingerprint mismatches**: Use `pdd sync --dry-run basename` to see what changes were detected and why operations were recommended

If you encounter persistent issues, consult the PDD documentation or post an issue on GitHub for assistance.



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

3. **macOS-specific issues**
   - **Xcode Command Line Tools not found**: Run `xcode-select --install` to install the required development tools
   - **Homebrew not found**: Install Homebrew using the command in the prerequisites section above
   - **Python not found or wrong version**: Install Python 3 via Homebrew: `brew install python`
   - **Permission denied during compilation**: Ensure Xcode Command Line Tools are properly installed and you have write permissions to the installation directory
   - **uv installation fails**: Try installing uv through Homebrew: `brew install uv`
   - **Python version conflicts**: If you have multiple Python versions, ensure `python3` points to Python 3.8+: `which python3 && python3 --version`
