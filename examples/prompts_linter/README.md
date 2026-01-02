# PDD Prompt Linter

The PDD Prompt Linter is a tool designed to analyze LLM prompts against Prompt-Driven Development (PDD) best practices. It provides automated feedback on prompt structure, clarity, and potential issues, helping developers write more effective and reliable prompts.

## Features

- **Multi-Interface**: Access the linter via CLI, REST API, or a Streamlit UI.
- **Rule-Based Analysis**: Validates prompts against a registry of PDD rules (e.g., clear instructions, structured sections).
- **Include Resolution**: (Experimental) Automatically resolves `<include>` tags to estimate final token counts.
- **Automated Suggestions**: Provides actionable feedback and suggested edits for identified issues.

---

## Prerequisites

- **Python 3.12+**
- Required libraries:
  ```bash
  pip install fastapi uvicorn typer streamlit requests pydantic pytest
  ```

## Running the Tool

### 1. Command Line Interface (CLI)
The CLI allows you to lint files directly from your terminal.

```bash
# Set PYTHONPATH to include the src directory
export PYTHONPATH=$PYTHONPATH:$(pwd)/src

# Lint a file
python src/cli/pddl.py lint examples/models_findings_example.py

# List all available rules
python src/cli/pddl.py rules

# Explain a specific rule
python src/cli/pddl.py explain PDD001
```

### 2. Backend API
Run the FastAPI server to provide linting services to other applications or the UI.

```bash
# Set PYTHONPATH to include the src directory
export PYTHONPATH=$PYTHONPATH:$(pwd)/src

# Start the server
python src/backend/app/main.py
```
The API will be available at `http://localhost:8000`. You can view the interactive documentation at `http://localhost:8000/docs`.

### 3. Streamlit UI
A web-based interface for interactive linting.

```bash
# Ensure the Backend API is running first (see above)

# Start the Streamlit app
streamlit run src/ui/streamlit_app.py
```

---

## Testing

Run the test suite using `pytest`.

```bash
export PYTHONPATH=$PYTHONPATH:$(pwd)/src
pytest
```

---

## Troubleshooting & Manual Fixes

During the PDD implementation process, several manual fixes were applied to bridge gaps between generated modules and ensure system integration:

### 1. Model Mismatch in Rule Helper
The generated `pdd_rules.py` initially used an incorrect schema for creating findings.
- **Problem**: `ValidationError` when creating `SuggestedEdit` and `Finding` objects.
- **Fix**: Updated `_create_finding` to use the `Evidence` model and the correct `SuggestedEdit` fields (`kind`, `snippet`).

### 2. Rule Registration in API
The API was returning empty reports because the rules were never loaded into the registry.
- **Problem**: `LintEngine` accessed `default_registry`, but no rules were registered because `pdd_rules.py` was never imported.
- **Fix**: Added `import src.backend.rules.pdd_rules` to `src/backend/app/main.py` to trigger the `@registry.register_rule` decorators.

### 3. Import Path Consistency
Standardized all internal imports to use the `src.` prefix (e.g., `from src.backend...`) to ensure compatibility when running from the project root.

---

## Functional Error Fixing with PDD

Beyond initial generation, the `pdd fix` command can be used to resolve functional bugs identified during testing. This workflow ensures that the implementation aligns with the original prompt specification and passes all unit tests.

### Case Study: Streamlit UI Score Display
A bug was identified where the Streamlit UI consistently showed a score of `0/100`, even when the backend API reported a higher score.

**Workflow:**
1.  **Reproduce**: Update or add unit tests (`tests/test_ui_streamlit.py`) to simulate the incorrect behavior and assert the expected outcome.
2.  **Confirm Failure**: Run the tests and capture the failure details.
    ```bash
    pytest tests/test_ui_streamlit.py > errors.log 2>&1
    ```
3.  **Apply Automated Fix**: Use the `pdd fix` command, providing the prompt, the failing code, the unit test, and the error log.
    ```bash
    pdd --force fix \
      --output-test tests/test_ui_streamlit.py \
      --output-code src/ui/streamlit_app.py \
      prompts/ui_streamlit_Python.prompt \
      src/ui/streamlit_app.py \
      tests/test_ui_streamlit.py \
      errors.log
    ```
4.  **Verify**: Run the tests again to ensure the code now correctly parses the API response and displays the expected data.

---

## PDD Commands Execution Plan

This document outlines the step-by-step commands to generate the PDD Prompt Linter project using the PDD CLI.

### 1. Project Initialization

Initialize the project configuration and documentation.

#### 1.1 Create .pddrc
Create the project configuration file `.pddrc` in the root directory:

```yaml
# .pddrc
version: "1.0"

contexts:
  default:
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
      example_output_path: "examples/"
      target_coverage: 10.0
      strength: 0.75
      temperature: 0.0
      budget: 10.0
      max_attempts: 3
```

#### 1.2 Create Documentation
Ensure the following documentation files exist in the `docs/` directory. These are inputs for the architecture generation.

- `docs/specs.md`: The Product Requirements Document (PRD).
- `docs/tech_stack.md`: The Technology Stack definition.

### 2. Architecture Generation

Generate the `architecture.json` file from the product requirements and tech stack documentation.

```bash
pdd --force generate --template architecture/architecture_json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output architecture.json
```

### 3. Environment Setup

Create the necessary directory structure to match the architecture.

```bash
mkdir -p prompts
mkdir -p src/backend/models
mkdir -p src/backend/rules
mkdir -p src/backend/core
mkdir -p src/backend/app
mkdir -p src/cli
mkdir -p src/ui
mkdir -p examples
mkdir -p tests
```

### 4. Prompt Generation

Generate the `.prompt` specification files for each module using the `architecture.json` and the `generic/generate_prompt` template.

#### 4.1 Models (Priority 1)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=models_findings \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/models_findings_Python.prompt
```

#### 4.2 Rules Registry (Priority 2)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=rules_registry \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/rules_registry_Python.prompt
```

#### 4.3 Parser (Priority 3)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=parser \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/parser_Python.prompt
```

#### 4.4 Include Resolver (Priority 4)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=include_resolver \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/include_resolver_Python.prompt
```

#### 4.5 Lint Engine (Priority 5)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=lint_engine \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/lint_engine_Python.prompt
```

#### 4.6 PDD Rules (Priority 6)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=pdd_rules \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/pdd_rules_Python.prompt
```

#### 4.7 API (Priority 7)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=api_main \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/api_main_Python.prompt
```

#### 4.8 CLI (Priority 8)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=cli_pddl \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/cli_pddl_Python.prompt
```

#### 4.9 UI (Priority 9)
```bash
pdd --force generate --template generic/generate_prompt \
  -e MODULE=ui_streamlit \
  -e LANG_OR_FRAMEWORK=Python \
  -e ARCHITECTURE_FILE=architecture.json \
  -e PRD_FILE=docs/specs.md \
  -e TECH_STACK_FILE=docs/tech_stack.md \
  --output prompts/ui_streamlit_Python.prompt
```

### 5. Module Implementation

Generate code, examples, and tests for each module in dependency order.

#### 5.1 models_findings
```bash
# Generate Code
pdd --force generate --output src/backend/models/findings.py prompts/models_findings_Python.prompt

# Generate Example
pdd --force example prompts/models_findings_Python.prompt src/backend/models/findings.py --output examples/models_findings_example.py

# Generate Tests
pdd --force test prompts/models_findings_Python.prompt src/backend/models/findings.py --output tests/test_findings.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_findings.py

# Fix if needed (example)
# pdd --force fix --output-test tests/test_findings.py --output-code src/backend/models/findings.py prompts/models_findings_Python.prompt src/backend/models/findings.py tests/test_findings.py errors.log
```

#### 5.2 rules_registry
```bash
# Generate Code
pdd --force generate --output src/backend/rules/registry.py prompts/rules_registry_Python.prompt

# Generate Example
pdd --force example prompts/rules_registry_Python.prompt src/backend/rules/registry.py --output examples/rules_registry_example.py

# Generate Tests
pdd --force test prompts/rules_registry_Python.prompt src/backend/rules/registry.py --output tests/test_registry.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_registry.py
```

#### 5.3 parser
```bash
# Generate Code
pdd --force generate --output src/backend/core/parser.py prompts/parser_Python.prompt

# Generate Example
pdd --force example prompts/parser_Python.prompt src/backend/core/parser.py --output examples/parser_example.py

# Generate Tests
pdd --force test prompts/parser_Python.prompt src/backend/core/parser.py --output tests/test_parser.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_parser.py
```

#### 5.4 include_resolver
```bash
# Generate Code
pdd --force generate --output src/backend/core/include_resolver.py prompts/include_resolver_Python.prompt

# Generate Example
pdd --force example prompts/include_resolver_Python.prompt src/backend/core/include_resolver.py --output examples/include_resolver_example.py

# Generate Tests
pdd --force test prompts/include_resolver_Python.prompt src/backend/core/include_resolver.py --output tests/test_include_resolver.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_include_resolver.py
```

#### 5.5 lint_engine
```bash
# Generate Code
pdd --force generate --output src/backend/core/lint_engine.py prompts/lint_engine_Python.prompt

# Generate Example
pdd --force example prompts/lint_engine_Python.prompt src/backend/core/lint_engine.py --output examples/lint_engine_example.py

# Generate Tests
pdd --force test prompts/lint_engine_Python.prompt src/backend/core/lint_engine.py --output tests/test_lint_engine.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_lint_engine.py
```

#### 5.6 pdd_rules
```bash
# Generate Code
pdd --force generate --output src/backend/rules/pdd_rules.py prompts/pdd_rules_Python.prompt

# Generate Example
pdd --force example prompts/pdd_rules_Python.prompt src/backend/rules/pdd_rules.py --output examples/pdd_rules_example.py

# Generate Tests
pdd --force test prompts/pdd_rules_Python.prompt src/backend/rules/pdd_rules.py --output tests/test_pdd_rules.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_pdd_rules.py
```

#### 5.7 api_main
```bash
# Generate Code
pdd --force generate --output src/backend/app/main.py prompts/api_main_Python.prompt

# Generate Example
pdd --force example prompts/api_main_Python.prompt src/backend/app/main.py --output examples/api_main_example.py

# Generate Tests
pdd --force test prompts/api_main_Python.prompt src/backend/app/main.py --output tests/test_api_main.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_api_main.py
```

#### 5.8 cli_pddl
```bash
# Generate Code
pdd --force generate --output src/cli/pddl.py prompts/cli_pddl_Python.prompt

# Generate Example
pdd --force example prompts/cli_pddl_Python.prompt src/cli/pddl.py --output examples/cli_pddl_example.py

# Generate Tests
pdd --force test prompts/cli_pddl_Python.prompt src/cli/pddl.py --output tests/test_cli_pddl.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_cli_pddl.py
```

#### 5.9 ui_streamlit
```bash
# Generate Code
pdd --force generate --output src/ui/streamlit_app.py prompts/ui_streamlit_Python.prompt

# Generate Example
pdd --force example prompts/ui_streamlit_Python.prompt src/ui/streamlit_app.py --output examples/ui_streamlit_example.py

# Generate Tests
pdd --force test prompts/ui_streamlit_Python.prompt src/ui/streamlit_app.py --output tests/test_ui_streamlit.py

# Run Tests
export PYTHONPATH=$PYTHONPATH:$(pwd)/src && pytest tests/test_ui_streamlit.py
```

Note: pdd sync can do all code generation steps in a single command - instructions for using that will be added in the future

```