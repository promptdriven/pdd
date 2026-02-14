# PDD Onboarding Guide

This guide provides instructions for setting up the Prompt-Driven Development (PDD) toolkit. It includes a quick start for users and a comprehensive guide for developers contributing to the project.

## Prerequisites

- A GitHub account
- Basic knowledge of command line operations
- Windows, macOS, or Linux operating system

## Installation Steps

### 1. Install UV Tool

UV is a Python package installer and resolver. Install it using one of the following methods:

**Windows (PowerShell):**

```powershell
(Invoke-WebRequest -Uri "https://astral.sh/uv/install.ps1" -UseBasicParsing).Content | pwsh -Command -
```

**macOS/Linux:**

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

*Note: You may need to restart your terminal or source your shell profile for the `uv` command to become available.*

### 2. Install PDD-CLI

Using UV, install the PDD CLI tool:

```bash
uv tool install pdd-cli
```

*Note: If the `pdd` command is not found after installation, try restarting your terminal.*

To verify your setup is complete, run:

```bash
pdd --version
```

### 3. Clone the GitHub Repository

```bash
git clone https://github.com/promptdriven/pdd.git
cd pdd
```

### 4. Review Documentation

1. Read the Whitepaper to understand the core concepts and architecture:
   - Local: pdd/docs/whitepaper.md
   - Notion: https://www.notion.so/Whitepaper-The-Case-for-Prompt-Driven-Development-1efd44f08ca480ac987ae068f2578f83
2. Review the main repository overview and setup instructions:
   - Root README: README.md
3. Learn how to write effective prompts for PDD:
   - Prompting Guide: pdd/docs/prompting_guide.md
   - PDD Doctrine (principles and guardrails): pdd/docs/prompt-driven-development-doctrine.md

### 5. Set Up Cursor IDE (*Optional but heavily recommended, Visual Studio Code or other similar IDE)

1. Visit [Cursor.sh](https://cursor.sh) and sign up for a trial account
2. Download and install Cursor for your operating system
3. Launch Cursor and sign in with your account

### 6. Install .prompt Extension

To enable syntax highlighting for `.prompt` files in your editor, you'll need to install the PDD extension.

1. **Download the Extension:**

   - Navigate to the [project&#39;s GitHub Releases page](https://github.com/promptdriven/pdd/releases).
   - Download the latest version of the extension, which will be a file named `prompt-*.vsix`.
2. **Install in your IDE:**

   - Open your IDE (Cursor, VS Code, etc.).
   - Open the command palette with `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS).
   - Type `"Extensions: Install from VSIX..."` and select it.
   - Locate the `prompt-*.vsix` file you downloaded and select it to complete the installation.

### 7. Set Up API Keys

**Recommended: Use the setup wizard**

Run the interactive setup wizard to configure your API keys:

```bash
pdd setup
```

The wizard will:
- **Scan your environment** for existing API keys from all sources (shell, .env, ~/.pdd files)
- **Present an interactive menu** to add/fix keys, configure local LLMs, or manage providers
- **Validate keys** with real test requests to ensure they work
- **Show cost transparency** for different model tiers
- **Create .pddrc** configuration for your project

**Alternative: Manual configuration**

If you prefer manual setup, add your LLM API keys to a `.env` file in the project root:

```bash
# Required: At least one LLM provider
OPENAI_API_KEY=sk-your-key-here
# OR
ANTHROPIC_API_KEY=sk-ant-your-key-here
# OR
GEMINI_API_KEY=your-google-api-key

# Optional: For Vertex AI (Gemini via GCP)
VERTEX_CREDENTIALS=/path/to/service-account.json
VERTEX_PROJECT=your-gcp-project-id
VERTEX_LOCATION=us-central1
```

**To use Vertex AI (optional):**

1. Go to [GCP Console &gt; IAM &gt; Service Accounts](https://console.cloud.google.com/iam-admin/serviceaccounts)
2. Create a service account with the "Vertex AI User" role
3. Create and download a JSON key file
4. Save it securely (e.g., `~/.gcp/pdd-service-account.json`)
5. Set `VERTEX_CREDENTIALS` to the file path in your `.env`

See `.env.example` for a complete list of supported environment variables.

### Final Project Configuration

These final steps configure the local repository to ensure the application can find its resources correctly.

**1. Set the `PDD_PATH` Environment Variable:**
The application needs the absolute path to the `pdd/` source directory to function correctly.

- **Step 1: Get the path.**
  From the project root, run:
  ```bash
  cd pdd
  pwd  # Copy the full path output by this command
  cd ..
  ```
- **Step 2: Create a local `.env` file.**
  ```bash
  # Replace "/path/to/your/project/pdd" with the path you copied
  echo "PDD_PATH=/path/to/your/project/pdd" > .env
  ```
- **Step 3: Update `.gitignore`** to ensure this local configuration file is not committed to version control.
  ```bash
  echo ".env" >> .gitignore
  ```

**2. Set Conda Environment Variable (Recommended for WSL):**
This is the most robust method to ensure `PDD_PATH` is always set correctly when your Conda environment is active, as it takes precedence over system variables within the Conda shell.

- **Step 1: Set the Conda variable.**
  Using the same absolute path you copied in Step 2.1 (`/path/to/your/project/pdd`), run the following command from your project root (using pwd):
  ```bash
  # Replace "/path/to/your/project/pdd" with the correct path
  conda env config vars set PDD_PATH="/path/to/your/project/pdd"
  ```
- **Step 2: Reactivate the environment.**
  The change will only take effect after you deactivate and reactivate your environment.
  ```bash
  conda deactivate
  conda activate pdd
  ```
- **Step 3: Verify the change.**
  You can now check if the path is set correctly.
  ```bash
  echo $PDD_PATH
  # It should print the correct path: /path/to/your/project/pdd
  ```

---

## Using PDD

### Web Interface (Recommended)

After installation, the easiest way to use PDD is through the web interface:

```bash
pdd connect
```

This opens a browser-based dashboard where you can:
- Run PDD commands visually (including `pdd change`, `pdd bug`, `pdd fix`)
- Browse and edit prompts, code, and tests
- Access your session remotely via PDD Cloud

### Issue-Driven CLI

For command-line users, implement GitHub issues directly:

```bash
# Feature requests
pdd change https://github.com/owner/repo/issues/123

# Bug reports
pdd bug https://github.com/owner/repo/issues/456
pdd fix https://github.com/owner/repo/issues/456
```

**Prerequisites for Issue-Driven CLI:**

1. **GitHub CLI** - Required for issue access:
   ```bash
   brew install gh && gh auth login
   ```

2. **One Agentic CLI** - Required to run the workflows (install at least one):
   - **Claude Code**: `npm install -g @anthropic-ai/claude-code` (requires `ANTHROPIC_API_KEY`)
   - **Gemini CLI**: `npm install -g @google/gemini-cli` (requires `GOOGLE_API_KEY`)
   - **Codex CLI**: `npm install -g @openai/codex` (requires `OPENAI_API_KEY`)

### Manual Prompt Workflow

For working with existing prompt files:
```bash
pdd sync module_name
```

See [README.md](../README.md) for complete command documentation.

---

## Testing Prompts with `prompt_tester.py`

A key part of developing with PDD is ensuring your prompts are robust and reliable. The repository includes a powerful tool, `tests/prompt_tester.py`, designed for this purpose. It allows you to test a prompt against a suite of test cases defined in a CSV file and evaluate its performance.

### How It Works

The `prompt_tester.py` script takes a prompt file and a CSV file of test cases. For each row in the CSV, it:

1. Runs the specified prompt with the `input_variables` from the row.
2. Compares the `actual_output` from the LLM with the `expected_output` from the row.
3. **Advanced Comparison:** If the outputs don't match exactly, it uses a more powerful LLM to perform a *semantic comparison*. It determines if the actual output is equivalent in meaning to the expected output, which is perfect for robustness testing.

### Step-by-Step Guide

#### 1. Create a Test Case CSV File

First, create a CSV file to define your test cases. For example, you could create `tests/csv/my_prompt_tests.csv`.

The CSV file must contain these columns:

- `test_case_name`: A brief, human-readable description of the test.
- `input_variables`: A JSON string representing the dictionary of variables your prompt expects.
- `expected_output`: The "golden" or ideal output you expect the prompt to generate.

**Example: Testing a Summarization Prompt**

Imagine you have a prompt that summarizes text. Your CSV file (`tests/csv/summarization_tests.csv`) might look like this:

```csv
test_case_name,input_variables,expected_output
"Baseline summarization","{""text"": ""The quick brown fox jumps over the lazy dog. This famous sentence contains all the letters of the English alphabet.""}", "A sentence about a fox jumping over a dog contains all letters of the alphabet."
"Robustness test with typo","{""text"": ""The quik brown fox jumps over the lazy dog. This famous sentence contains all the letters of the English alphabet.""}", "A sentence about a fox jumping over a dog contains all letters of the alphabet."
"Robustness test with different phrasing","{""text"": ""A well-known sentence about a speedy brown fox leaping over a tired canine includes every letter in the English alphabet.""}", "A sentence about a fox jumping over a dog contains all letters of the alphabet."
```

In this example, we test a baseline case and then two "robustness" cases where the input is slightly different, but the core meaning and expected summary remain the same.

#### 2. Run the Prompt Tester

Execute the script from the root of the project using the following command. Make sure your conda environment is active.

```bash
# General usage
python -m tests.prompt_tester <prompt_name> --csv_file <path_to_your_csv>

# Example using the summarization test
python -m tests.prompt_tester summarize_LLM --csv_file tests/csv/summarization_tests.csv
```

- Replace `<prompt_name>` with the name of the prompt file (without the `.prompt` extension).
- Replace `<path_to_your_csv>` with the path to the CSV file you created.

#### 3. Analyze the Results

The script will print a detailed, color-coded report to the console for each test case, showing:

- **PASS** or **FAIL**.
- The expected output vs. the actual output.
- A `diff` view highlighting the exact differences for failed tests.
- The reasoning from the LLM judge if a semantic comparison was performed.

This allows you to quickly identify which cases are failing and why, so you can refine your prompt accordingly.

## Claiming Issues

Before starting work on an issue, claim it to avoid duplicate effort.

### How to Claim an Issue

1. **Comment on the issue** with your intent to work on it
2. **Include your GitHub handle** so others know who's working on it
3. **Set a target completion date** to help maintainers track progress

**Example claiming comment:**
```
I'd like to work on this issue.

Assignee: @username
Target completion: 2024-01-20
```

If you have repository permissions, also assign yourself to the issue. Otherwise, a maintainer will assign you.

### Keeping Issues Updated

- Post progress updates if your timeline changes
- If you can no longer work on an issue, comment to release it for others
- Maintainers may reassign stale issues on a case-by-case basis

### Implementing Issues with PDD

After claiming an issue, use PDD to implement it:

**Using the Web Interface:**
```bash
pdd connect
# Then run `pdd change <url>` or `pdd bug <url>` through the command interface
```

**Using CLI:**
```bash
# For feature requests
pdd change https://github.com/promptdriven/pdd/issues/XXX

# For bug reports
pdd bug https://github.com/promptdriven/pdd/issues/XXX
pdd fix https://github.com/promptdriven/pdd/issues/XXX
```

PDD will create an isolated worktree, implement changes, and generate a PR automatically. Review the PR, refine if needed, then request human review.

## Pull Request Completeness Checklist

Before submitting a PR, ensure you have completed all applicable items. Incomplete PRs will be sent back for revisions.

### Required for ALL PRs

- [ ] **All tests pass** - Run the full test suite:

  ```bash
  pytest -vv tests/
  ```
- [ ] **Regression tests pass** - Run both regression suites:

  ```bash
  make regression        # ~20 min
  make sync-regression   # ~15 min
  ```
- [ ] **Test coverage reported** - Include coverage numbers in your PR description:

  ```bash
  make coverage
  ```
- [ ] **Copilot/automated review comments addressed** - Review and resolve all automated review comments before requesting human review

  **Tip:** Use an agentic coding tool (Claude Code, Cursor, Gemini CLI, etc.) to automatically fix Copilot comments:

  ```bash
  # Example with Claude Code
  claude: "Review and fix the Copilot comments (that make sense) on my PR: https://github.com/promptdriven/pdd/pull/XXX. Respond to the comments"
  ```
- [ ] **No temp/backup files committed** - Remove any `.bak`, `*_backup*`, `*.pyc`, cache directories, or test output files from your commits
- [ ] **No warnings** - Fix any pytest warnings or linting issues:

  ```bash
  make lint
  ```
- [ ] **No merge conflicts** - Rebase on latest `main` and resolve all conflicts before requesting review

- [ ] **PR linked to GitHub issue** - Reference the issue in your PR description using keywords like `Fixes #123` or `Closes #123`. This automatically closes the issue when the PR is merged.

### Required for Bug Fixes

- [ ] **Failing test reproduces the bug** - Write a test that fails before your fix and passes after. This proves the fix works.

### Required for New Features

**Before implementation**, follow the documentation-first workflow:

1. [ ] **Update documentation first** - Before writing code, update the README or relevant docs to describe:
   - What the feature does
   - How users will use it (CLI flags, API, etc.)
   - Example usage and expected output

2. [ ] **Post to Discord for feedback** - Share your documentation changes in the `#feedback` channel to get early review from maintainers. This prevents wasted effort on features that need changes.

3. [ ] **Wait for approval** - Get a 👍 or approval comment before starting implementation

4. [ ] **Use docs to drive prompt changes** - Your approved documentation describes the intended behavior. Use it to guide your prompt modifications in `pdd_cap`.

**After implementation:**

- [ ] **Manual testing performed** - Document what manual testing you did in the PR description
- [ ] **A/B comparison provided** - For significant features, show before/after examples demonstrating the improvement
- [ ] **Final documentation review** - Ensure docs match the actual implementation

### Required if Prompt Files Changed

- [ ] **Prompt changes submitted to pdd_cap** - If you modified any `.prompt` files, submit corresponding changes to the [pdd_cap repository](https://github.com/promptdriven/pdd_cap)

### PR Description

Use **GitHub Copilot** to auto-generate your PR description:

1. When creating a PR, click the Copilot icon (sparkle) in the description field
2. Copilot will analyze your commits and generate a summary
3. Review and edit the generated description to ensure accuracy
4. Add the following sections that Copilot may not include:

**Required sections to add/verify:**

- **Test Results** - Include actual pass/fail status and coverage percentage
- **Manual Testing** - Describe any manual testing performed
- **Checklist** - Confirm all applicable items are complete
- **Issue Link** - Reference the GitHub issue (e.g., "Fixes #123")

**Example PR description structure:**

```markdown
## Summary
[Copilot-generated or manual summary of changes]

## Test Results
- Unit tests: PASS
- Regression tests: PASS
- Sync regression: PASS
- Test coverage: 84%

## Manual Testing
[Describe manual testing performed, or "N/A" for pure refactors]

## Checklist
- [x] All tests pass
- [x] Copilot comments addressed
- [x] No temp files committed
- [x] No merge conflicts
- [ ] (If bug fix) Failing test added
- [ ] (If feature) A/B comparison included
- [ ] (If prompts changed) Submitted to pdd_cap

Fixes #123
```

---

## Next Steps

1. **Launch the web interface**: `pdd connect` to explore PDD visually
2. **Try implementing an issue**: Pick one from [GitHub Issues](https://github.com/promptdriven/pdd/issues)
3. Join the PDD community on Discord
4. For manual workflows, see examples in `examples/` directory
5. Read the [Issue-Driven Development Tutorial](./TUTORIALS.md#issue-driven-development-tutorial)

---

## Developer Setup (Contributing to PDD)

If you're contributing to the PDD project, follow these additional setup steps to install development dependencies and run tests efficiently.

> **Important: UV vs Conda**
>
> - **End users** install PDD via UV: `uv tool install pdd-cli`
> - **Developers/contributors** must use a **Conda environment** for development
>
> UV creates isolated environments per-package (great for production), but development requires a mutable environment where you can modify PDD source code and see changes immediately.

### 1. Create a Conda Environment for Development

**Create and activate the pdd conda environment:**

```bash
# Create a new conda environment named 'pdd' with Python 3.11+
conda create -n pdd python=3.12
conda activate pdd
```

### 2. Install Development Dependencies

The project uses optional development dependencies defined in `pyproject.toml` for testing, code quality, and build tools.

**Install all development dependencies:**

```bash
# Make sure you're in the project root and pdd conda environment is active
conda activate pdd

# Install the package in editable mode with dev dependencies
pip install -e ".[dev]"
```

**What this installs:**

- **pytest-cov**: Code coverage reporting
- **pytest-testmon**: Smart test selection (only runs tests affected by changes)
- **pytest-xdist**: Parallel test execution for faster runs
- **pytest-mock**: Mocking utilities for unit tests
- **pytest-asyncio**: Support for async test functions
- **z3-solver**: Formal verification tools
- **commitizen**: Conventional commits and versioning
- **build, twine**: Package building and publishing tools

### 2. Enable Test Caching and Smart Execution

**Use testmon for incremental testing:**

```bash
# First run (creates cache)
pytest --testmon

# Subsequent runs (only tests affected by changes)
pytest --testmon
```

**Use xdist for parallel execution:**

```bash
# Run tests in parallel (auto-detect CPU cores)
pytest -n auto

# Run with specific number of workers
pytest -n 4

# Combine with coverage
pytest -n auto --cov=pdd --cov-report=html
```

**Combine both for maximum efficiency:**

```bash
# Smart selection + parallel execution
pytest --testmon -n auto
```

### 3. Run Tests with Coverage

**Generate coverage reports:**

```bash
# Run tests with coverage
make coverage

# Or manually
pytest --cov=pdd --cov-report=term --cov-report=html

# View HTML report
open htmlcov/index.html  # macOS
xdg-open htmlcov/index.html  # Linux
```

### 4. Run Regression Tests

**Recommended test execution order:**
Run tests in this order to catch issues early:

1. **Unit tests first:** `make test` or `pytest -vv tests/` (17 min)
2. **All regression tests:** `make all-regression` (45 min total)
   - Or run individually: `regression` (20 min), `sync-regression` (15 min), `cloud-regression` (10 min)

**Sync regression tests:**

```bash
make sync-regression

# Or run directly
./tests/sync_regression.sh
```

### 5. Lint and Code Quality

**Run linting:**

```bash
# Run pylint on all pdd modules
make lint

# Or on specific module
pylint pdd/code_generator.py
```

### 6. Build and Install Locally

**Build the package:**

```bash
make build
# Creates wheel in dist/
```

**Install locally for testing:**

```bash
make install
# Installs the local build
```

### 7. Developer Workflow Tips

**Efficient test workflow:**

```bash
# 1. During development - fast feedback loop
pytest -k test_my_feature --testmon

# 2. Before committing - run affected tests in parallel
pytest --testmon -n auto

# 3. Before pushing - full test suite with coverage
make test
make coverage

# 4. Final check - regression tests
make regression
```

**Clear test caches if needed:**

```bash
# Remove pytest cache
rm -rf .pytest_cache

# Remove testmon cache
rm -rf .testmondata

# Remove coverage data
rm -rf .coverage htmlcov/
```

### 8. Git Workflow with Commitizen

**Make commits following conventional commits:**

```bash
# Stage your changes
git add .

# Use commitizen for structured commits
cz commit

# Or use git commit with conventional format
git commit -m "feat: add new feature"
git commit -m "fix: resolve bug in module"
git commit -m "docs: update documentation"
```

**Bump version (maintainers only):**

```bash
# Automatically bump version and update CHANGELOG
cz bump

# Push with tags
git push --follow-tags
```

### 9. Troubleshooting Development Setup

**"pytest: command not found":**

```bash
# Reinstall dev dependencies
pip install -e ".[dev]"
```

**"ModuleNotFoundError" during tests:**

```bash
# Verify PDD_PATH is set
echo $PDD_PATH

# Reinstall in editable mode
pip install -e .
```

**Tests are slow:**

```bash
# Use parallel execution
pytest -n auto

# Use testmon for smart test selection
pytest --testmon -n auto
```

**Coverage reports missing:**

```bash
# Install coverage dependencies
pip install pytest-cov

# Run with coverage flags
pytest --cov=pdd --cov-report=html
```

## Understanding PDD's File Structure

Before troubleshooting, it's helpful to understand where PDD stores different types of files:

### Directory Layout

```
pdd/                          # Main project directory
├── prompts/                  # Prompt templates (root level)
├── data/                     # CSV configuration files (root level)
├── pdd/                      # Source code directory
│   ├── prompts -> ../prompts/  # Symbolic link (must exist!)
│   └── data -> ../data/        # Symbolic link (must exist!)
├── context/                  # Generated examples and context
├── output/                   # Command outputs
├── staging/                  # Regression test logs
│   └── regression_YYYYMMDD_HHMMSS/
├── tests/                    # Test files
└── examples/                 # Example projects
```

### Cache Files (Can Be Safely Deleted)

PDD caches LLM responses to save costs and improve performance:

- `litellm_cache.sqlite/` - LLM response cache (root level)
- `pdd/litellm_cache.sqlite/` - LLM response cache (pdd directory)
- `__pycache__/` - Python bytecode cache
- `*.pyc` - Compiled Python files

**To clear all caches:**

```bash
rm -rf litellm_cache.sqlite pdd/litellm_cache.sqlite
find . -name "*.pyc" -delete && find . -name "__pycache__" -type d -exec rm -rf {} + 2>/dev/null || true
rm -rf staging/regression_*
```

---

## Troubleshooting

This section helps you diagnose and fix common setup issues. Start by identifying your symptoms below.

### Quick Diagnostic Checklist

Run these commands to check your setup:

```bash
# 1. Check if you're in the right environment
conda env list
# Look for * next to 'pdd'

# 2. Verify PDD is installed and accessible
pdd --version

# 3. Check symbolic links exist
ls -la pdd/prompts pdd/data
# Should show: prompts -> ../prompts and data -> ../data

# 4. Verify PDD_PATH is set
echo $PDD_PATH
# Should show: /absolute/path/to/your/pdd

# 5. Test Python can import PDD
python -c "import pdd; print('PDD imports correctly')"
```

---

### "Command not found: pdd"

**What this means:** Your terminal can't find the PDD command.

**Quick fix:**

```bash
# Activate the conda environment
conda activate pdd

# Verify it worked
pdd --version
```

**If still not working:**

- Make sure you completed step 2 in Installation (`uv tool install pdd-cli`)
- Try restarting your terminal
- Check if UV is installed: `uv --version`

---

### "ModuleNotFoundError" or "Failed to load prompt template"

**What this means:** PDD can't find its configuration files or prompts.

**Root cause:** Missing or broken symbolic links in the `pdd/` directory.

**Fix it:** Re-run the symbolic link creation steps from **"Final Project Configuration → Step 1: Create Symbolic Links"** above.

**Verify the fix:**

```bash
ls -la pdd/prompts pdd/data
# Should show: lrwxr-xr-x prompts -> ../prompts
#              lrwxr-xr-x data -> ../data
```

---

### Import Errors or "Cannot import name X from pdd"

**What this means:** Python can't find the PDD modules or is using the wrong version.

**Common causes:**

1. `PDD_PATH` environment variable not set
2. Conflicting PYTHONPATH settings
3. Running from wrong directory

**Fix:** Follow the `PDD_PATH` setup steps from **"Final Project Configuration → Step 2 or Step 3"** above. Choose either:

- **Step 2**: Set `PDD_PATH` in a `.env` file
- **Step 3**: Set `PDD_PATH` in Conda environment (recommended for WSL)

**Verify the fix:**

```bash
echo $PDD_PATH
python -c "import pdd; print('Success!')"
```

---

### "API key not found" or "Quota exceeded"

**What this means:** PDD can't access your LLM provider API keys, or you're hitting rate limits.

**Understanding API key priority:**
PDD checks for API keys in this order (highest priority first):

1. **Infisical secrets** (when using `infisical run --`)
2. **`~/.pdd/llm_model.csv`** (user-specific model registry)
3. **`.env` file** (project root)
4. **Shell environment variables**

**Fix for "quota exceeded":**

```bash
# Check if you have a user-specific model file that might be using a rate-limited model
ls -la ~/.pdd/llm_model.csv

# If it exists, remove it to use project defaults
rm -f ~/.pdd/llm_model.csv
```

**Fix for "API key not found":**

**Recommended:** Run the setup wizard to detect and fix missing API keys:
```bash
pdd setup
```

The wizard will:
- Scan all sources (shell, .env, ~/.pdd files) and show which keys are missing
- Let you add missing keys with immediate validation
- Show exactly where each key is loaded from for transparency

**Manual fixes:**
- If using **Infisical**: Follow **"Step 7: Set Up Infisical for Secrets Management"** above to configure your API keys
- If using **.env file**: Ensure your `.env` file in the project root contains your API keys (e.g., `OPENAI_API_KEY=sk-...`)

**Verify keys are loaded:**

```bash
infisical run -- env | grep API_KEY  # If using Infisical
# OR
env | grep API_KEY  # If using .env
# OR
pdd setup  # Shows scan of all keys with source transparency
```

**Note on API key requirements for testing:**
Some tests require multiple API providers. If you only have a single API key (e.g., only Gemini), some tests may fail with errors like "OpenAI API key not found." For full test compatibility, we recommend having API keys for at least:

- OpenAI (OPENAI_API_KEY)
- One additional provider (e.g., GEMINI_API_KEY or ANTHROPIC_API_KEY)

---

### Tests Fail with "[Errno 2] No such file or directory" (WSL Users)

**What this means:** Windows Subsystem for Linux has path translation issues.

**Quick fix:**

```bash
# Set this environment variable before running tests
export TEST_LOCAL=true
./tests/regression.sh

# Or with Infisical:
export TEST_LOCAL=true
infisical run -- make regression
```

**Why this happens:** WSL paths like `/mnt/c/...` sometimes don't translate correctly between Windows and Linux.

---

### "Validation errors for CodeFix" (Advanced Issue)

**What this means:** The LLM returned a response that doesn't match the expected format.

**Full error example:**

```
ValueError: 4 validation errors for CodeFix
  update_program: Field required
  update_code: Field required
  fixed_program: Field required
  fixed_code: Field required
```

**When this occurs:**

- Using the `pdd crash` command
- With models that have `structured_output: False` in `data/llm_model.csv`
- Examples: DeepSeek R1, Qwen3 Coder, local MLX models

**Fix:**
Use a model with better structured output support:

```bash
# Check which models have structured_output: True
cat data/llm_model.csv | grep "True"

# Recommended models:
# - GPT-5
# - Claude Sonnet 4.5
# - Gemini 2.5 Pro
```

**Technical details (for developers):**

- File: `pdd/fix_code_module_errors.py` (lines 131-135)
- Prompt: `prompts/extract_program_code_fix_LLM.prompt`
- The LLM must return valid JSON with specific required fields

---

### General Troubleshooting Steps

If you're still having issues after trying the specific fixes above:

1. **Re-run the installation and configuration steps** from the beginning of this guide
2. **Clear all caches** (see **"Understanding PDD's File Structure → Cache Files"** above)
3. **Check documentation:**

   - [README](https://github.com/promptdriven/pdd/blob/main/README.md) - Detailed setup instructions
   - [Whitepaper](./whitepaper.md) - Core concepts and architecture
   - [Prompting Guide](./prompting_guide.md) - How to write effective prompts
4. **Get help:**

   - [GitHub Issues](https://github.com/promptdriven/pdd/issues) - Search existing issues
   - [Discord Community](https://discord.gg/Q7Ts5Qt3) - Ask questions and get support

---

### Verify Your Setup Is Complete

Run this comprehensive check:

```bash
#!/bin/bash
echo "PDD Setup Verification"
echo "========================="
echo ""

echo "1. Conda Environment:"
conda env list | grep pdd && echo "[PASS] pdd environment exists" || echo "[FAIL] pdd environment not found"
echo ""

echo "2. PDD Command:"
pdd --version && echo "[PASS] PDD command works" || echo "[FAIL] PDD command not found"
echo ""

echo "3. Symbolic Links:"
ls -la pdd/prompts pdd/data 2>/dev/null && echo "[PASS] Symbolic links exist" || echo "[FAIL] Symbolic links missing"
echo ""

echo "4. PDD_PATH:"
[ -n "$PDD_PATH" ] && echo "[PASS] PDD_PATH is set: $PDD_PATH" || echo "[FAIL] PDD_PATH not set"
echo ""

echo "5. Python Import:"
python -c "import pdd" 2>/dev/null && echo "[PASS] Python can import pdd" || echo "[FAIL] Import failed"
echo ""

echo "6. API Keys (Infisical):"
infisical run -- env | grep -q API_KEY && echo "[PASS] API keys available" || echo "[WARN] API keys not detected (may be in .env)"
echo ""

echo "========================="
echo "Setup verification complete!"
```

Save this as `verify_setup.sh`, make it executable with `chmod +x verify_setup.sh`, and run it with `./verify_setup.sh`.
