# To create a Makefile that handles generating Python modules, tests, context, testing, and cleaning, we can define several targets. These targets will include generating code from prompts, running tests, and cleaning up generated files and compiled bytecode.

# Here's a Makefile that accomplishes these tasks:

# ```Makefile
# Define directories
PROMPTS_DIR := prompts
CONTEXT_DIR := context
PDD_DIR := pdd
STAGING_DIR := staging
TESTS_DIR := tests

# Define Python interpreter
PYTHON := python

# Define the pdd script
PDD_SCRIPT := $(PDD_DIR)/pdd.py

# Define the prompt files
PROMPT_FILES := $(wildcard $(PROMPTS_DIR)/*.prompt)

# Define the output files
OUTPUT_FILES := $(patsubst $(PROMPTS_DIR)/%.prompt, $(STAGING_DIR)/pdd/%.py, $(PROMPT_FILES))

# Help target
.PHONY: help
help:
	@echo "Available targets:"
	@echo "  generate    - Generate Python modules from prompts"
	@echo "  test        - Run tests"
	@echo "  clean       - Clean generated files and bytecode"
	@echo "  help        - Show this help message"

# Generate Python modules from prompts
.PHONY: generate
generate: $(OUTPUT_FILES)

$(STAGING_DIR)/pdd/%.py: $(PROMPTS_DIR)/%.prompt
	@mkdir -p $(dir $@)
	$(PYTHON) $(PDD_SCRIPT) -o $@ $<

# Run tests
.PHONY: test
test:
	$(PYTHON) -m unittest discover -s $(TESTS_DIR)

# Clean generated files and bytecode
.PHONY: clean
clean:
	@echo "Cleaning generated files and bytecode..."
	@find $(STAGING_DIR) -name '*.pyc' -delete
	@find $(STAGING_DIR) -name '__pycache__' -delete
	@find $(STAGING_DIR) -type f -name '*.py' -delete
	@find $(CONTEXT_DIR) -name '*.pyc' -delete
	@find $(CONTEXT_DIR) -name '__pycache__' -delete
	@find $(CONTEXT_DIR) -type f -name '*_example.py' -delete

# Default target
.DEFAULT_GOAL := help
# ```

# ### Explanation:

# 1. **Directories and Variables**:
#    - `PROMPTS_DIR`, `CONTEXT_DIR`, `PDD_DIR`, `STAGING_DIR`, `TESTS_DIR`: Define the directories used in the project.
#    - `PYTHON`: Define the Python interpreter.
#    - `PDD_SCRIPT`: Path to the `pdd.py` script.
#    - `PROMPT_FILES`: List of all prompt files in the `prompts` directory.
#    - `OUTPUT_FILES`: List of output files to be generated in the `staging/pdd` directory.

# 2. **Help Target**:
#    - Provides a help message listing available targets.

# 3. **Generate Target**:
#    - Generates Python modules from prompt files using the `pdd.py` script.
#    - Uses pattern rules to match prompt files to their corresponding output files.

# 4. **Test Target**:
#    - Runs tests using Python's `unittest` module.

# 5. **Clean Target**:
#    - Cleans up generated files and bytecode.
#    - Uses `find` to delete `.pyc` files, `__pycache__` directories, and generated Python files.

# 6. **Default Target**:
#    - Sets the default target to `help` to display the help message when `make` is run without arguments.

# This Makefile provides a structured way to manage the generation of Python modules, running tests, and cleaning up the project directory.