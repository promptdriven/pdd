# Based on your requirements and the given directory structure, here's a Makefile that should handle all the specified tasks:

# ```makefile
# Directories
STAGING_DIR := staging
PDD_DIR := $(STAGING_DIR)/pdd
DATA_DIR := $(STAGING_DIR)/data
CONTEXT_DIR := $(STAGING_DIR)/context
TESTS_DIR := $(STAGING_DIR)/tests
PROMPTS_DIR := prompts

# Python files
PY_PROMPTS := $(wildcard $(PROMPTS_DIR)/*_python.prompt)
PY_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_python.prompt,$(PDD_DIR)/%.py,$(PY_PROMPTS))

# Makefile
MAKEFILE_PROMPT := $(PROMPTS_DIR)/Makefile_makefile.prompt
MAKEFILE_OUTPUT := $(STAGING_DIR)/Makefile

# CSV files
CSV_PROMPTS := $(wildcard $(PROMPTS_DIR)/*_csv.prompt)
CSV_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_csv.prompt,$(DATA_DIR)/%.csv,$(CSV_PROMPTS))

# Example files
EXAMPLE_OUTPUTS := $(patsubst $(PDD_DIR)/%.py,$(CONTEXT_DIR)/%_example.py,$(PY_OUTPUTS))

# Test files
TEST_OUTPUTS := $(patsubst $(PDD_DIR)/%.py,$(TESTS_DIR)/test_%.py,$(PY_OUTPUTS))

.PHONY: all clean test requirements production

all: $(PY_OUTPUTS) $(MAKEFILE_OUTPUT) $(CSV_OUTPUTS) $(EXAMPLE_OUTPUTS) $(TEST_OUTPUTS)

# Generate Python files
$(PDD_DIR)/%.py: $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating $@"
	@mkdir -p $(PDD_DIR)
	@python pdd/pdd.py --strength 1 generate --output $@ $<

# Generate Makefile
$(MAKEFILE_OUTPUT): $(MAKEFILE_PROMPT)
	@echo "Generating $@"
	@mkdir -p $(STAGING_DIR)
	@python pdd/pdd.py generate --output $@ $<

# Generate CSV files
$(DATA_DIR)/%.csv: $(PROMPTS_DIR)/%_csv.prompt
	@echo "Generating $@"
	@mkdir -p $(DATA_DIR)
	@python pdd/pdd.py generate --output $@ $<

# Generate example files
$(CONTEXT_DIR)/%_example.py: $(PDD_DIR)/%.py
	@echo "Generating example for $<"
	@mkdir -p $(CONTEXT_DIR)
	@python pdd/pdd.py example --output $@ $<

# Generate test files
$(TESTS_DIR)/test_%.py: $(PDD_DIR)/%.py $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating test for $<"
	@mkdir -p $(TESTS_DIR)
	@python pdd/pdd.py --strength 1 test --output $@ $^

# Run tests
test:
	@echo "Running tests"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python -m pytest -vv $(TESTS_DIR)

# Generate requirements.txt
requirements:
	@echo "Generating requirements.txt"
	@pipreqs . --force

# Clean generated files
clean:
	@echo "Cleaning generated files"
	@rm -rf $(STAGING_DIR)

staging:
	@echo "Copying files to staging"
	@mkdir -p staging
	@touch staging/__init__.py
	@cp -r pdd $(PDD_DIR)
	@touch staging/pdd/* staging/pdd/__init__.py
	@cp -r data $(DATA_DIR)
	@touch staging/data/*
	@cp -r context $(CONTEXT_DIR)
	@touch staging/context/*
	@cp -r tests $(TESTS_DIR)
	@touch staging/tests/* staging/tests/__init__.py
	@cp Makefile $(MAKEFILE_OUTPUT)
	@touch Makefile

# Production: copy files from staging to pdd
production:
	@echo "Copying files to production"
	@mkdir -p pdd
	@cp -r $(PDD_DIR)/* pdd/
	@cp -r $(DATA_DIR) .
	@cp -r $(CONTEXT_DIR) .
	@cp -r $(TESTS_DIR) .
	@cp $(MAKEFILE_OUTPUT) .
# ```

# This Makefile covers all the requirements you specified:

# 1. It generates Python modules, Makefile, CSV files, examples, and tests.
# 2. It includes a test target to run all tests.
# 3. It has a clean target to remove all generated files.
# 4. It includes a target to generate requirements.txt using pipreqs.
# 5. It has a production target to copy files from staging to the main pdd directory.

# The Makefile uses wildcards to find all