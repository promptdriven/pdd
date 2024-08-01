# Directories
PROMPT_DIR := prompts
STAGING_DIR := staging
PDD_DIR := pdd
CONTEXT_DIR := context
DATA_DIR := data
TEST_DIR := tests

# Python script
PDD_SCRIPT := $(PDD_DIR)/pdd.py

# Wildcards for different file types
PYTHON_PROMPTS := $(wildcard $(PROMPT_DIR)/*_python.prompt)
MAKEFILE_PROMPTS := $(wildcard $(PROMPT_DIR)/*_makefile.prompt)
CSV_PROMPTS := $(wildcard $(PROMPT_DIR)/*_csv.prompt)

PYTHON_OUTPUTS := $(patsubst $(PROMPT_DIR)/%_python.prompt,$(STAGING_DIR)/$(PDD_DIR)/%.py,$(PYTHON_PROMPTS))
MAKEFILE_OUTPUTS := $(patsubst $(PROMPT_DIR)/%_makefile.prompt,$(STAGING_DIR)/%,$(MAKEFILE_PROMPTS))
CSV_OUTPUTS := $(patsubst $(PROMPT_DIR)/%_csv.prompt,$(STAGING_DIR)/$(DATA_DIR)/%.csv,$(CSV_PROMPTS))

EXAMPLE_SOURCES := $(wildcard $(STAGING_DIR)/$(PDD_DIR)/*.py)
EXAMPLE_OUTPUTS := $(patsubst $(STAGING_DIR)/$(PDD_DIR)/%.py,$(STAGING_DIR)/$(CONTEXT_DIR)/%_example.py,$(EXAMPLE_SOURCES))

# Default target
all: generate test

# Generate all files
generate: python_files makefile_files csv_files example_files

# Generate Python files
python_files: $(PYTHON_OUTPUTS)

$(STAGING_DIR)/$(PDD_DIR)/%.py: $(PROMPT_DIR)/%_python.prompt
	@mkdir -p $(@D)
	@echo "Generating $@"
	@python $(PDD_SCRIPT) $< -o $@ --force

# Generate Makefile
makefile_files: $(MAKEFILE_OUTPUTS)

$(STAGING_DIR)/%: $(PROMPT_DIR)/%_makefile.prompt
	@mkdir -p $(@D)
	@echo "Generating $@"
	@python $(PDD_SCRIPT) $< -o $@ --force

# Generate CSV files
csv_files: $(CSV_OUTPUTS)

$(STAGING_DIR)/$(DATA_DIR)/%.csv: $(PROMPT_DIR)/%_csv.prompt
	@mkdir -p $(@D)
	@echo "Generating $@"
	@python $(PDD_SCRIPT) $< -o $@ --force

# Generate example files
example_files: $(EXAMPLE_OUTPUTS)

$(STAGING_DIR)/$(CONTEXT_DIR)/%_example.py: $(STAGING_DIR)/$(PDD_DIR)/%.py
	@mkdir -p $(@D)
	@echo "Generating example for $<"
	@python $(PDD_SCRIPT) $< -oe $@ --force

# Run tests
test:
	@echo "Running tests"
	@jupyter nbconvert --to notebook --execute $(TEST_DIR)/testing.ipynb

# Clean generated files
clean:
	@echo "Cleaning generated files"
	@rm -rf $(STAGING_DIR)

# Generate requirements.txt
requirements:
	@echo "Generating requirements.txt"
	@pipreqs . --force

# Production: copy files from staging to pdd
production:
	@echo "Copying files to production"
	@rsync -av --exclude='__pycache__' $(STAGING_DIR)/$(PDD_DIR)/ $(PDD_DIR)/
	@rsync -av $(STAGING_DIR)/$(DATA_DIR)/ $(DATA_DIR)/
	@rsync -av $(STAGING_DIR)/$(CONTEXT_DIR)/ $(CONTEXT_DIR)/

.PHONY: all generate python_files makefile_files csv_files example_files test clean requirements production