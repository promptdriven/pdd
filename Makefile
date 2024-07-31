# Certainly! Below is a Makefile that adheres to the rules and directory structure you provided. This Makefile uses wildcards to ensure all files are found and generated, and it handles different file extensions based on the prompt file names.

# ```Makefile
# Variables
PROMPTS_DIR := prompts
STAGING_DIR := staging
PDD_SCRIPT := pdd/pdd.py

# Wildcards for different types of prompts
PYTHON_PROMPTS := $(wildcard $(PROMPTS_DIR)/*_python.prompt)
CSV_PROMPTS := $(wildcard $(PROMPTS_DIR)/*_csv.prompt)
MAKEFILE_PROMPTS := $(wildcard $(PROMPTS_DIR)/*_makefile.prompt)

# Output files
PYTHON_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_python.prompt,$(STAGING_DIR)/pdd/%.py,$(PYTHON_PROMPTS))
CSV_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_csv.prompt,$(STAGING_DIR)/data/%.csv,$(CSV_PROMPTS))
MAKEFILE_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_makefile.prompt,$(STAGING_DIR)/%,$(MAKEFILE_PROMPTS))

# Default target
all: generate

# Generate all files
generate: $(PYTHON_OUTPUTS) $(CSV_OUTPUTS) $(MAKEFILE_OUTPUTS)

# Rule to generate Python files
$(STAGING_DIR)/pdd/%.py: $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating Python file: $@"
	python $(PDD_SCRIPT) -o $@ $<

# Rule to generate CSV files
$(STAGING_DIR)/data/%.csv: $(PROMPTS_DIR)/%_csv.prompt
	@echo "Generating CSV file: $@"
	python $(PDD_SCRIPT) -o $@ $<

# Rule to generate Makefile
$(STAGING_DIR)/%: $(PROMPTS_DIR)/%_makefile.prompt
	@echo "Generating Makefile: $@"
	python $(PDD_SCRIPT) -o $@ $<

# Clean generated files
clean:
	@echo "Cleaning generated files..."
	rm -f $(PYTHON_OUTPUTS) $(CSV_OUTPUTS) $(MAKEFILE_OUTPUTS)

# Generate requirements.txt using pipreqs
requirements.txt:
	@echo "Generating requirements.txt..."
	pipreqs . --force

# Copy files from staging to production
production: generate
	@echo "Copying files from staging to production..."
	cp -r $(STAGING_DIR)/* .

# Test
test:
	@echo "Running tests..."
	jupyter nbconvert --to notebook --execute tests/testing.ipynb

# Help
help:
	@echo "Usage:"
	@echo "  make generate       Generate all files from prompts"
	@echo "  make clean          Clean generated files"
	@echo "  make requirements   Generate requirements.txt"
	@echo "  make production     Copy files from staging to production"
	@echo "  make test           Run tests"
	@echo "  make help           Show this help message"

.PHONY: all generate clean requirements production test help
# ```

# ### Explanation:
# 1. **Variables**:
#    - `PROMPTS_DIR`: Directory containing the prompt files.
#    - `STAGING_DIR`: Directory where generated files will be placed.
#    - `PDD_SCRIPT`: Path to the `pdd.py` script.

# 2. **Wildcards**:
#    - `PYTHON_PROMPTS`, `CSV_PROMPTS`, `MAKEFILE_PROMPTS`: Wildcards to find all prompt files of different types.

# 3. **Output Files**:
#    - `PYTHON_OUTPUTS`, `CSV_OUTPUTS`, `MAKEFILE_OUTPUTS`: Output file paths based on the prompt files.

# 4. **Default Target**:
#    - `all`: Default target that depends on the `generate` target.

# 5. **Generate Targets**:
#    - Rules to generate Python, CSV, and Makefile outputs using the `pdd.py` script.

# 6. **Clean**:
#    - Removes all generated files.

# 7. **Requirements**:
#    - Generates `requirements.txt` using `pipreqs`.

# 8. **Production**:
#    - Copies files from the staging directory to the production directory.

# 9. **Test**:
#    - Runs tests using Jupyter Notebook.

# 10. **Help**:
#     - Provides a help message with usage instructions.

# This Makefile should cover the requirements you specified and handle the generation, testing, cleaning, and production tasks effectively.