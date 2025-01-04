# Directories
PROD_DIR := pdd
STAGING_DIR := .
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

.PHONY: all clean test requirements production coverage staging regression install build analysis

all: $(PY_OUTPUTS) $(MAKEFILE_OUTPUT) $(CSV_OUTPUTS) $(EXAMPLE_OUTPUTS) $(TEST_OUTPUTS)

# Generate Python files
$(PDD_DIR)/%.py: $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating $@"
	@mkdir -p $(PDD_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd --strength 1 generate --output $@ $<

# Generate Makefile
$(MAKEFILE_OUTPUT): $(MAKEFILE_PROMPT)
	@echo "Generating $@"
	@mkdir -p $(STAGING_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd generate --output $@ $<

# Generate CSV files
$(DATA_DIR)/%.csv: $(PROMPTS_DIR)/%_csv.prompt
	@echo "Generating $@"
	@mkdir -p $(DATA_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd generate --output $@ $<

# Generate example files
$(CONTEXT_DIR)/%_example.py: $(PDD_DIR)/%.py
	@echo "Generating example for $<"
	@mkdir -p $(CONTEXT_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd example --output $@ $<

# Generate test files
$(TESTS_DIR)/test_%.py: $(PDD_DIR)/%.py $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating test for $<"
	@mkdir -p $(TESTS_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd --strength 1 test --output $@ $^

# Run tests
test:
	@echo "Running staging tests"
	@cd $(STAGING_DIR)
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python -m pytest -vv $(TESTS_DIR)

# Run tests with coverage
coverage:
	@echo "Running tests with coverage"
	@cd $(STAGING_DIR)
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH pytest --cov=$(PDD_DIR) --cov-report=term-missing --cov-report=html $(TESTS_DIR)

# Generate requirements.txt
requirements:
	@echo "Generating requirements.txt"
	@PYTHONPATH=$(PROD_DIR) pipreqs ./pdd --force --savepath ./requirements.txt
	@PYTHONPATH=$(PROD_DIR) pipreqs ./tests --force --savepath ./tmp_requirements.txt
	@cat ./tmp_requirements.txt ./requirements.txt | sort | uniq > ./final_requirements.txt
	@mv ./final_requirements.txt ./requirements.txt
	@rm ./tmp_requirements.txt

# Clean generated files
clean:
	@echo "Cleaning generated files"
	@rm -rf staging output output.csv pdd/*_[0-9]_[0-9]_[0-9]*.py tests/*_[0-9]_[0-9]_[0-9]*.py

.PHONY: staging
staging:
	@echo "Copying files to staging"
	@mkdir -p staging
	@touch staging/__init__.py
	@cp -r pdd/* $(PDD_DIR)
	@touch staging/pdd/* staging/pdd/__init__.py
	@cp -r data/* $(DATA_DIR)
	@touch staging/data/*
	@cp -r context/* $(CONTEXT_DIR)
	@touch staging/context/*
	@cp -r tests/* $(TESTS_DIR)
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

regression:
	@echo "Running regression tests"
	@mkdir -p staging/regression
	@@find staging/regression -type f ! -name ".*" -delete
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/regression.sh

install:
	@echo "Installing pdd"
	@pip install -e .

build:
	@echo "Building pdd"
	@python -m build

analysis:
	@echo "Running regression analysis"
	@mkdir -p staging/regression
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH pdd --strength 1 generate --output staging/regression/regression_analysis.log prompts/regression_analysis_log.prompt
	@echo "Analysis results:"
	@python -c "from rich.console import Console; from rich.syntax import Syntax; console = Console(); content = open('staging/regression/regression_analysis.log').read(); syntax = Syntax(content, 'python', theme='monokai', line_numbers=True); console.print(syntax)"