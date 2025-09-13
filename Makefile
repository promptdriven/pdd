# Directories
PROD_DIR := pdd
STAGING_DIR := .
PDD_DIR := $(STAGING_DIR)/pdd
DATA_DIR := $(STAGING_DIR)/data
CONTEXT_DIR := $(STAGING_DIR)/context
TESTS_DIR := $(STAGING_DIR)/tests
PROMPTS_DIR := prompts

# Default target
.PHONY: help
help:
	@echo "PDD Makefile Help"
	@echo "================="
	@echo ""
	@echo "Generation Commands:"
	@echo "  make generate [MODULE=name]  - Generate specific module or all files"
	@echo "  make run-examples            - Run all example files"
	@echo ""
	@echo "Testing Commands:"
	@echo "  make test                    - Run staging tests"
	@echo "  make coverage                - Run tests with coverage"
	@echo "  make regression [TEST_NUM=n] - Run regression tests (optionally specific test number)"
	@echo "  make sync-regression [TEST_NUM=n] - Run sync regression tests (optionally specific test number)"
	@echo "  make all-regression 		  - Run all regression test suites"
	@echo "  make analysis                - Run regression analysis"
	@echo "  make verify MODULE=name      - Verify code functionality against prompt intent"
		@echo "  make lint                    - Run pylint for static code analysis"
		@echo ""
		@echo "Public repo helpers:"
		@echo "  make public-update           - Ensure and update local public repo clone ($(PUBLIC_PDD_REPO_DIR))"
		@echo "  make public-import ITEM=path - Copy file/dir from public clone into this repo (e.g., ITEM=pdd/examples/SETUP_WITH_GEMINI.md)"
		@echo "  make public-diff ITEM=path   - Show diff between public clone file and local file (uses same ITEM rules)"
	@echo "Fixing & Maintenance:"
	@echo "  make fix [MODULE=name]       - Fix prompts command"
	@echo "  make crash MODULE=name       - Fix crashes in code"
	@echo "  make detect CHANGE_FILE=path  - Detect which prompts need changes based on a description file"
	@echo "  make change CHANGE_PROMPT=path CODE_FILE=path PROMPT_FILE=path [OUTPUT_FILE=path] - Modify a single prompt file"
	@echo "  make change CSV_FILE=path [CODE_DIR=path] [OUTPUT_LOCATION=path] - Modify prompts in batch via CSV (CODE_DIR defaults to ./pdd)"
	@echo "  make requirements            - Generate requirements.txt"
	@echo "  make clean                   - Clean generated files"
	@echo ""
	@echo "Build & Deployment:"
	@echo "  make install                 - Install pdd"
	@echo "  make build                   - Build pdd package"
	@echo "  make publish                 - Build & upload current version"
	@echo "  make publish-public          - Copy artifacts to public repo only"
	@echo "  make release                 - Bump version and build package"
	@echo "  make staging                 - Copy files to staging"
	@echo "  make production              - Copy files from staging to pdd"
	@echo "  make update-extension        - Update VS Code extension"
 
# Public repo paths (override via env if needed)
PUBLIC_PDD_REPO_DIR ?= staging/public/pdd
PUBLIC_PDD_REMOTE ?= https://github.com/promptdriven/pdd.git
# Top-level files to publish if present
PUBLIC_ROOT_FILES ?= LICENSE CHANGELOG.md CONTRIBUTING.md requirements.txt pyproject.toml .env.example README.md .gitignore
# Include core unit tests by default
PUBLIC_COPY_TESTS ?= 1
PUBLIC_TEST_INCLUDE ?= tests/test_*.py tests/__init__.py
PUBLIC_TEST_EXCLUDE ?= tests/regression* tests/sync_regression* tests/**/regression* tests/**/sync_regression* tests/**/*.ipynb tests/csv/**
PUBLIC_COPY_CONTEXT ?= 1
PUBLIC_CONTEXT_INCLUDE ?= context/*_example.py
PUBLIC_CONTEXT_EXCLUDE ?= context/**/__pycache__ context/**/*.log context/**/*.csv

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

# All Example files in context directory
EXAMPLE_FILES := $(wildcard $(CONTEXT_DIR)/*_example.py)

.PHONY: all clean test requirements production coverage staging regression sync-regression all-regression install build analysis fix crash update-extension generate run-examples verify detect change lint publish publish-public public-ensure public-update public-import public-diff

all: $(PY_OUTPUTS) $(MAKEFILE_OUTPUT) $(CSV_OUTPUTS) $(EXAMPLE_OUTPUTS) $(TEST_OUTPUTS)

# Generate Python files
$(PDD_DIR)/%.py: $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating $@"
	@mkdir -p $(PDD_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd --strength 1 generate --output $@ $< || touch $@

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
$(CONTEXT_DIR)/%_example.py: $(PDD_DIR)/%.py $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating example for $<"
	@mkdir -p $(CONTEXT_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd --strength .8 example --output $@ $(word 2,$^) $< || touch $@

# Generate test files
$(TESTS_DIR)/test_%.py: $(PDD_DIR)/%.py $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating test for $<"
	@mkdir -p $(TESTS_DIR)
	@PYTHONPATH=$(PROD_DIR) pdd --strength 1 test --output $@ $^

# Generate specific module or all files
generate:
ifdef MODULE
	@echo "Generating files for module: $(MODULE)"
	@# Define file paths based on MODULE
	$(eval PY_FILE := $(PDD_DIR)/$(MODULE).py)
	$(eval PY_PROMPT := $(PROMPTS_DIR)/$(MODULE)_python.prompt)
	$(eval EXAMPLE_FILE := $(CONTEXT_DIR)/$(MODULE)_example.py)
	$(eval TEST_FILE := $(TESTS_DIR)/test_$(MODULE).py)

	@# Generate Python file
	@echo "Generating $(PY_FILE)"
	@mkdir -p $(PDD_DIR)
	-@PYTHONPATH=$(PROD_DIR) pdd --strength .9 --time 1 --temperature .7 --local generate --output $(PY_FILE) $(PY_PROMPT)

	@# Generate example file
	@echo "Generating example for $(PY_FILE)"
	@mkdir -p $(CONTEXT_DIR)
	-@PYTHONPATH=$(PROD_DIR) pdd  --strength .9 --verbose example --output $(EXAMPLE_FILE) $(PY_PROMPT) $(PY_FILE)

	@# Generate test file
	@echo "Generating test for $(PY_FILE)"
	@mkdir -p $(TESTS_DIR)
	-@PYTHONPATH=$(PROD_DIR) pdd --strength .9 test --output $(TEST_FILE) $(PY_PROMPT) $(PY_FILE)
else
	@echo "Generating all Python files, examples, and tests"
	@$(MAKE) $(PY_OUTPUTS) $(EXAMPLE_OUTPUTS) $(TEST_OUTPUTS)
endif

# Run example files
run-examples: $(EXAMPLE_FILES)
	@echo "Running examples one by one:"
	@$(foreach example_file,$(EXAMPLE_FILES), \
		echo "Running $(example_file)"; \
		conda run -n pdd --no-capture-output PYTHONPATH=$(STAGING_DIR):$(PDD_DIR):$$PYTHONPATH python $(example_file) || exit 1; \
	)
	@echo "All examples ran successfully"

# Run tests
test:
	@echo "Running staging tests"
	@cd $(STAGING_DIR)
	@conda run -n pdd --no-capture-output PDD_PATH=$(STAGING_DIR) PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python -m pytest -vv $(TESTS_DIR)

# Run tests with coverage
coverage:
	@echo "Running tests with coverage"
	@cd $(STAGING_DIR)
	@conda run -n pdd --no-capture-output PDD_PATH=$(STAGING_DIR) PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python -m pytest --cov=$(PDD_DIR) --cov-report=term-missing --cov-report=html $(TESTS_DIR)

# Run pylint
lint:
	@echo "Running pylint"
	@conda run -n pdd --no-capture-output pylint pdd tests

# Fix crashes in code
crash:
ifdef MODULE
	@echo "Attempting to fix crashes for module: $(MODULE)"
	@# Define file paths based on MODULE
	$(eval PY_FILE := $(PDD_DIR)/$(MODULE).py)
	$(eval PY_PROMPT := $(PROMPTS_DIR)/$(MODULE)_python.prompt)
	$(eval PROGRAM_FILE := $(CONTEXT_DIR)/$(MODULE)_example.py)
	$(eval ERROR_FILE := $(MODULE)_crash.log)
	
	@echo "Running $(PROGRAM_FILE) to capture crash output..."
	@mkdir -p $(shell dirname $(ERROR_FILE))
	@-PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python $(PROGRAM_FILE) 2> $(ERROR_FILE) || true
	
	@echo "Fixing crashes in $(PY_FILE)"
	-pdd --strength .9 --temperature 0 --verbose crash --loop --max-attempts 3 --budget 5.0 --output $(PDD_DIR)/$(MODULE).py --output-program $(CONTEXT_DIR)/$(MODULE)_example.py $(PY_PROMPT) $(PY_FILE) $(PROGRAM_FILE) $(ERROR_FILE)
else
	@echo "Please specify a MODULE to fix crashes"
	@echo "Usage: make crash MODULE=<module_name>"
endif

# Verify code functionality against prompt intent
verify:
ifdef MODULE
	@echo "Verifying functionality for module: $(MODULE)"
	@# Define file paths based on MODULE
	$(eval PY_FILE := $(PDD_DIR)/$(MODULE).py)
	$(eval PY_PROMPT := $(PROMPTS_DIR)/$(MODULE)_python.prompt)
	$(eval PROGRAM_FILE := $(CONTEXT_DIR)/$(MODULE)_example.py)
	$(eval RESULTS_FILE := $(MODULE)_verify_results.log)
	
	@echo "Verifying $(PY_FILE) functionality..."
	-conda run -n pdd --no-capture-output pdd --strength .9 --verbose verify --max-attempts 3 --budget 5.0 --output-code $(PDD_DIR)/$(MODULE)_verified.py --output-program $(CONTEXT_DIR)/$(MODULE)_example_verified.py --output-results $(RESULTS_FILE) $(PY_PROMPT) $(PY_FILE) $(PROGRAM_FILE)
else
	@echo "Please specify a MODULE to verify"
	@echo "Usage: make verify MODULE=<module_name>"
endif

# Detect changes in prompts
.PHONY: detect
detect:
ifdef CHANGE_FILE
	@echo "Detecting which prompts need changes based on: $(CHANGE_FILE)"
	@# Ensure CHANGE_FILE exists
	@if [ ! -f "$(CHANGE_FILE)" ]; then \
		echo "Error: CHANGE_FILE '$(CHANGE_FILE)' not found."; \
		exit 1; \
	fi
	@# Define all prompt files
	$(eval ALL_PROMPT_FILES := $(wildcard $(PROMPTS_DIR)/*.prompt))
	@if [ -z "$(ALL_PROMPT_FILES)" ]; then \
		echo "No prompt files found in $(PROMPTS_DIR)"; \
		exit 1; \
	fi
	@echo "Analyzing prompts: $(ALL_PROMPT_FILES)"
	@# Define output file based on CHANGE_FILE basename
	$(eval CHANGE_FILE_BASENAME := $(basename $(notdir $(CHANGE_FILE))))
	$(eval DETECT_OUTPUT_FILE := $(CHANGE_FILE_BASENAME)_detect.csv)
	@echo "Output will be saved to $(DETECT_OUTPUT_FILE)"
	@conda run -n pdd --no-capture-output pdd detect --output $(DETECT_OUTPUT_FILE) $(ALL_PROMPT_FILES) $(CHANGE_FILE)
	@echo "Detection complete. Results in $(DETECT_OUTPUT_FILE)"
else
	@echo "Please specify a CHANGE_FILE to detect changes against."
	@echo "Usage: make detect CHANGE_FILE=<path_to_description_file>"
endif

# Change prompt file based on instructions
.PHONY: change
change:
ifeq ($(strip $(CSV_FILE)),) # If CSV_FILE is not set or empty, assume single prompt mode
	@# Single prompt change mode
ifdef CHANGE_PROMPT
ifdef CODE_FILE
ifdef PROMPT_FILE
	@echo "Modifying single prompt file: $(PROMPT_FILE)"
	@echo "Based on change prompt: $(CHANGE_PROMPT)"
	@echo "And input code: $(CODE_FILE)"

	@# Ensure input files exist for single mode
	@if [ ! -f "$(CHANGE_PROMPT)" ]; then echo "Error: CHANGE_PROMPT '$(CHANGE_PROMPT)' not found."; exit 1; fi
	@if [ ! -f "$(CODE_FILE)" ]; then echo "Error: CODE_FILE '$(CODE_FILE)' not found."; exit 1; fi
	@if [ ! -f "$(PROMPT_FILE)" ]; then echo "Error: PROMPT_FILE '$(PROMPT_FILE)' not found."; exit 1; fi

	$(eval PROMPT_BASENAME := $(basename $(notdir $(PROMPT_FILE))))
	$(eval DEFAULT_OUTPUT_FILE := modified_$(PROMPT_BASENAME).prompt)
	$(eval ACTUAL_OUTPUT_FILE := $(if $(OUTPUT_FILE),$(OUTPUT_FILE),$(DEFAULT_OUTPUT_FILE)))

	@echo "Output will be saved to $(ACTUAL_OUTPUT_FILE)"
	@conda run -n pdd --no-capture-output pdd change --output $(ACTUAL_OUTPUT_FILE) $(CHANGE_PROMPT) $(CODE_FILE) $(PROMPT_FILE)
	@echo "Single prompt modification complete. Output at $(ACTUAL_OUTPUT_FILE)"
else
	@echo "Error: PROMPT_FILE must be specified for single prompt change mode."
	@echo "Usage for single prompt: make change CHANGE_PROMPT=<c.prompt> CODE_FILE=<input.code> PROMPT_FILE=<orig.prompt> [OUTPUT_FILE=<o.prompt>]"
	@echo "Usage for CSV batch:   make change CSV_FILE=<c.csv> [CODE_DIR=<code_dir/>] [OUTPUT_LOCATION=<out_dir_or_csv>]"
	@exit 1
endif
else
	@echo "Error: CODE_FILE must be specified for single prompt change mode."
	@echo "Usage for single prompt: make change CHANGE_PROMPT=<c.prompt> CODE_FILE=<input.code> PROMPT_FILE=<orig.prompt> [OUTPUT_FILE=<o.prompt>]"
	@echo "Usage for CSV batch:   make change CSV_FILE=<c.csv> [CODE_DIR=<code_dir/>] [OUTPUT_LOCATION=<out_dir_or_csv>]"
	@exit 1
endif
else
	@echo "Error: CHANGE_PROMPT must be specified for single prompt change mode (when CSV_FILE is not set)."
	@echo "Usage for single prompt: make change CHANGE_PROMPT=<c.prompt> CODE_FILE=<input.code> PROMPT_FILE=<orig.prompt> [OUTPUT_FILE=<o.prompt>]"
	@echo "Usage for CSV batch:   make change CSV_FILE=<c.csv> [CODE_DIR=<code_dir/>] [OUTPUT_LOCATION=<out_dir_or_csv>]"
	@exit 1
endif
else
	@# CSV batch change mode
	$(eval EFFECTIVE_CODE_DIR := $(if $(CODE_DIR),$(CODE_DIR),./pdd))
	@echo "Modifying prompts in batch using CSV file: $(CSV_FILE)"
	@echo "Using code directory: $(EFFECTIVE_CODE_DIR) $(if $(CODE_DIR),,(default))"
	@echo "Prompts are assumed to be in: $(PROMPTS_DIR)"
ifdef CSV_FILE
	@# Ensure input file/directory exist for CSV mode
	@if [ ! -f "$(CSV_FILE)" ]; then echo "Error: CSV_FILE '$(CSV_FILE)' not found (expected relative to project root)."; exit 1; fi
	@if [ ! -d "$(EFFECTIVE_CODE_DIR)" ]; then echo "Error: Code directory '$(EFFECTIVE_CODE_DIR)' not found or is not a directory."; exit 1; fi
	@if [ ! -d "$(PROMPTS_DIR)" ]; then echo "Error: PROMPTS_DIR '$(PROMPTS_DIR)' not found or is not a directory."; exit 1; fi

	$(eval REL_CSV_FILE := ../$(CSV_FILE))
	$(eval REL_CODE_DIR := ../$(EFFECTIVE_CODE_DIR))
	$(eval DEFAULT_CSV_OUTPUT_DIR := ../prompts) # Output dir relative to PROMPTS_DIR
	$(eval CMD_OUTPUT_ARG :=)

	$(if $(OUTPUT_LOCATION), \
		$(eval IS_ABS_OUTPUT := $(filter /%,$(OUTPUT_LOCATION))) \
		$(if $(IS_ABS_OUTPUT), \
			$(eval CMD_OUTPUT_ARG := --output $(OUTPUT_LOCATION)), \
			$(eval CMD_OUTPUT_ARG := --output ../$(OUTPUT_LOCATION)) \
		) \
	, \
		$(eval CMD_OUTPUT_ARG := --output $(DEFAULT_CSV_OUTPUT_DIR)) \
		@mkdir -p $(PROMPTS_DIR)/$(DEFAULT_CSV_OUTPUT_DIR) \
		@echo "No OUTPUT_LOCATION specified, defaulting to $(PROMPTS_DIR)/$(DEFAULT_CSV_OUTPUT_DIR)/" \
	)

	@if [ ! -z "$(OUTPUT_LOCATION)" ]; then echo "Output location specified by user: $(OUTPUT_LOCATION)"; fi
	@echo "Executing from $(PROMPTS_DIR): conda run -n pdd --no-capture-output pdd --force change --budget 10.0 --csv $(CMD_OUTPUT_ARG) $(REL_CSV_FILE) $(REL_CODE_DIR)"
	@cd $(PROMPTS_DIR) && conda run -n pdd --no-capture-output pdd --force change --budget 10.0 --csv $(CMD_OUTPUT_ARG) $(REL_CSV_FILE) $(REL_CODE_DIR)
	@echo "CSV batch prompt modification complete."
else # This means CSV_FILE was not defined, which contradicts the outer ifeq logic. This branch likely won't be hit if CSV_FILE is the primary condition.
	@echo "Error: CSV_FILE must be specified for CSV batch change mode." # This case should ideally not be reached due to outer ifeq
	@echo "Usage for CSV batch:   make change CSV_FILE=<c.csv> [CODE_DIR=<code_dir/>] [OUTPUT_LOCATION=<out_dir_or_csv>]"
	@echo "Usage for single prompt: make change CHANGE_PROMPT=<c.prompt> CODE_FILE=<input.code> PROMPT_FILE=<orig.prompt> [OUTPUT_FILE=<o.prompt>]"
	@exit 1
endif
endif

# Fix prompts command
fix:
ifdef MODULE
	@echo "Attempting to fix module: $(MODULE)"
	@name=$(MODULE); \
	prompt="$(PROMPTS_DIR)/$${name}_python.prompt"; \
	echo "Fixing $$name"; \
	if [ -f "$(CONTEXT_DIR)/$${name}_example.py" ]; then \
		conda run -n pdd --no-capture-output python -m pdd.cli --time 1 --strength .9 --temperature 0 --verbose --force fix --loop --auto-submit --max-attempts 5 --output-test output/ --output-code output/ --verification-program $(CONTEXT_DIR)/$${name}_example.py $$prompt $(PDD_DIR)/$${name}.py $(TESTS_DIR)/test_$${name}.py $${name}.log; \
	else \
		echo "Warning: No verification program found for $$name"; \
	fi;
else
	@echo "Attempting to fix all prompts"
	@for prompt in $(wildcard $(PROMPTS_DIR)/*_python.prompt); do \
		name=$$(basename $$prompt _python.prompt); \
		echo "Fixing $$name"; \
		if [ -f "$(CONTEXT_DIR)/$${name}_example.py" ]; then \
			conda run -n pdd --no-capture-output python -m pdd.cli --strength .9 --temperature 0 --verbose --force fix --loop --auto-submit --max-attempts 5 --output-test output/ --output-code output/ --verification-program $(CONTEXT_DIR)/$${name}_example.py $$prompt $(PDD_DIR)/$${name}.py $(TESTS_DIR)/test_$${name}.py $${name}.log; \
		else \
			echo "Warning: No verification program found for $$name"; \
		fi; \
	done
endif

# Generate requirements.txt
requirements:
	@echo "Generating requirements.txt"
	@PYTHONPATH=$(PROD_DIR) pipreqs ./pdd --force --savepath ./requirements.txt
	@PYTHONPATH=$(PROD_DIR) pipreqs ./tests --force --savepath ./tmp_requirements.txt
	@cat ./tmp_requirements.txt ./requirements.txt | sort | uniq > ./final_requirements.txt
	@mv ./final_requirements.txt ./requirements.txt
	@rm ./tmp_requirements.txt
	@fawltydeps --detailed 

# Clean generated files
clean:
	@echo "Cleaning generated files"
	@rm -rf staging output output.csv pdd/*_[0-9]_[0-9]_[0-9]_[0-9]*.py tests/*_[0-9]_[0-9]_[0-9]_[0-9]*.py

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
	@find staging/regression -type f ! -name ".*" -delete
ifdef TEST_NUM
	@echo "Running specific test: $(TEST_NUM)"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/regression.sh $(TEST_NUM)
else
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/regression.sh
endif

sync-regression:
	@echo "Running sync regression tests"
ifdef TEST_NUM
	@echo "Running specific sync test: $(TEST_NUM)"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/sync_regression.sh $(TEST_NUM)
else
	@echo "Running all sync regression tests"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/sync_regression.sh
endif

all-regression: regression sync-regression
	@echo "All regression test suites completed."

install:
	@echo "Installing pdd"
	@pip install -e .

build:
	@echo "Building pdd"
	@rm -rf dist
	@conda run -n pdd --no-capture-output python -m build
	@rm dist/*.tar.gz #don't upload source distribution
	
	# Post-process the wheel with preprocessed prompts
	@echo "Post-processing wheel with preprocessed prompts..."
	@conda run -n pdd --no-capture-output python scripts/preprocess_wheel.py 'dist/*.whl'
	
	@conda run -n pdd --no-capture-output twine upload --repository pypi dist/*.whl

publish:
	@echo "Building and uploading package"
	@$(MAKE) build
	@$(MAKE) publish-public

release:
	@echo "Preparing release"
	@CURRENT_VERSION=$$(sed -n '1,120s/^version[[:space:]]*=[[:space:]]*"\([0-9.]*\)"/\1/p' pyproject.toml | head -n1); \
	CURRENT_TAG="v$$CURRENT_VERSION"; \
	if git tag --points-at HEAD | grep -qx "$$CURRENT_TAG"; then \
		echo "HEAD already at $$CURRENT_TAG; skipping bump and publishing current version."; \
		$(MAKE) publish; \
	else \
		echo "Bumping version with commitizen"; \
		python -m commitizen bump --increment PATCH --yes; \
		echo "Publishing new version"; \
		$(MAKE) publish; \
	fi

analysis:
	@echo "Running regression analysis"
	@LATEST_REGRESSION_DIR=$$(ls -td -- "staging/regression_"* 2>/dev/null | head -n 1); \
	if [ -d "$$LATEST_REGRESSION_DIR" ]; then \
		echo "Using latest regression directory: $$LATEST_REGRESSION_DIR"; \
		ANALYSIS_FILE="$$LATEST_REGRESSION_DIR/regression_analysis.md"; \
		PYTHONPATH=$(PDD_DIR):$$PYTHONPATH REGRESSION_TARGET_DIR=$$LATEST_REGRESSION_DIR pdd --strength .9 --local generate --output "$$ANALYSIS_FILE" prompts/regression_analysis_log.prompt; \
		echo "Analysis results:"; \
		python -c "from rich.console import Console; from rich.syntax import Syntax; console = Console(); content = open('$$ANALYSIS_FILE').read(); syntax = Syntax(content, 'python', theme='monokai', line_numbers=True); console.print(syntax)"; \
	else \
		echo "No regression directory found. Please run 'make regression' first."; \
		exit 1; \
	fi

# Update VS Code extension
update-extension:
	@echo "Updating VS Code extension"
	@pdd --strength .865 --verbose --force generate --output utils/vscode_prompt/syntaxes/prompt.tmLanguage.json prompts/prompt.tmLanguage_json.prompt
	@cd utils/vscode_prompt && vsce package
	@code --install-extension utils/vscode_prompt/prompt-0.0.1.vsix --force
publish-public:
	@# Ensure target directory is a Git repo (clone if empty and not a repo)
	@if [ ! -d "$(PUBLIC_PDD_REPO_DIR)/.git" ]; then \
		if [ ! -d "$(PUBLIC_PDD_REPO_DIR)" ] || [ -z "$$(/bin/ls -A "$(PUBLIC_PDD_REPO_DIR)" 2>/dev/null)" ]; then \
			echo "Cloning public repo $(PUBLIC_PDD_REMOTE) into $(PUBLIC_PDD_REPO_DIR)"; \
			mkdir -p "$(dir $(PUBLIC_PDD_REPO_DIR))"; \
			git clone "$(PUBLIC_PDD_REMOTE)" "$(PUBLIC_PDD_REPO_DIR)"; \
		else \
			echo "Warning: $(PUBLIC_PDD_REPO_DIR) exists and is not a Git repo."; \
			echo "Set PUBLIC_PDD_REPO_DIR to a clone of $(PUBLIC_PDD_REMOTE) or remove the directory and re-run."; \
		fi; \
	fi
	@echo "Ensuring public repo directory exists: $(PUBLIC_PDD_REPO_DIR)"
	@mkdir -p $(PUBLIC_PDD_REPO_DIR)
	@echo "Copying examples to public repo"
	@cp -r ./examples $(PUBLIC_PDD_REPO_DIR)/
	@echo "Copying doctrine doc to public repo"
	@mkdir -p $(PUBLIC_PDD_REPO_DIR)/docs
	@cp docs/prompt-driven-development-doctrine.md $(PUBLIC_PDD_REPO_DIR)/docs/
	@echo "Copying specific whitepaper files to public repo"
	@mkdir -p $(PUBLIC_PDD_REPO_DIR)/docs/whitepaper_with_benchmarks/analysis_report
	@mkdir -p $(PUBLIC_PDD_REPO_DIR)/docs/whitepaper_with_benchmarks/creation_report
	@cp "docs/whitepaper_with_benchmarks/whitepaper_w_benchmarks.md" $(PUBLIC_PDD_REPO_DIR)/docs/whitepaper_with_benchmarks/
	@cp \
		docs/whitepaper_with_benchmarks/analysis_report/overall_success_rate.png \
		docs/whitepaper_with_benchmarks/analysis_report/overall_avg_execution_time.png \
		docs/whitepaper_with_benchmarks/analysis_report/overall_avg_api_cost.png \
		docs/whitepaper_with_benchmarks/analysis_report/cost_per_successful_task.png \
		docs/whitepaper_with_benchmarks/analysis_report/success_rate_by_file_size.png \
		docs/whitepaper_with_benchmarks/analysis_report/avg_api_cost_by_file_size.png \
		docs/whitepaper_with_benchmarks/analysis_report/avg_execution_time_by_file_size.png \
		docs/whitepaper_with_benchmarks/analysis_report/success_rate_by_edit_type.png \
		docs/whitepaper_with_benchmarks/analysis_report/avg_api_cost_by_edit_type.png \
		docs/whitepaper_with_benchmarks/analysis_report/avg_execution_time_by_edit_type.png \
		$(PUBLIC_PDD_REPO_DIR)/docs/whitepaper_with_benchmarks/analysis_report/
	@cp \
		docs/whitepaper_with_benchmarks/creation_report/total_cost_comparison.png \
		docs/whitepaper_with_benchmarks/creation_report/total_time_comparison.png \
		docs/whitepaper_with_benchmarks/creation_report/pdd_avg_cost_per_module_dist.png \
		docs/whitepaper_with_benchmarks/creation_report/claude_cost_per_run_dist.png \
		$(PUBLIC_PDD_REPO_DIR)/docs/whitepaper_with_benchmarks/creation_report/
	@echo "Copying VS Code extension to public repo"
	@mkdir -p $(PUBLIC_PDD_REPO_DIR)/utils
	@cp -r ./utils/vscode_prompt $(PUBLIC_PDD_REPO_DIR)/utils/
	@echo "Copying selected top-level files to public repo (if present): $(PUBLIC_ROOT_FILES)"
	@set -e; for f in $(PUBLIC_ROOT_FILES); do \
		if [ -f "$$f" ]; then \
			echo "  -> $$f"; \
			cp "$$f" $(PUBLIC_PDD_REPO_DIR)/; \
		fi; \
	done
	@if [ "$(PUBLIC_COPY_TESTS)" = "1" ]; then \
		echo "Copying core unit tests to public repo"; \
		conda run -n pdd --no-capture-output python scripts/copy_package_data_to_public.py \
			--dest $(PUBLIC_PDD_REPO_DIR) \
			--copy-tests \
			$(foreach pat,$(PUBLIC_TEST_INCLUDE),--tests-include '$(pat)') \
			$(foreach xpat,$(PUBLIC_TEST_EXCLUDE),--tests-exclude '$(xpat)'); \
	else \
		echo "Skipping tests copy (PUBLIC_COPY_TESTS=$(PUBLIC_COPY_TESTS))"; \
	fi
	@if [ "$(PUBLIC_COPY_CONTEXT)" = "1" ]; then \
		echo "Copying context examples to public repo"; \
		conda run -n pdd --no-capture-output python scripts/copy_package_data_to_public.py \
			--dest $(PUBLIC_PDD_REPO_DIR) \
			--copy-context \
			$(foreach pat,$(PUBLIC_CONTEXT_INCLUDE),--context-include '$(pat)') \
			$(foreach xpat,$(PUBLIC_CONTEXT_EXCLUDE),--context-exclude '$(xpat)'); \
	else \
		echo "Skipping context copy (PUBLIC_COPY_CONTEXT=$(PUBLIC_COPY_CONTEXT))"; \
	fi
		@echo "Copying package-data files defined in pyproject.toml to public repo"
		@mkdir -p $(PUBLIC_PDD_REPO_DIR)/pdd
		@conda run -n pdd --no-capture-output python scripts/copy_package_data_to_public.py --dest $(PUBLIC_PDD_REPO_DIR)
	@echo "Committing and pushing updates in public repo"
	@if git -C "$(PUBLIC_PDD_REPO_DIR)" rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		cd "$(PUBLIC_PDD_REPO_DIR)" && git add . && git commit -m "Bump version" && git push; \
		else \
			echo "Skip commit: $(PUBLIC_PDD_REPO_DIR) is not a Git repo. Set PUBLIC_PDD_REPO_DIR to a clone of $(PUBLIC_PDD_REMOTE)."; \
		fi

# Ensure the public repo clone exists at $(PUBLIC_PDD_REPO_DIR)
public-ensure:
	@if [ ! -d "$(PUBLIC_PDD_REPO_DIR)/.git" ]; then \
		if [ ! -d "$(PUBLIC_PDD_REPO_DIR)" ] || [ -z "$$(/bin/ls -A "$(PUBLIC_PDD_REPO_DIR)" 2>/dev/null)" ]; then \
			echo "Cloning public repo $(PUBLIC_PDD_REMOTE) into $(PUBLIC_PDD_REPO_DIR)"; \
			mkdir -p "$(dir $(PUBLIC_PDD_REPO_DIR))"; \
			git clone "$(PUBLIC_PDD_REMOTE)" "$(PUBLIC_PDD_REPO_DIR)"; \
		else \
			echo "Warning: $(PUBLIC_PDD_REPO_DIR) exists and is not a Git repo."; \
			echo "Set PUBLIC_PDD_REPO_DIR to a clone of $(PUBLIC_PDD_REMOTE) or remove the directory and re-run."; \
			exit 1; \
		fi; \
	else \
		echo "Public repo clone already present: $(PUBLIC_PDD_REPO_DIR)"; \
	fi

# Update the public repo clone to its default branch
public-update: public-ensure
	@echo "Updating public repo clone at $(PUBLIC_PDD_REPO_DIR)"
	@if [ -d "$(PUBLIC_PDD_REPO_DIR)/.git" ]; then \
		cd "$(PUBLIC_PDD_REPO_DIR)"; \
		git fetch --all; \
		DEFAULT_BRANCH=$$(git remote show origin | awk '/HEAD branch/ {print $$NF}'); \
		if [ -z "$$DEFAULT_BRANCH" ]; then DEFAULT_BRANCH=main; fi; \
		git checkout "$$DEFAULT_BRANCH"; \
		git pull --rebase --autostash origin "$$DEFAULT_BRANCH"; \
	else \
		echo "Error: $(PUBLIC_PDD_REPO_DIR) is not a Git repo."; \
		exit 1; \
	fi

# Import a file or directory from the public repo clone into this repo
# Usage: make public-import ITEM=relative/path/in/public/repo
public-import: public-update
	@if [ -z "$(ITEM)" ]; then \
		echo "Usage: make public-import ITEM=relative/path (e.g., ITEM=examples/SETUP_WITH_GEMINI.md)"; \
		exit 1; \
	fi
	@SRC="$(PUBLIC_PDD_REPO_DIR)/$(ITEM)"; DST="$(ITEM)"; \
	if [ ! -e "$$SRC" ]; then \
		ALT_ITEM="$${ITEM#pdd/}"; \
		ALT_SRC="$(PUBLIC_PDD_REPO_DIR)/$${ALT_ITEM}"; \
		if [ "$$ALT_ITEM" != "$(ITEM)" ] && [ -e "$$ALT_SRC" ]; then \
			SRC="$$ALT_SRC"; DST="$$ALT_ITEM"; \
		else \
			echo "Error: $$SRC not found in public repo clone."; \
			exit 1; \
		fi; \
	fi; \
	mkdir -p "$$(dirname "$$DST")"; \
	cp -a "$$SRC" "$$DST"; \
	echo "Imported $$SRC -> $$DST"

# Show diff between the public clone file and the local file
# Usage: make public-diff ITEM=relative/path/in/public/repo
public-diff: public-update
	@if [ -z "$(ITEM)" ]; then \
		echo "Usage: make public-diff ITEM=relative/path (e.g., ITEM=examples/SETUP_WITH_GEMINI.md)"; \
		exit 1; \
	fi
	@SRC="$(PUBLIC_PDD_REPO_DIR)/$(ITEM)"; DST="$(ITEM)"; \
	if [ ! -e "$$SRC" ]; then \
		ALT_ITEM="$${ITEM#pdd/}"; \
		ALT_SRC="$(PUBLIC_PDD_REPO_DIR)/$${ALT_ITEM}"; \
		if [ "$$ALT_ITEM" != "$(ITEM)" ] && [ -e "$$ALT_SRC" ]; then \
			SRC="$$ALT_SRC"; DST="$$ALT_ITEM"; \
		else \
			echo "Error: $$SRC not found in public repo clone."; \
			exit 1; \
		fi; \
	fi; \
	if [ -e "$$DST" ]; then \
		echo "Showing diff: local '$$DST' vs public '$$SRC'"; \
		git --no-pager diff --no-index -- "$${DST}" "$${SRC}" || true; \
	else \
		echo "Local destination missing: $$DST"; \
		echo "Diff against empty file:"; \
		git --no-pager diff --no-index -- /dev/null "$${SRC}" || true; \
	fi
