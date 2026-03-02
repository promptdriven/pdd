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
	@echo "  make example [MODULE=name]   - Generate specific example or all example files"
	@echo "  make run-examples            - Run all example files"
	@echo ""
	@echo "Testing Commands:"
	@echo "  make test                    - Run staging tests"
	@echo "  make coverage                - Run tests with coverage"
	@echo "  make regression [TEST_NUM=n] - Run regression tests (optionally specific test number)"
	@echo "  make sync-regression [TEST_NUM=n] - Run sync regression tests (optionally specific test number)"
	@echo "  make all-regression 		  - Run all regression test suites"
	@echo "  make cloud-regression [TEST_NUM=n] - Run cloud regression tests (no --local flag)"
	@echo "  make test-all-ci [PR_NUMBER=n] [PR_URL=url] - Run all tests with result capture"
	@echo "  make test-all-with-infisical [PR_NUMBER=n] [PR_URL=url] - Run all tests with Infisical"
	@echo "  make pr-test pr-url=URL      - Test any GitHub PR on GitHub Actions (e.g., https://github.com/owner/repo/pull/123)"
	@echo "  make cloud-test              - Build image + push + run all tests on Cloud Batch"
	@echo "  make cloud-test-quick        - Run tests on Cloud Batch (skip image rebuild)"
	@echo "  make cloud-test-build        - Build and push image via Cloud Build"
	@echo "  make cloud-test-push         - (no-op, included in cloud-test-build)"
	@echo "  make cloud-test-setup        - One-time GCP infrastructure setup"
	@echo "  make analysis                - Run regression analysis"
	@echo "  make verify MODULE=name      - Verify code functionality against prompt intent"
	@echo "  make lint                    - Run pylint for static code analysis"
	@echo ""
	@echo "Public repo helpers:"
	@echo "  make public-update           - Ensure and update local public repo clone ($(PUBLIC_PDD_REPO_DIR))"
	@echo "  make public-import ITEM=path - Copy file/dir from public clone into this repo (e.g., ITEM=pdd/examples/SETUP_WITH_GEMINI.md)"
	@echo "  make public-diff ITEM=path   - Show diff between public clone file and local file (uses same ITEM rules)"
	@echo "  make sync-public             - Fetch public remote and list commits missing locally"
	@echo "Fixing & Maintenance:"
	@echo "  make update [MODULE=name]    - Update prompt based on code changes (uses git)"
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
	@echo "  make publish-public-cap      - Copy artifacts to CAP public repo only"
	@echo "  make check-deps              - Check pyproject.toml and requirements.txt are in sync"
	@echo "  make release                 - Bump version and build package (runs check-deps first)"
	@echo "  make staging                 - Copy files to staging"
	@echo "  make production              - Copy files from staging to pdd"
	@echo "  make update-extension        - Update VS Code extension"
 
# Public repo paths (override via env if needed)
PUBLIC_PDD_REPO_DIR ?= staging/public/pdd
PUBLIC_PDD_REMOTE ?= https://github.com/promptdriven/pdd.git
# CAP public repo (optional second destination)
PUBLIC_PDD_CAP_REPO_DIR ?= staging/public/pdd_cap
PUBLIC_PDD_CAP_REMOTE ?= https://github.com/promptdriven/pdd_cap.git
# Top-level files to publish if present (read from .sync-config.yml)
PUBLIC_ROOT_FILES ?= $(shell python scripts/get_sync_patterns.py root_files 2>/dev/null || echo "LICENSE README.md requirements.txt pyproject.toml")
# Include core unit tests by default
PUBLIC_COPY_TESTS ?= 1
PUBLIC_TEST_INCLUDE ?= $(shell python scripts/get_sync_patterns.py test_patterns 2>/dev/null || echo "tests/test_*.py tests/__init__.py tests/conftest.py")
PUBLIC_TEST_EXCLUDE ?= tests/regression* tests/sync_regression* tests/**/regression* tests/**/sync_regression* tests/**/*.ipynb tests/csv/**
PUBLIC_COPY_CONTEXT ?= 1
PUBLIC_CONTEXT_INCLUDE ?= context/**/*_example.py
PUBLIC_CONTEXT_EXCLUDE ?= context/**/__pycache__ context/**/*.log context/**/*.csv
PUBLIC_REGRESSION_SCRIPTS ?= $(wildcard tests/*regression*.sh)

# Python files
PY_PROMPTS := $(shell find $(PROMPTS_DIR) -name "*_python.prompt")
PY_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_python.prompt,$(PDD_DIR)/%.py,$(PY_PROMPTS))

# Makefile
MAKEFILE_PROMPT := $(PROMPTS_DIR)/Makefile_makefile.prompt
MAKEFILE_OUTPUT := $(STAGING_DIR)/Makefile
SKIP_MAKEFILE_REGEN ?= 0

# Auto-skip Makefile regeneration if prompt file doesn't exist (e.g., public repo)
ifeq ($(wildcard $(MAKEFILE_PROMPT)),)
SKIP_MAKEFILE_REGEN := 1
endif

# CSV files
CSV_PROMPTS := $(shell find $(PROMPTS_DIR) -name "*_csv.prompt")
CSV_OUTPUTS := $(patsubst $(PROMPTS_DIR)/%_csv.prompt,$(DATA_DIR)/%.csv,$(CSV_PROMPTS))


# Test files
TEST_OUTPUTS := $(patsubst $(PDD_DIR)/%.py,$(TESTS_DIR)/test_%.py,$(PY_OUTPUTS))

# All Example files in context directory (recursive)
EXAMPLE_FILES := $(shell find $(CONTEXT_DIR) -name "*_example.py" 2>/dev/null)

.PHONY: all clean test requirements production coverage staging regression sync-regression all-regression cloud-regression install build analysis fix crash update update-extension generate run-examples verify detect change lint publish publish-public publish-public-cap public-ensure public-update public-import public-diff sync-public ensure-dev-deps cloud-test cloud-test-quick cloud-test-build cloud-test-push cloud-test-setup test-frontend

all: $(PY_OUTPUTS) $(MAKEFILE_OUTPUT) $(CSV_OUTPUTS) $(EXAMPLE_OUTPUTS) $(TEST_OUTPUTS)

example:
ifdef MODULE
	@echo "Generating example for module: $(MODULE)"
	$(eval PY_FILE := $(PDD_DIR)/$(MODULE).py)
	$(eval PY_PROMPT := $(PROMPTS_DIR)/$(MODULE)_python.prompt)
	# Example file path in subdirectory
	$(eval EXAMPLE_FILE := $(CONTEXT_DIR)/$(MODULE)_example.py)

	@# Generate example file
	@echo "Generating $(EXAMPLE_FILE)"
	@mkdir -p $(dir $(EXAMPLE_FILE))
	-@PYTHONPATH=$(STAGING_DIR) pdd --strength .9 --verbose example --output $(EXAMPLE_FILE) $(PY_PROMPT) $(PY_FILE)
else
	# Code for generating all examples (nested)
	@echo "Generating all example files (nested in $(CONTEXT_DIR))"
	@$(foreach prompt_file,$(PY_PROMPTS),\n\t\t$(eval module_path := $(patsubst $(PROMPTS_DIR)/%_python.prompt,%,$(prompt_file)))\n\t\t$(eval py_file := $(PDD_DIR)/$(module_path).py)\n\t\t$(eval example_file := $(CONTEXT_DIR)/$(module_path)_example.py)\n\t\techo "Generating example for $(module_path) -> $(example_file)";\n\t\tmkdir -p $(dir $(example_file));\n\t\tPYTHONPATH=$(STAGING_DIR) pdd --strength .8 example --output $(example_file) $(prompt_file) $(py_file) || true;\n\t)
endif

# Generate Python files
$(PDD_DIR)/%.py: $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating $@"
	@mkdir -p $(dir $@)
	@PYTHONPATH=$(STAGING_DIR) pdd --strength 1 generate --output $@ $< || touch $@

# Generate Makefile
ifeq ($(SKIP_MAKEFILE_REGEN),1)
$(MAKEFILE_OUTPUT):
	@echo "Skipping Makefile regeneration (SKIP_MAKEFILE_REGEN=1)"
else
$(MAKEFILE_OUTPUT): $(MAKEFILE_PROMPT)
	@echo "Generating $@"
	@mkdir -p $(STAGING_DIR)
	@PYTHONPATH=$(STAGING_DIR) pdd generate --output $@ $<
endif

# Generate CSV files
$(DATA_DIR)/%.csv: $(PROMPTS_DIR)/%_csv.prompt
	@echo "Generating $@"
	@mkdir -p $(dir $@)
	@PYTHONPATH=$(STAGING_DIR) pdd generate --output $@ $<

# Generate test files
$(TESTS_DIR)/test_%.py: $(PDD_DIR)/%.py $(PROMPTS_DIR)/%_python.prompt
	@echo "Generating test for $<"
	@mkdir -p $(dir $@)
	@PYTHONPATH=$(STAGING_DIR) pdd --strength 1 test --output $@ $^

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
	-@PYTHONPATH=$(STAGING_DIR) pdd --strength .9 --time 1 --temperature .7 --local generate --output $(PY_FILE) $(PY_PROMPT)

	@# Generate example file
	@echo "Generating example for $(PY_FILE)"
	@mkdir -p $(CONTEXT_DIR)
	-@PYTHONPATH=$(STAGING_DIR) pdd  --strength .9 --verbose example --output $(EXAMPLE_FILE) $(PY_PROMPT) $(PY_FILE)

	@# Generate test file
	@echo "Generating test for $(PY_FILE)"
	@mkdir -p $(TESTS_DIR)
	-@PYTHONPATH=$(STAGING_DIR) pdd --strength .9 test --output $(TEST_FILE) $(PY_PROMPT) $(PY_FILE)
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

# Ensure dev dependencies are installed before running tests
ensure-dev-deps:
	@echo "Updating pdd conda environment with dev dependencies"
	@conda run -n pdd --no-capture-output python -c "import site, glob, shutil; [shutil.rmtree(p) for p in glob.glob(site.getsitepackages()[0] + '/pdd_cli-*.dist-info')]" 2>/dev/null || true
	@conda run -n pdd --no-capture-output pip install -e '.[dev]'

# Run tests
test: ensure-dev-deps
	@echo "Running staging tests"
	@cd $(STAGING_DIR)
	@conda run -n pdd --no-capture-output PDD_MODEL_DEFAULT=vertex_ai/gemini-3-flash-preview PDD_RUN_REAL_LLM_TESTS=1 PDD_RUN_LLM_TESTS=1 PDD_PATH=$(abspath $(PDD_DIR)) PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python -m pytest -vv -n auto $(TESTS_DIR)

# Run tests with coverage
coverage: ensure-dev-deps
	@echo "Running tests with coverage"
	@cd $(STAGING_DIR)
	@conda run -n pdd --no-capture-output PDD_MODEL_DEFAULT=vertex_ai/gemini-3-flash-preview PDD_PATH=$(STAGING_DIR) PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python -m pytest --cov=$(PDD_DIR) --cov-report=term-missing --cov-report=html $(TESTS_DIR)

# Run pylint
lint: ensure-dev-deps
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
	@if PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python $(PROGRAM_FILE) 2> $(ERROR_FILE); then \
		echo "No crashes detected in $(MODULE)."; \
	else \
		echo "Crash detected! Fixing crashes in $(PY_FILE)"; \
		pdd --strength .9 --temperature 0 --verbose crash --loop --max-attempts 3 --budget 5.0 --output $(PDD_DIR)/$(MODULE).py --output-program $(CONTEXT_DIR)/$(MODULE)_example.py $(PY_PROMPT) $(PY_FILE) $(PROGRAM_FILE) $(ERROR_FILE); \
	fi
else
	@echo "Attempting to fix crashes for all modules"
	@find $(PROMPTS_DIR) -name "*_python.prompt" | while read prompt; do \
		rel_path="$${prompt#$(PROMPTS_DIR)/}"; \
		name="$${rel_path%_python.prompt}"; \
		py_file="$(PDD_DIR)/$${name}.py"; \
		program_file="$(CONTEXT_DIR)/$${name}_example.py"; \
		error_file="$${name}_crash.log"; \
		if [ -f "$$program_file" ]; then \
			echo "Processing module: $$name"; \
			echo "Running $$program_file to capture crash output..."; \
			mkdir -p $$(dirname "$$error_file"); \
			if PYTHONPATH=$(PDD_DIR):$$PYTHONPATH python "$$program_file" 2> "$$error_file"; then \
				echo "No crashes detected in $$name."; \
			else \
				echo "Crash detected! Fixing crashes in $$py_file"; \
				pdd --strength .9 --temperature 0 --verbose crash --loop --max-attempts 3 --budget 5.0 --output "$$py_file" --output-program "$$program_file" "$$prompt" "$$py_file" "$$program_file" "$$error_file"; \
			fi; \
		else \
			echo "Skipping module $$name: No example program found at $$program_file"; \
		fi; \
	done
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
	@find $(PROMPTS_DIR) -name "*_python.prompt" | while read prompt; do \
		rel_path="$${prompt#$(PROMPTS_DIR)/}"; \
		name="$${rel_path%_python.prompt}"; \
		echo "Fixing $$name"; \
		if [ -f "$(CONTEXT_DIR)/$${name}_example.py" ]; then \
			conda run -n pdd --no-capture-output python -m pdd.cli --strength .9 --temperature 0 --verbose --force fix --loop --auto-submit --max-attempts 5 --output-test output/ --output-code output/ --verification-program $(CONTEXT_DIR)/$${name}_example.py $$prompt $(PDD_DIR)/$${name}.py $(TESTS_DIR)/test_$${name}.py $${name}.log; \
		else \
			echo "Warning: No verification program found for $$name"; \
		fi; \
	done
endif

# Update prompt based on code changes
update:
ifdef MODULE
	@echo "Updating prompt for module: $(MODULE)"
	$(eval PY_FILE := $(PDD_DIR)/$(MODULE).py)
	$(eval PY_PROMPT := $(PROMPTS_DIR)/$(MODULE)_python.prompt)

	@if [ ! -f "$(PY_FILE)" ]; then \
		echo "Error: Code file $(PY_FILE) not found."; \
		exit 1; \
	fi
	@if [ ! -f "$(PY_PROMPT)" ]; then \
		echo "Error: Prompt file $(PY_PROMPT) not found."; \
		exit 1; \
	fi

	@echo "Updating $(PY_PROMPT) based on changes in $(PY_FILE)"
	conda run -n pdd --no-capture-output pdd --verbose update --git $(PY_PROMPT) $(PY_FILE)
else
	@echo "Running repository-wide prompt update"
	conda run -n pdd --no-capture-output pdd --verbose update --directory pdd --extensions py
endif

# Generate requirements.txt
requirements:
	@echo "Generating requirements.txt"
	@PYTHONPATH=$(STAGING_DIR) pipreqs ./pdd --force --savepath ./requirements.txt
	@PYTHONPATH=$(STAGING_DIR) pipreqs ./tests --force --savepath ./tmp_requirements.txt
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

regression: ensure-dev-deps
	@echo "Running regression tests"
	@mkdir -p staging/regression
	@find staging/regression -type f ! -name ".*" -delete
ifdef TEST_NUM
	@echo "Running specific test: $(TEST_NUM)"
	@PDD_MODEL_DEFAULT=vertex_ai/gemini-3-flash-preview PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/regression.sh $(TEST_NUM)
else
	@PDD_MODEL_DEFAULT=vertex_ai/gemini-3-flash-preview PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/regression.sh
endif

SYNC_PARALLEL ?= 1

sync-regression: ensure-dev-deps
	@echo "Running sync regression tests"
ifdef TEST_NUM
	@echo "Running specific sync test: $(TEST_NUM)"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/sync_regression.sh $(TEST_NUM)
else
ifeq ($(SYNC_PARALLEL),1)
	@echo "Running sync regression suite in parallel"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/sync_regression_parallel.sh
else
	@echo "Running all sync regression tests sequentially"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/sync_regression.sh
endif
endif

all-regression: regression sync-regression cloud-regression
	@echo "All regression test suites completed."

cloud-regression: ensure-dev-deps
	@echo "Running cloud regression tests"
	@mkdir -p staging/cloud_regression
ifdef TEST_NUM
	@echo "Running specific cloud test: $(TEST_NUM)"
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/cloud_regression.sh $(TEST_NUM)
else
	@PYTHONPATH=$(PDD_DIR):$$PYTHONPATH bash tests/cloud_regression.sh
endif

# Cloud Batch configuration
CLOUD_BATCH_DIR := ci/cloud-batch
GCP_PROJECT_ID := prompt-driven-development-stg
GCP_REGION ?= us-central1
GCS_BUCKET ?= pdd-stg-ci-results
AR_IMAGE := $(GCP_REGION)-docker.pkg.dev/$(GCP_PROJECT_ID)/pdd-ci/pdd-test:latest

# Files baked into the Docker image — changes to these require a rebuild
CLOUD_IMAGE_DEPS := requirements.txt pyproject.toml $(CLOUD_BATCH_DIR)/entrypoint.sh $(CLOUD_BATCH_DIR)/Dockerfile
CLOUD_IMAGE_HASH_FILE := .cloud-image-hash

# Smart run: auto-detects whether image rebuild is needed
cloud-test:
	@CURRENT_HASH=$$(cat $(CLOUD_IMAGE_DEPS) | shasum -a 256 | cut -d' ' -f1); \
	STORED_HASH=$$(cat $(CLOUD_IMAGE_HASH_FILE) 2>/dev/null || echo "none"); \
	if [ "$$CURRENT_HASH" != "$$STORED_HASH" ]; then \
		echo "Image deps changed — rebuilding via Cloud Build"; \
		$(MAKE) cloud-test-build; \
	else \
		echo "Image deps unchanged — skipping rebuild"; \
	fi
	@$(MAKE) cloud-test-quick

# Upload source and run tests (skip image rebuild — typical workflow)
cloud-test-quick:
	@echo "Running tests on Cloud Batch (quick mode — no image rebuild)"
	@GCP_PROJECT_ID=$(GCP_PROJECT_ID) GCP_REGION=$(GCP_REGION) GCS_BUCKET=$(GCS_BUCKET) \
		bash $(CLOUD_BATCH_DIR)/submit.sh

# Build and push image via Cloud Build (no local Docker needed)
cloud-test-build:
	@echo "Submitting build to Cloud Build"
	@gcloud builds submit \
		--config=$(CLOUD_BATCH_DIR)/cloudbuild.yaml \
		--substitutions=_AR_IMAGE=$(AR_IMAGE) \
		--project=$(GCP_PROJECT_ID) \
		.
	@cat $(CLOUD_IMAGE_DEPS) | shasum -a 256 | cut -d' ' -f1 > $(CLOUD_IMAGE_HASH_FILE)

# No-op — push is handled by Cloud Build
cloud-test-push:
	@echo "Push is now handled by cloud-test-build (Cloud Build). Nothing to do."

# One-time GCP infrastructure setup
cloud-test-setup:
	@echo "Setting up Cloud Batch infrastructure"
	@GCP_PROJECT_ID=$(GCP_PROJECT_ID) GCP_REGION=$(GCP_REGION) GCS_BUCKET=$(GCS_BUCKET) \
		bash $(CLOUD_BATCH_DIR)/setup-gcp.sh

# Automated test runner with Infisical for CI/CD
.PHONY: test-all-ci
test-all-ci: ensure-dev-deps
	@echo "Running all test suites with result capture for CI/CD"
	@mkdir -p test_results
ifdef PR_NUMBER
ifdef PR_URL
	@conda run -n pdd --no-capture-output python scripts/run_all_tests_with_results.py --pr-number $(PR_NUMBER) --pr-url $(PR_URL)
else
	@conda run -n pdd --no-capture-output python scripts/run_all_tests_with_results.py --pr-number $(PR_NUMBER)
endif
else
	@conda run -n pdd --no-capture-output python scripts/run_all_tests_with_results.py
endif

# Run all tests with Infisical (for local development and CI)
.PHONY: test-all-with-infisical
test-all-with-infisical: ensure-dev-deps
	@echo "Running all test suites with Infisical"
	@if ! command -v infisical &> /dev/null; then \
		echo "Error: Infisical CLI not found. Please install it:"; \
		echo "npm install -g @infisical/cli"; \
		exit 1; \
	fi
	@mkdir -p test_results
ifdef PR_NUMBER
ifdef PR_URL
	@infisical run -- conda run -n pdd --no-capture-output python scripts/run_all_tests_with_results.py --pr-number $(PR_NUMBER) --pr-url $(PR_URL)
else
	@infisical run -- conda run -n pdd --no-capture-output python scripts/run_all_tests_with_results.py --pr-number $(PR_NUMBER)
endif
else
	@infisical run -- conda run -n pdd --no-capture-output python scripts/run_all_tests_with_results.py
endif

# Test a PR from a public or private repo by triggering GitHub Actions
.PHONY: pr-test
pr-test:
	@if [ -z "$(pr-url)" ]; then \
		echo "Error: pr-url is required"; \
		echo "Usage: make pr-test pr-url=https://github.com/owner/repo/pull/123"; \
		exit 1; \
	fi
	@echo "Triggering GitHub Actions to test PR at $(pr-url)..."
	@if ! command -v gh &> /dev/null; then \
		echo "Error: GitHub CLI (gh) not found. Please install it:"; \
		echo "  macOS: brew install gh"; \
		echo "  Linux: https://github.com/cli/cli/blob/trunk/docs/install_linux.md"; \
		exit 1; \
	fi
	@PR_NUMBER=$$(echo "$(pr-url)" | grep -o '[0-9]*$$'); \
	if [ -z "$$PR_NUMBER" ]; then \
		echo "Error: Could not extract PR number from URL."; \
		exit 1; \
	fi; \
	gh workflow run pr-tests.yml \
		--repo gltanaka/pdd \
		--field public_pr_number=$$PR_NUMBER \
		--field public_pr_url=$(pr-url)
	@echo "Workflow triggered successfully!"
	@echo "View progress: https://github.com/gltanaka/pdd/actions"
	@echo "Results will be posted to: $(pr-url)"

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
	@$(MAKE) publish-public publish-public-cap

# Check that pyproject.toml dependencies match requirements.txt
check-deps:
	@python scripts/check_deps.py

# Issue #186: Detect suspicious single-letter files (C, E, T)
# These files sometimes appear during release operations
# Files are logged but NOT removed so we can debug when it happens
.PHONY: check-suspicious-files
check-suspicious-files:
	@echo "Checking for suspicious single-letter files (Issue #186)..."
	@SUSPICIOUS=$$(find . -maxdepth 1 -type f \( -name 'C' -o -name 'E' -o -name 'T' -o -name '?' -o -name '??' \) ! -name '.*' 2>/dev/null); \
	if [ -n "$$SUSPICIOUS" ]; then \
		echo "⚠️  SUSPICIOUS FILES DETECTED:"; \
		echo "$$SUSPICIOUS"; \
		echo "Logging to ~/.pdd/suspicious_files.log"; \
		mkdir -p ~/.pdd; \
		echo "" >> ~/.pdd/suspicious_files.log; \
		echo "============================================================" >> ~/.pdd/suspicious_files.log; \
		echo "Timestamp: $$(date -Iseconds)" >> ~/.pdd/suspicious_files.log; \
		echo "Context: make check-suspicious-files" >> ~/.pdd/suspicious_files.log; \
		echo "Directory: $$(pwd)" >> ~/.pdd/suspicious_files.log; \
		echo "Files: $$SUSPICIOUS" >> ~/.pdd/suspicious_files.log; \
		for f in $$SUSPICIOUS; do \
			echo "  File: $$f, Size: $$(stat -f%z "$$f" 2>/dev/null || stat -c%s "$$f" 2>/dev/null) bytes, Modified: $$(stat -f%Sm "$$f" 2>/dev/null || stat -c%y "$$f" 2>/dev/null)" >> ~/.pdd/suspicious_files.log; \
		done; \
		echo "Files left in place for debugging."; \
	else \
		echo "No suspicious files found."; \
	fi

release: check-deps check-suspicious-files
	@echo "Preparing release"
	@CURRENT_VERSION=$$(sed -n '1,120s/^version[[:space:]]*=[[:space:]]*"\([0-9.]*\)"/\1/p' pyproject.toml | head -n1); \
	CURRENT_TAG="v$$CURRENT_VERSION"; \
	if git tag --points-at HEAD | grep -qx "$$CURRENT_TAG"; then \
		echo "HEAD already at $$CURRENT_TAG; skipping bump and publishing current version."; \
		$(MAKE) publish; \
	else \
		echo "Bumping version with commitizen"; \
		python -m commitizen bump --increment PATCH --yes; \
		echo "Pushing to origin before publishing"; \
		git push origin main --tags; \
		echo "Publishing new version"; \
		$(MAKE) publish; \
	fi
	@# Post-release cleanup check (Issue #186)
	@$(MAKE) check-suspicious-files
	@# Update CHANGELOG.md with changes from this release
	@echo "Updating CHANGELOG.md..."
	@claude --dangerously-skip-permissions -p "Update CHANGELOG.md for the latest release. Steps: \
1. Run 'git tag | tail -2' to find the prior and current version tags. \
2. Run 'git diff <prior>..HEAD --stat' and 'git log <prior>..HEAD --oneline' to see all changes. \
3. For files with significant changes (>20 lines in the stat), run 'git diff <prior>..HEAD -- <file>' to understand the SEMANTIC meaning of the change, not just that lines changed. Look for: new features, behavior changes, removed constants/functions, generalized logic. \
4. Note any DELETED files (shown as 'delete mode' or '0 insertions, N deletions') - these are often meaningful (e.g., removed prompts, deprecated modules). \
5. IMPORTANT: PR numbers in merge commits (e.g., 'Merge pull request #337') are from the FORK (gltanaka/pdd), NOT the public repo (promptdriven/pdd). Do NOT include fork PR numbers in the CHANGELOG - they will confuse users who look them up on the public repo. \
6. For external contributor credits ONLY: use 'gh pr list --repo promptdriven/pdd --state merged --limit 20' to find upstream PRs. Verify PRs exist with 'gh pr view <num> --repo promptdriven/pdd --json state,title'. Only credit PRs that are actually merged on promptdriven/pdd. \
7. Organize changes into sections: Feat, Fix, Build, Refactor, Docs. \
8. Keep descriptions concise but complete. Every significant code change should be represented. \
We are using a prompt driven development approach: docs/prompting_guide.md."

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
test-frontend:
	@echo "Running frontend Vitest tests"
	@cd pdd/frontend && npm test

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
	@# Reset to origin/main before copying so the copy lands on a clean baseline
	@if git -C "$(PUBLIC_PDD_REPO_DIR)" rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		cd "$(PUBLIC_PDD_REPO_DIR)" && git fetch origin && git reset --hard origin/main; \
	fi
	@echo "Copying files from .sync-config.yml (shared section only)"
	@python scripts/copy_package_data_to_public.py \
		--dest $(PUBLIC_PDD_REPO_DIR) \
		--project-root . \
		--config .sync-config.yml \
		--sections shared \
		--sync-deletions
	@# Create prompts symlink if needed (prompts/ -> pdd/prompts/)
	@if [ -d "$(PUBLIC_PDD_REPO_DIR)/pdd/prompts" ] && [ ! -e "$(PUBLIC_PDD_REPO_DIR)/prompts" ]; then \
		echo "Creating prompts symlink"; \
		cd "$(PUBLIC_PDD_REPO_DIR)" && ln -s pdd/prompts prompts; \
	fi
	@# Create data symlink for regression tests (data/ -> pdd/data/)
	@if [ -d "$(PUBLIC_PDD_REPO_DIR)/pdd/data" ] && [ ! -e "$(PUBLIC_PDD_REPO_DIR)/data" ]; then \
		echo "Creating data symlink for regression tests"; \
		cd "$(PUBLIC_PDD_REPO_DIR)" && ln -s pdd/data data; \
	fi
	@echo "Committing and pushing updates in public repo"
	@if git -C "$(PUBLIC_PDD_REPO_DIR)" rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		cd "$(PUBLIC_PDD_REPO_DIR)" && git add . && \
		if ! git diff --cached --quiet; then \
			git commit -m "Bump version" && \
			CURR_VER=$$(sed -n 's/^version[[:space:]]*=[[:space:]]*"\([0-9.]*\)"/\1/p' pyproject.toml | head -n1) && \
			(git tag -a "v$$CURR_VER" -m "Release v$$CURR_VER" 2>/dev/null || true) && \
			git push && git push --tags; \
		else \
			echo "No changes to commit in public repo — skipping push"; \
		fi; \
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

# Publish to CAP public repo (copies all prompts, including non _LLM.prompt)
.PHONY: publish-public-cap
publish-public-cap:
	@# Ensure target directory is a Git repo (clone if empty and not a repo)
	@if [ ! -d "$(PUBLIC_PDD_CAP_REPO_DIR)/.git" ]; then \
		if [ ! -d "$(PUBLIC_PDD_CAP_REPO_DIR)" ] || [ -z "$$(/bin/ls -A "$(PUBLIC_PDD_CAP_REPO_DIR)" 2>/dev/null)" ]; then \
			echo "Cloning public CAP repo $(PUBLIC_PDD_CAP_REMOTE) into $(PUBLIC_PDD_CAP_REPO_DIR)"; \
			mkdir -p "$(dir $(PUBLIC_PDD_CAP_REPO_DIR))"; \
			git clone "$(PUBLIC_PDD_CAP_REMOTE)" "$(PUBLIC_PDD_CAP_REPO_DIR)"; \
		else \
			echo "Warning: $(PUBLIC_PDD_CAP_REPO_DIR) exists and is not a Git repo."; \
			echo "Set PUBLIC_PDD_CAP_REPO_DIR to a clone of $(PUBLIC_PDD_CAP_REMOTE) or remove the directory and re-run."; \
		fi; \
	fi
	@echo "Ensuring CAP public repo directory exists: $(PUBLIC_PDD_CAP_REPO_DIR)"
	@mkdir -p $(PUBLIC_PDD_CAP_REPO_DIR)
	@# Reset to origin/main before copying so the copy lands on a clean baseline
	@if git -C "$(PUBLIC_PDD_CAP_REPO_DIR)" rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		cd "$(PUBLIC_PDD_CAP_REPO_DIR)" && git fetch origin && git reset --hard origin/main; \
	fi
	@echo "Copying files from .sync-config.yml (shared + cap_only sections)"
	@python scripts/copy_package_data_to_public.py \
		--dest $(PUBLIC_PDD_CAP_REPO_DIR) \
		--project-root . \
		--config .sync-config.yml \
		--sections shared cap_only \
		--sync-deletions
	@# Create prompts symlink if needed (prompts/ -> pdd/prompts/)
	@if [ -d "$(PUBLIC_PDD_CAP_REPO_DIR)/pdd/prompts" ] && [ ! -e "$(PUBLIC_PDD_CAP_REPO_DIR)/prompts" ]; then \
		echo "Creating prompts symlink"; \
		cd "$(PUBLIC_PDD_CAP_REPO_DIR)" && ln -s pdd/prompts prompts; \
	fi
	@# Create data symlink for regression tests (data/ -> pdd/data/)
	@if [ -d "$(PUBLIC_PDD_CAP_REPO_DIR)/pdd/data" ] && [ ! -e "$(PUBLIC_PDD_CAP_REPO_DIR)/data" ]; then \
		echo "Creating data symlink for regression tests"; \
		cd "$(PUBLIC_PDD_CAP_REPO_DIR)" && ln -s pdd/data data; \
	fi
	@echo "Committing and pushing updates in CAP public repo"
	@if git -C "$(PUBLIC_PDD_CAP_REPO_DIR)" rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		cd "$(PUBLIC_PDD_CAP_REPO_DIR)" && git add . && \
		if ! git diff --cached --quiet; then \
			git commit -m "Bump version" && \
			CURR_VER=$$(sed -n 's/^version[[:space:]]*=[[:space:]]*"\([0-9.]*\)"/\1/p' pyproject.toml | head -n1) && \
			(git tag -a "v$$CURR_VER" -m "Release v$$CURR_VER" 2>/dev/null || true) && \
			git push && git push --tags; \
		else \
			echo "No changes to commit in CAP public repo — skipping push"; \
		fi; \
	else \
		echo "Skip commit: $(PUBLIC_PDD_CAP_REPO_DIR) is not a Git repo. Set PUBLIC_PDD_CAP_REPO_DIR to a clone of $(PUBLIC_PDD_CAP_REMOTE)."; \
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

# Fetch updates from the public remote and report unsynced commits
sync-public:
	@if ! git remote get-url public >/dev/null 2>&1; then \
		echo "Error: no 'public' remote configured."; \
		echo "Add it with: git remote add public $(PUBLIC_PDD_REMOTE)"; \
		exit 1; \
	fi
	@echo "Fetching refs from 'public' remote"
	@git fetch public
	@DEFAULT_BRANCH=$$(git remote show public | awk '/HEAD branch/ {print $$NF}'); \
	if [ -z "$$DEFAULT_BRANCH" ]; then DEFAULT_BRANCH=main; fi; \
	echo "Comparing against public/$$DEFAULT_BRANCH"; \
	BEHIND=$$(git rev-list --count HEAD..public/$$DEFAULT_BRANCH 2>/dev/null || echo 0); \
	AHEAD=$$(git rev-list --count public/$$DEFAULT_BRANCH..HEAD 2>/dev/null || echo 0); \
	if [ "$$BEHIND" -eq 0 ]; then \
		echo "No missing commits from public/$$DEFAULT_BRANCH."; \
	else \
		echo "$$BEHIND commit(s) in public/$$DEFAULT_BRANCH not yet synced locally:"; \
		git --no-pager log --oneline HEAD..public/$$DEFAULT_BRANCH; \
	fi; \
	if [ "$$AHEAD" -eq 0 ]; then \
		echo "No local commits ahead of public/$$DEFAULT_BRANCH."; \
	else \
		echo "$$AHEAD local commit(s) ahead of public/$$DEFAULT_BRANCH:"; \
		git --no-pager log --oneline public/$$DEFAULT_BRANCH..HEAD; \
	fi
