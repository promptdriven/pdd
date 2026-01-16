SHELL := /bin/bash

# Configuration
USE_LOCAL ?= yes
USE_FORCE ?= yes

PDD_FLAGS :=
ifeq ($(USE_LOCAL),yes)
    PDD_FLAGS += --local
endif
ifeq ($(USE_FORCE),yes)
    PDD_FLAGS += --force
endif

PDD := pdd $(PDD_FLAGS)

# Directories
BENCHMARK_DIR := benchmark_results
CODE_BASED_DIR := $(BENCHMARK_DIR)/code_based
EXAMPLE_BASED_DIR := $(BENCHMARK_DIR)/example_based

.PHONY: help benchmark generate-code-based generate-example-based analyze compare run-tests clean verify-examples generate-example

help:
	@echo "Test Generation Benchmark: Code-based vs TDD/Example-based"
	@echo "============================================================"
	@echo ""
	@echo "Main targets:"
	@echo "  make benchmark          - Run full benchmark (generate + analyze)"
	@echo "  make compare            - Show diff between generated tests"
	@echo "  make run-tests          - Run both test suites against implementation"
	@echo "  make clean              - Remove generated test files"
	@echo ""
	@echo "Individual steps:"
	@echo "  make generate-example       - Generate example file using 'pdd example'"
	@echo "  make generate-code-based    - Generate tests from src/email_validator.py"
	@echo "  make generate-example-based - Generate tests from examples/email_validator_example.py"
	@echo "  make analyze                - Analyze generated tests for implementation references"
	@echo "  make verify-examples        - Run the example file to verify it works"
	@echo ""
	@echo "Options:"
	@echo "  USE_LOCAL=yes|no   - Use local API (default: yes)"
	@echo "  USE_FORCE=yes|no   - Skip prompts (default: yes)"
	@echo ""

# Generate the example file using pdd example (TDD input)
generate-example:
	@echo "==> Generating example file using 'pdd example'..."
	@mkdir -p examples
	$(PDD) example email_validator_python.prompt src/email_validator.py \
		--output examples/email_validator_example.py
	@echo ""
	@echo "Example file generated: examples/email_validator_example.py"

# Verify examples work before benchmarking
verify-examples:
	@echo "==> Verifying example file works..."
	@PYTHONPATH=src python examples/email_validator_example.py
	@echo ""

# Generate tests using code-based approach (analyzes actual implementation)
generate-code-based: $(CODE_BASED_DIR)
	@echo "==> Generating tests using CODE-BASED approach..."
	@echo "    Template: generate_test_LLM.prompt"
	@echo "    Input: email_validator_python.prompt + src/email_validator.py"
	@echo "    This analyzes the ACTUAL code to generate tests."
	@echo ""
	$(PDD) --strength 0.9 test \
		email_validator_python.prompt \
		src/email_validator.py \
		--output $(CODE_BASED_DIR)/test_email_validator.py
	@echo ""
	@echo "Code-based tests saved to: $(CODE_BASED_DIR)/test_email_validator.py"

# Generate tests using example-based approach (TDD style)
generate-example-based: $(EXAMPLE_BASED_DIR)
	@echo "==> Generating tests using EXAMPLE-BASED (TDD) approach..."
	@echo "    Template: generate_test_from_example_LLM.prompt"
	@echo "    Input: email_validator_python.prompt + examples/email_validator_example.py"
	@echo "    This analyzes the INTENDED BEHAVIOR from examples."
	@echo ""
	$(PDD) --strength 0.9 test \
		email_validator_python.prompt \
		examples/email_validator_example.py \
		--output $(EXAMPLE_BASED_DIR)/test_email_validator.py
	@echo ""
	@echo "Example-based tests saved to: $(EXAMPLE_BASED_DIR)/test_email_validator.py"

# Create output directories
$(CODE_BASED_DIR) $(EXAMPLE_BASED_DIR):
	@mkdir -p $@

# Run full benchmark
benchmark: clean verify-examples generate-code-based generate-example-based analyze
	@echo ""
	@echo "============================================"
	@echo "BENCHMARK COMPLETE"
	@echo "============================================"
	@echo ""
	@echo "Generated test files:"
	@echo "  Code-based:    $(CODE_BASED_DIR)/test_email_validator.py"
	@echo "  Example-based: $(EXAMPLE_BASED_DIR)/test_email_validator.py"
	@echo ""
	@echo "Next steps:"
	@echo "  make compare    - View side-by-side diff"
	@echo "  make run-tests  - Execute both test suites"

# Analyze generated tests for implementation detail references
analyze:
	@echo ""
	@echo "============================================"
	@echo "ANALYSIS: References to Implementation Details"
	@echo "============================================"
	@echo ""
	@echo "Looking for references to private members:"
	@echo "  - _normalize, _check_local_part, _check_domain"
	@echo "  - _has_consecutive_dots, EMAIL_PATTERN, _MIN_DOMAIN_PARTS"
	@echo ""
	@echo "--- CODE-BASED TEST ANALYSIS ---"
	@if [ -f "$(CODE_BASED_DIR)/test_email_validator.py" ]; then \
		echo "Lines: $$(wc -l < $(CODE_BASED_DIR)/test_email_validator.py)"; \
		echo "Test functions: $$(grep -c 'def test_' $(CODE_BASED_DIR)/test_email_validator.py 2>/dev/null || echo 0)"; \
		echo "Private method refs: $$(grep -cE '_normalize|_check_local_part|_check_domain|_has_consecutive_dots' $(CODE_BASED_DIR)/test_email_validator.py 2>/dev/null || echo 0)"; \
		echo "EMAIL_PATTERN refs: $$(grep -c 'EMAIL_PATTERN' $(CODE_BASED_DIR)/test_email_validator.py 2>/dev/null || echo 0)"; \
		echo ""; \
		if grep -qE '_normalize|_check_local_part|_check_domain|_has_consecutive_dots|EMAIL_PATTERN' $(CODE_BASED_DIR)/test_email_validator.py 2>/dev/null; then \
			echo "Found implementation references:"; \
			grep -nE '_normalize|_check_local_part|_check_domain|_has_consecutive_dots|EMAIL_PATTERN' $(CODE_BASED_DIR)/test_email_validator.py | head -10; \
		else \
			echo "No direct implementation references found."; \
		fi; \
	else \
		echo "File not found. Run 'make generate-code-based' first."; \
	fi
	@echo ""
	@echo "--- EXAMPLE-BASED TEST ANALYSIS ---"
	@if [ -f "$(EXAMPLE_BASED_DIR)/test_email_validator.py" ]; then \
		echo "Lines: $$(wc -l < $(EXAMPLE_BASED_DIR)/test_email_validator.py)"; \
		echo "Test functions: $$(grep -c 'def test_' $(EXAMPLE_BASED_DIR)/test_email_validator.py 2>/dev/null || echo 0)"; \
		echo "Private method refs: $$(grep -cE '_normalize|_check_local_part|_check_domain|_has_consecutive_dots' $(EXAMPLE_BASED_DIR)/test_email_validator.py 2>/dev/null || echo 0)"; \
		echo "EMAIL_PATTERN refs: $$(grep -c 'EMAIL_PATTERN' $(EXAMPLE_BASED_DIR)/test_email_validator.py 2>/dev/null || echo 0)"; \
		echo ""; \
		if grep -qE '_normalize|_check_local_part|_check_domain|_has_consecutive_dots|EMAIL_PATTERN' $(EXAMPLE_BASED_DIR)/test_email_validator.py 2>/dev/null; then \
			echo "Found implementation references:"; \
			grep -nE '_normalize|_check_local_part|_check_domain|_has_consecutive_dots|EMAIL_PATTERN' $(EXAMPLE_BASED_DIR)/test_email_validator.py | head -10; \
		else \
			echo "No direct implementation references found."; \
		fi; \
	else \
		echo "File not found. Run 'make generate-example-based' first."; \
	fi
	@echo ""

# Compare generated tests side-by-side
compare:
	@echo "============================================"
	@echo "DIFF: Code-based vs Example-based Tests"
	@echo "============================================"
	@if [ -f "$(CODE_BASED_DIR)/test_email_validator.py" ] && [ -f "$(EXAMPLE_BASED_DIR)/test_email_validator.py" ]; then \
		diff -u $(CODE_BASED_DIR)/test_email_validator.py $(EXAMPLE_BASED_DIR)/test_email_validator.py || true; \
	else \
		echo "Error: Both test files must exist. Run 'make benchmark' first."; \
		exit 1; \
	fi

# Run both test suites against the implementation
run-tests:
	@echo "============================================"
	@echo "Running Generated Test Suites"
	@echo "============================================"
	@echo ""
	@echo "--- CODE-BASED TESTS ---"
	@if [ -f "$(CODE_BASED_DIR)/test_email_validator.py" ]; then \
		PYTHONPATH=src pytest -v $(CODE_BASED_DIR)/test_email_validator.py || true; \
	else \
		echo "File not found. Run 'make generate-code-based' first."; \
	fi
	@echo ""
	@echo "--- EXAMPLE-BASED TESTS ---"
	@if [ -f "$(EXAMPLE_BASED_DIR)/test_email_validator.py" ]; then \
		PYTHONPATH=src pytest -v $(EXAMPLE_BASED_DIR)/test_email_validator.py || true; \
	else \
		echo "File not found. Run 'make generate-example-based' first."; \
	fi

# Clean generated files
clean:
	@echo "Cleaning benchmark results..."
	@rm -rf $(BENCHMARK_DIR)
	@echo "Clean complete."
