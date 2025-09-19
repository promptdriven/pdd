SHELL := /bin/bash
# Makefile for project setup and cleaning


# Define directories
EDIT_FILE_TOOL_DIR := edit_file_tool
TESTS_DIR := tests
LOGS_DIR := logs
COST_REPORTS_DIR := cost_reports
PROMPTS_DIR := prompts
EXAMPLES_DIR := examples

# PDD Configuration Variables
# USE_INFISICAL: Set to 'yes' to use infisical, 'no' to skip it
# USE_LOCAL: Set to 'yes' to use --local flag, 'no' for cloud mode (default)
# 
# Examples:
#   make USE_INFISICAL=no USE_LOCAL=yes tool_list    # Results in: pdd --local
#   make USE_INFISICAL=yes USE_LOCAL=no tool_list    # Results in: infisical run -- pdd  
#   make USE_INFISICAL=no USE_LOCAL=no tool_list     # Results in: pdd
#   make tool_list                                   # Results in: infisical run -- pdd (defaults)
USE_INFISICAL ?= yes
USE_LOCAL ?= yes

# Build PDD_CMD dynamically based on configuration
PDD_BASE := pdd
ifeq ($(USE_LOCAL),yes)
PDD_FLAGS := --local
else
PDD_FLAGS := 
endif

# Use direct pdd command
PDD_CMD_BASE := pdd

ifeq ($(USE_LOCAL),yes)
FULL_PYTHON_CMD := $(PDD_CMD_BASE) $(PDD_FLAGS)
else
FULL_PYTHON_CMD := $(PDD_CMD_BASE)
endif

ifeq ($(USE_INFISICAL),yes)
PDD_CMD := infisical run -- $(FULL_PYTHON_CMD)
else
PDD_CMD := $(FULL_PYTHON_CMD)
endif

# Export PDD configuration as environment variables for Python scripts
export USE_INFISICAL
export USE_LOCAL
export PDD_CMD
export ENABLE_TAGGING

# Component building configuration
# CLEAN_COMPONENTS: Set to 'yes' to enable --clean flag for PDD_workflow.py, 'no' to disable (default)
CLEAN_COMPONENTS ?= yes

# ENABLE_TAGGING: Set to 'yes' to enable tagging functionality, 'no' to disable (default)
ENABLE_TAGGING ?= no

ifeq ($(CLEAN_COMPONENTS),yes)
WORKFLOW_FLAGS := --clean
else
WORKFLOW_FLAGS := 
endif

TOOL_COST_CSV := $(COST_REPORTS_DIR)/tool_track.csv

# Phony targets
.PHONY: setup clean clean-all arch_list all architecture component component-delete build_all_components prompts test

# Default target: all
all: setup arch_list prompts build_all_components

# Setup target: Create directory structure
setup:
	@echo Creating directory structure...
	@mkdir -p "$(EDIT_FILE_TOOL_DIR)"
	@mkdir -p "$(TESTS_DIR)"
	@mkdir -p "$(LOGS_DIR)"
	@mkdir -p "$(COST_REPORTS_DIR)"
	@mkdir -p "$(PROMPTS_DIR)"
	@mkdir -p "$(EXAMPLES_DIR)"
	@echo Directory structure created.

# Clean target: Remove all files in the specified folders
clean:
	@echo Cleaning project files...
	@if [ -d "$(EDIT_FILE_TOOL_DIR)" ]; then echo "Removing files in $(EDIT_FILE_TOOL_DIR)..." && rm -rf "$(EDIT_FILE_TOOL_DIR)"/*; fi
	@if [ -d "$(TESTS_DIR)" ]; then echo "Removing files in $(TESTS_DIR)..." && rm -rf "$(TESTS_DIR)"/*; fi
	@if [ -d "$(LOGS_DIR)" ]; then echo "Removing files in $(LOGS_DIR)..." && rm -rf "$(LOGS_DIR)"/*; fi
	@if [ -d "$(COST_REPORTS_DIR)" ]; then echo "Removing files in $(COST_REPORTS_DIR)..." && rm -rf "$(COST_REPORTS_DIR)"/*; fi
	@if [ -d "$(EXAMPLES_DIR)" ]; then echo "Removing files in $(EXAMPLES_DIR)..." && rm -rf "$(EXAMPLES_DIR)"/*; fi
	@echo Project files cleaned.


# Clean-all target: Remove all created directories and the Makefile itself
clean-all:
	@echo Starting full clean...
	@echo Removing directories...
	@if [ -d "$(EDIT_FILE_TOOL_DIR)" ]; then rm -rf "$(EDIT_FILE_TOOL_DIR)"; fi
	@if [ -d "$(TESTS_DIR)" ]; then rm -rf "$(TESTS_DIR)"; fi
#	@if [ -d "$(LOGS_DIR)" ]; then rm -rf "$(LOGS_DIR)"; fi
#	@if [ -d "$(COST_REPORTS_DIR)" ]; then rm -rf "$(COST_REPORTS_DIR)"; fi
	@echo Removing architecture JSON files...
	@if [ -f "pdd/architecture.json" ]; then rm "pdd/architecture.json"; fi
	@echo Directories removed.

# Architecture list target: Generate architecture.json
arch_list:
	@echo Generating architecture JSON file...
	@$(PDD_CMD) --output-cost $(TOOL_COST_CSV) generate $(PROMPTS_DIR)/architecture_json.prompt > $(LOGS_DIR)/architecture_json.log
	@echo Architecture JSON file generated.

# Architecture target: Display components from architecture.json
architecture:
	@echo Displaying architecture components from architecture.json...
	@if [ ! -f "pdd/architecture.json" ]; then \
	    echo "pdd/architecture.json not found."; \
	else \
	    python -c "import json,sys; \
data=json.load(open('pdd/architecture.json',encoding='utf-8')); \
print('\n'.join(f\"{item['filename']} - {item['reason']}\" for item in data))"; \
	fi
	@echo Done displaying architecture components.

# Generate prompts target: Create prompts from architecture.json
prompts:
	@echo Generating prompts from architecture.json...
	@if [ ! -f "pdd/architecture.json" ]; then \
		echo "[ERROR] pdd/architecture.json not found. Please run 'make arch_list' first to generate it." && \
		exit 1; \
	else \
		echo "[INFO] Running prompts_script.py..." && \
		python Scripts/prompts_script.py && \
		echo "[INFO] Prompts generated successfully."; \
	fi

# -----------------------------------------------------------------
# Build all components from architecture.json
# This is called by 'make all' or 'make component all'
build_all_components: pdd/architecture.json all_components.py
	@echo "[INFO] Building ALL components from architecture.json via all_components.py..."
	@echo "[INFO] Confirming component build..."
	@python -c "import json,sys; \
data=json.load(open('pdd/architecture.json',encoding='utf-8')); \
filenames=[item['filename'] for item in data]; \
print('\\nAre you sure you want to build all components? Have you verified that the prompts look good and are what you want?'); \
print('\\nThe components that you want to build are:'); \
[print(f'  - {f}') for f in filenames]; \
print(''); \
response=input('Press y to confirm and proceed, N or anything else to cancel: ').lower().strip(); \
sys.exit(0 if response == 'y' else 1)"
	@echo "[INFO] Confirmation received. Building components..."
	@for component in $$(python all_components.py); do \
		echo "[INFO] Building component: $$component" && \
		python Scripts/PDD_workflow.py $$component $(WORKFLOW_FLAGS) || \
		(echo "[ERROR] Failed to build component: $$component" && exit 1); \
	done
	@echo "[INFO] All components built successfully!"
	@echo "[INFO] Done building all components."


# Component deletion configuration
# DRY_RUN: Set to 'yes' to enable dry-run mode, 'no' to actually delete (default)
# FORCE_DELETE: Set to 'yes' to skip confirmation, 'no' for confirmation prompt (default)
DRY_RUN ?= no
FORCE_DELETE ?= no

# Build delete flags
DELETE_FLAGS := 
ifeq ($(DRY_RUN),yes)
DELETE_FLAGS += --dry-run
endif
ifeq ($(FORCE_DELETE),yes)
DELETE_FLAGS += --force
endif

# -----------------------------------------------------------------
# Component deletion using component_delete.py
# Usage: 
#   make component-delete claude_api
#   make DRY_RUN=yes component-delete claude_api
#   make FORCE_DELETE=yes component-delete claude_api
component-delete:
	@$(eval REMAINING_ARGS := $(filter-out $@,$(MAKECMDGOALS)))
	@echo "[Makefile] Deleting components: $(REMAINING_ARGS)"
	@if [ -z "$(REMAINING_ARGS)" ]; then \
		echo "[ERROR] No components specified. Usage: make component-delete <filename>"; \
		echo "[INFO] Examples:"; \
		echo "[INFO]   make component-delete claude_api"; \
		echo "[INFO]   make DRY_RUN=yes component-delete claude_api"; \
		echo "[INFO]   make FORCE_DELETE=yes component-delete claude_api"; \
		echo "[INFO] Use 'make architecture' to see available components."; \
		exit 1; \
	fi
	@echo "[INFO] Deleting individual components: $(REMAINING_ARGS)"
	@for component in $(REMAINING_ARGS); do \
		echo "[INFO] Deleting component: $$component"; \
		python Scripts/component_delete.py $$component $(DELETE_FLAGS) || \
		(echo "[ERROR] Failed to delete component: $$component" && exit 1); \
	done
	@echo "[INFO] All specified components deleted successfully!"

# -----------------------------------------------------------------
# Flexible component builder using PDD_workflow.py
component:
	@$(eval REMAINING_ARGS := $(filter-out $@,$(MAKECMDGOALS)))
	@echo "[Makefile] Building components with PDD_workflow.py: $(REMAINING_ARGS)"
	@if [ -z "$(REMAINING_ARGS)" ]; then \
		echo "[ERROR] No components specified. Usage: make component <filename> or make component all"; \
		echo "[INFO] Use 'make architecture' to see available components."; \
		exit 1; \
	fi
	@if [ "$(REMAINING_ARGS)" = "all" ]; then \
		$(MAKE) build_all_components; \
	else \
		echo "[INFO] Building individual components: $(REMAINING_ARGS)"; \
		for component in $(REMAINING_ARGS); do \
			echo "[INFO] Cleaning component before build: $$component"; \
			python Scripts/component_delete.py $$component --force || \
			(echo "[WARN] Component $$component may not exist, proceeding with build..."); \
			echo "[INFO] Building component: $$component"; \
			python Scripts/PDD_workflow.py $$component $(WORKFLOW_FLAGS) || \
			(echo "[ERROR] Failed to build component: $$component" && exit 1); \
		done; \
		echo "[INFO] All specified components built successfully!"; \
	fi

# -----------------------------------------------------------------
# Infisical-enabled component builder
# Usage: make infisical-component <component_name> [flags]
# Example: make infisical-component utils --clean
infisical-component:
	@$(eval REMAINING_ARGS := $(filter-out $@,$(MAKECMDGOALS)))
	@echo "[Makefile] Building components with Infisical secrets: $(REMAINING_ARGS)"
	@if [ -z "$(REMAINING_ARGS)" ]; then \
		echo "[ERROR] No components specified. Usage: make infisical-component <filename>"; \
		echo "[INFO] Use 'make architecture' to see available components."; \
		exit 1; \
	fi
	@echo "[INFO] Building individual components with Infisical: $(REMAINING_ARGS)"; \
	@for component in $(REMAINING_ARGS); do \
		echo "[INFO] Building component with Infisical secrets: $$component"; \
		./scripts/pdd_with_infisical.sh $$component || \
		(echo "[ERROR] Failed to build component: $$component" && exit 1); \
	done; \
	@echo "[INFO] All specified components built successfully with Infisical!"

# -----------------------------------------------------------------
# Direct Infisical wrapper for any command
# Usage: make infisical-run COMMAND="your command here"
# Example: make infisical-run COMMAND="pdd sync utils"
infisical-run:
	@if [ -z "$(COMMAND)" ]; then \
		echo "[ERROR] No command specified. Usage: make infisical-run COMMAND=\"your command\""; \
		exit 1; \
	fi
	@echo "[INFO] Running command with Infisical secrets: $(COMMAND)"
	@source scripts/setup_env_from_infisical.sh && $(COMMAND)

# Test target: Run all pytest tests in the tests directory
test:
	@echo "Running all pytest tests..."
	@pytest $(TESTS_DIR)/test_*.py -v

# Prevent Make from treating component arguments as targets
%:
	@: