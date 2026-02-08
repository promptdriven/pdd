SHELL := /bin/bash

.PHONY: init new-agentic new-pdd summarize clean

init:
	mkdir -p runs/agentic runs/pdd results
	touch results/run_results.csv
	@echo "Initialized replay_stability_ab experiment directories."

new-agentic:
	@if [ -z "$(RUN_ID)" ]; then echo "Usage: make new-agentic RUN_ID=01"; exit 1; fi
	./scripts/create_run_workspace.sh agentic "$(RUN_ID)"

new-pdd:
	@if [ -z "$(RUN_ID)" ]; then echo "Usage: make new-pdd RUN_ID=01"; exit 1; fi
	./scripts/create_run_workspace.sh pdd "$(RUN_ID)"

summarize:
	python3 scripts/summarize_results.py --results results/run_results.csv

clean:
	rm -rf runs/agentic runs/pdd results/run_results.csv
	@echo "Cleaned run workspaces and results CSV."
