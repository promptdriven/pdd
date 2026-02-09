SHELL := /bin/bash

.PHONY: init new-agentic new-pdd summarize clean scr-run scr-summary

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

scr-run:
	@if [ -z "$(ARM)" ] || [ -z "$(RUN_ID)" ]; then echo "Usage: make scr-run ARM=agentic RUN_ID=10"; exit 1; fi
	./scripts/run_scr_full.sh "$(ARM)" "$(RUN_ID)"

scr-summary:
	python3 scripts/scr_summarize.py

clean:
	rm -rf runs/agentic runs/pdd results/run_results.csv results/scr_code_metrics.csv
	@echo "Cleaned run workspaces and results CSV."
