SHELL := /bin/bash

.PHONY: seed-local seed-staging run-local run-staging cleanup-local cleanup-staging \
        experiment-local experiment-staging summarize clean \
        gen-stability-staging gen-stability-prod gen-summarize gen-experiment-staging clean-gen

# ---------------------------------------------------------------------------
# Seed test examples
# ---------------------------------------------------------------------------

seed-local:
	python3 scripts/seed_examples.py --env local

seed-staging:
	infisical run --env=staging -- python3 scripts/seed_examples.py --env staging

seed-dry-run:
	python3 scripts/seed_examples.py --env local --dry-run

# ---------------------------------------------------------------------------
# Run retrieval queries
# ---------------------------------------------------------------------------

run-local:
	python3 scripts/run_retrieval.py --env local

run-staging:
	infisical run --env=staging -- python3 scripts/run_retrieval.py --env staging

# ---------------------------------------------------------------------------
# Cleanup test data
# ---------------------------------------------------------------------------

cleanup-local:
	python3 scripts/cleanup_examples.py --env local

cleanup-staging:
	infisical run --env=staging -- python3 scripts/cleanup_examples.py --env staging

# ---------------------------------------------------------------------------
# Summarize results
# ---------------------------------------------------------------------------

summarize:
	python3 scripts/summarize_results.py

# ---------------------------------------------------------------------------
# Full experiment cycle
# ---------------------------------------------------------------------------

experiment-local: clean seed-local run-local cleanup-local summarize
	@echo "Local experiment complete."

experiment-staging: clean seed-staging run-staging cleanup-staging summarize
	@echo "Staging experiment complete."

# ---------------------------------------------------------------------------
# Generation stability experiment
# ---------------------------------------------------------------------------

gen-stability-staging:
	infisical run --env=staging -- python3 scripts/run_generation_stability.py --env staging

gen-stability-prod:
	python3 scripts/run_generation_stability.py --env prod

gen-summarize:
	python3 scripts/summarize_generation.py

gen-experiment-staging: clean-gen seed-staging gen-stability-staging cleanup-staging gen-summarize
	@echo "Generation stability experiment complete."

clean-gen:
	rm -rf results/generation_stability.csv results/generations/
	@echo "Cleaned generation results."

# ---------------------------------------------------------------------------
# Clean results
# ---------------------------------------------------------------------------

clean:
	rm -f results/retrieval_results.csv
	@echo "Cleaned results."
