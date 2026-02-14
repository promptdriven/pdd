SHELL := /bin/bash

.PHONY: seed-local seed-staging run-local run-staging cleanup-local cleanup-staging \
        experiment-local experiment-staging summarize clean \
        gen-stability-staging gen-stability-prod gen-summarize gen-experiment-staging clean-gen \
        llm-invoke-prod llm-invoke-staging llm-invoke-seed-staging \
        llm-invoke-pdd-local-prod \
        llm-invoke-evaluate llm-invoke-summarize \
        llm-invoke-experiment-prod llm-invoke-experiment-staging clean-llm-invoke

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
# llm_invoke regeneration experiment
# ---------------------------------------------------------------------------

llm-invoke-prod:
	python3 scripts/run_llm_invoke_stability.py --env prod --runs 5 --temperature 1.0

llm-invoke-staging:
	infisical run --env=staging -- python3 scripts/run_llm_invoke_stability.py --env staging --runs 5 --temperature 1.0

llm-invoke-pdd-local-prod:
	python3 scripts/run_llm_invoke_stability.py \
		--env prod --runs 5 --temperature 1.0 --arms ungrounded-pdd

llm-invoke-seed-staging:
	infisical run --env=staging -- python3 scripts/seed_llm_invoke_staging.py

llm-invoke-evaluate:
	python3 scripts/evaluate_llm_invoke.py

llm-invoke-summarize:
	python3 scripts/summarize_llm_invoke.py

llm-invoke-experiment-prod: clean-llm-invoke llm-invoke-prod llm-invoke-evaluate llm-invoke-summarize
	@echo "llm_invoke regeneration experiment complete (prod)."

llm-invoke-experiment-staging: clean-llm-invoke llm-invoke-staging llm-invoke-evaluate llm-invoke-summarize
	@echo "llm_invoke regeneration experiment complete (staging)."

clean-llm-invoke:
	rm -rf results/llm_invoke_stability.csv results/llm_invoke_evaluation.csv results/llm_invoke_generations/
	@echo "Cleaned llm_invoke experiment results."

# ---------------------------------------------------------------------------
# Clean results
# ---------------------------------------------------------------------------

clean:
	rm -f results/retrieval_results.csv
	@echo "Cleaned results."
