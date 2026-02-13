# Experiments

This directory contains benchmark and validation experiments that are more
research-oriented than the product examples in `examples/`.

## Available

1. `replay_stability_ab/`
   - A/B replay stability comparison (`PDD` vs `Agentic-Only`)
   - Includes baseline assets, run workspace scaffolding, evaluation scripts,
     and result summarization tools.

2. `grounding/`
   - Retrieval quality validation for `reviewExamples` endpoint
   - Seeds known test examples, runs retrieval queries, and measures whether
     the system returns the right examples in the right order (vector search
     ranking, score boosts, pin/exclude overrides, ranking stability).
