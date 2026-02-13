# Grounding Experiments

Two phases: retrieval quality (Phase 1) and generation stability (Phase 2).

## Phase 1: Retrieval Experiment

Validates that `reviewExamples` retrieves semantically relevant few-shot
examples in the correct order. Tests retrieval quality — not code generation.

## What It Tests

| Experiment Type    | What                                        | Env        |
|--------------------|---------------------------------------------|------------|
| `same_domain`      | Math query → math examples rank top         | Staging    |
| `cross_domain`     | Math query → web/data examples rank low     | Staging    |
| `self_retrieval`   | Exact prompt → exact example rank 1         | Staging    |
| `language_filter`  | Python examples ranked above JS             | Staging    |
| `validated_boost`  | Validated (fix) examples get +0.1 boost     | Staging    |
| `pin`              | Pinned example appears with score 1.0       | Both       |
| `exclude`          | Excluded example absent from results        | Both       |
| `conflict`         | Pin + exclude same slug → 400 error         | Both       |
| `stability`        | Same query 3x → same ranking               | Both       |

## Prerequisites

- Firebase emulator running (for local tests)
- `firebase-admin`, `google-cloud-firestore`, `requests` installed
- For staging: Infisical configured with `--env=staging` secrets
- For staging semantic tests: `GOOGLE_API_KEY` for real embeddings

## Quick Start

```bash
# Local emulator (tests pin, exclude, conflict, stability)
make experiment-local

# Staging (tests ALL including semantic retrieval quality)
infisical run --env=staging -- make experiment-staging

# Just view results
make summarize
```

## Individual Steps

```bash
# Seed test examples into Firestore
make seed-local          # or: make seed-staging

# Run retrieval queries
make run-local           # or: make run-staging

# Clean up test data
make cleanup-local       # or: make cleanup-staging

# Dry run (see what would be seeded)
make seed-dry-run
```

## Output

Results are written to `results/retrieval_results.csv` with columns:

```
timestamp_utc, env, query_id, experiment_type, command, language, limit,
pin_slugs, exclude_slugs, run_number, http_status, examples_returned_count,
example_ids, example_scores, rank_1_id, rank_1_score,
assertion_passed, assertion_detail, response_time_ms
```

## Caveats

- **Emulator limitations**: SHA-based deterministic embeddings don't capture
  semantic similarity. Only pin, exclude, conflict, and stability tests work
  locally. Semantic ranking tests (same_domain, cross_domain, etc.) require
  staging with real `gemini-embedding-001` embeddings.

- **Vector index latency**: After seeding in staging, Firestore may need up to
  30 minutes to index new vectors. Run `make seed-staging` well in advance of
  the first experiment.

- **Cache**: `search_similar_examples` caches results for 1 hour. Use a fresh
  emulator instance per run to avoid stale results.

## Test Corpus

7 examples across 3 domains (math, web, data) — see `seed_data/domains.json`.
2 examples are "validated" (`command=fix`) which triggers the +0.1 score boost.

---

## Phase 2: Generation Stability Experiment

Measures whether grounding (few-shot examples) improves code generation
stability by comparing two code paths:

- **Grounded arm**: `POST /generateCode` — cloud endpoint with grounding enabled
  (calls `reviewExamples`, injects `<FEW_SHOT_EXAMPLE>` XML block)
- **Ungrounded arm**: `pdd --local --force --temperature 0.0 generate` — local CLI,
  no grounding

Both paths call the same `code_generator()` from `pdd/pdd/code_generator.py`.
The only meaningful difference is whether a few-shot example is injected.
No production code changes are required.

### Prerequisites

- `pdd` CLI installed and on PATH (for the ungrounded/local arm)
- Local LLM API key configured (used by `pdd --local`)
- For staging: Infisical configured with `--env=staging` secrets (for the grounded arm)

### How It Works

For each of 5 test prompts:
1. **Grounded arm**: Call cloud `generateCode` endpoint — N runs (default 3)
2. **Ungrounded arm**: Run `pdd --local` CLI — N runs (default 3)
3. Compare stability metrics between arms

### Stability Metrics

- **Exact match rate**: How many runs produce byte-identical code (via SHA-256 hash)
- **Lines of code stddev**: Variation in output length across runs
- **Pairwise similarity**: Average normalized Levenshtein distance between all run pairs
- **Examples used**: Which grounding example was selected (verifies retrieval works)

### Quick Start

```bash
# 1. Seed examples (for grounded arm to find matches)
infisical run --env=staging -- make seed-staging

# 2. Wait 5-30 min for vector index

# 3. Run experiment (no backend deploy needed!)
infisical run --env=staging -- make gen-stability-staging

# 4. View results
make gen-summarize

# 5. Cleanup
infisical run --env=staging -- make cleanup-staging
```

```bash
# Against prod (requires PDD_JWT_TOKEN with credits)
PDD_JWT_TOKEN=<token> make gen-stability-prod
make gen-summarize
```

### Output

- `results/generation_stability.csv` — structured results per run
- `results/generations/{prompt_id}_{arm}_run{N}.py` — raw generated code for diffing

### Costs

Only the grounded arm uses staging credits (~$0.05/generation x 5 prompts x 3 runs = ~$0.75).
The ungrounded arm uses the local API key (cost depends on provider).

### Expected Outcome

If grounding works correctly:
- **Grounded arm** shows higher exact match rate (few-shot example anchors output)
- **Grounded arm** shows lower lines-of-code stddev (less variation)
- **Ungrounded arm** shows more variation (no reference point)
- Prompts matching seeded examples show the largest stability delta
- The no-match prompt (rgb-to-hex) shows similar stability in both arms
