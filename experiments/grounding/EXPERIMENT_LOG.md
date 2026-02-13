# Experiment Log: Grounding Validation

Updated: 2026-02-13
Experiment directory: `experiments/grounding/`
Retrieval CSV: `experiments/grounding/results/retrieval_results.csv`
Generation CSV: `experiments/grounding/results/generation_stability.csv`

## Scope

This log captures recorded runs for the grounding validation experiment, which measures:
1. **Phase 1 — Retrieval quality**: Does `reviewExamples` vector search return semantically relevant few-shot examples?
2. **Phase 2 — Generation stability**: Does grounding (few-shot examples) improve code generation consistency?

## Phase 1: Retrieval Quality

### Run 1 — Staging (2026-02-12)

- **Environment**: Staging (`prompt-driven-development-stg`)
- **Embedding model**: `gemini-embedding-001` (post-migration from `text-embedding-004`)
- **Few-shot collection**: 7 seeded test examples across 3 domains (math, web, data)
- **Results**: See `results/retrieval_results.csv`

All retrieval tests passed on staging, including semantic ranking (same_domain, cross_domain, self_retrieval), filtering (language_filter, pin, exclude), and stability (3x repeated queries).

## Phase 2: Generation Stability

### Run 1 — Staging (2026-02-12)

- **Environment**: Staging
- **Embedding model**: `gemini-embedding-001`
- **Few-shot collection**: 7 seeded test examples
- **Generation model**: `vertex_ai/gemini-3-flash-preview` (grounded arm), local CLI (ungrounded arm)
- **Temperature**: 0.0
- **Runs per arm**: 3
- **Prompts**: 5 (factorial, fibonacci, csv-parser, flask-api, no-match)
- **Results**: Staging run confirmed experiment infrastructure works end-to-end

### Run 2 — Production (2026-02-13)

- **Environment**: Production (`prompt-driven-development`)
- **Embedding model**: `gemini-embedding-001` (1025 production `few_shot` documents migrated from `text-embedding-004`)
- **Generation model**: `vertex_ai/gemini-3-flash-preview` (grounded arm), local CLI (ungrounded arm)
- **Temperature**: 0.0
- **Runs per arm**: 3
- **Prompts**: 5 (factorial, fibonacci, csv-parser, flask-api, no-match)
- **Total calls**: 30 (27 succeeded, 3 failed — JWT token expired on gen-no-match grounded arm)
- **Total cost**: ~$0.10 (grounded arm only; ungrounded uses local API)
- **Auth**: Production JWT via GitHub OAuth Device Flow

#### Results

| Prompt | Arm | Runs | Exact Match | Lines | Examples Used | Avg Time |
|---|---|---:|---:|---:|---|---:|
| gen-factorial | grounded | 3 | 3/3 (100%) | 36 | (none) | 26.7s |
| gen-factorial | ungrounded | 3 | 3/3 (100%) | 53 | — | 9.6s |
| gen-fibonacci | grounded | 3 | 3/3 (100%) | 39 | `N8iZ6cVhNZ540DgAEvm9` | 10.7s |
| gen-fibonacci | ungrounded | 3 | 3/3 (100%) | 63 | — | 9.2s |
| gen-csv-parser | grounded | 3 | 3/3 (100%) | 80 | `xvh1jzeSGgGTmZjQeD2L` | 12.8s |
| gen-csv-parser | ungrounded | 3 | 3/3 (100%) | 238 | — | 10.2s |
| gen-flask-api | grounded | 3 | 3/3 (100%) | 35 | (none) | 16.4s |
| gen-flask-api | ungrounded | 3 | 3/3 (100%) | 136 | — | 8.7s |
| gen-no-match | grounded | 3 | **FAILED** | 0 | — | 0.1s |
| gen-no-match | ungrounded | 3 | 3/3 (100%) | 31 | — | 8.5s |

#### Example Retrieval

| Prompt | Example ID | Domain Match |
|---|---|---|
| gen-factorial | (none) | No matching example in prod collection |
| gen-fibonacci | `N8iZ6cVhNZ540DgAEvm9` | Math domain hit |
| gen-csv-parser | `xvh1jzeSGgGTmZjQeD2L` | Data domain hit |
| gen-flask-api | (none) | No matching example in prod collection |
| gen-no-match | (none) | Expected: control prompt with no domain match |

#### Aggregate Metrics

| Metric | Grounded | Ungrounded | Delta |
|---|---|---|---|
| Exact match rate | 100% | 100% | +0.0pp |
| Avg lines stddev | 0.0 | 0.0 | 0.0 |
| Avg pairwise similarity | 0.800* | 1.000 | -0.200 |
| Avg response time | 13.3s | 9.2s | +4.1s |

*Grounded pairwise similarity is dragged down to 0.800 by the 3 failed gen-no-match runs (empty output → 0.0 similarity). Excluding gen-no-match, grounded pairwise similarity is 1.000.

### Data Issues

1. **JWT token expiration**: The production JWT expired after ~4.5 minutes into the experiment, causing all 3 gen-no-match grounded runs to return HTTP 401. The gen-no-match ungrounded runs completed successfully. This is the control prompt (designed to have no matching few-shot examples), so the missing data is less critical but should be backfilled.
2. **9 of 15 grounded runs had no example retrieved** (`[NO_EXAMPLE]`): factorial (3), flask-api (3), and no-match (3). Only fibonacci and csv-parser found matching examples. This indicates the production `few_shot` collection has coverage gaps for some prompt domains.

## Key Findings

### 1. Temperature 0.0 produces trivially perfect stability
Both arms achieved 100% exact match rate across all runs. At temperature 0.0, deterministic sampling eliminates variation entirely. **To meaningfully test the grounding stability hypothesis, re-run at temperature 0.3-0.7.**

### 2. Grounding produces dramatically more concise code
Across 4 completed prompts, the grounded arm produced 2.5x fewer lines on average:

| Prompt | Grounded Lines | Ungrounded Lines | Reduction |
|---|---:|---:|---|
| gen-factorial | 36 | 53 | 1.5x |
| gen-fibonacci | 39 | 63 | 1.6x |
| gen-csv-parser | 80 | 238 | 3.0x |
| gen-flask-api | 35 | 136 | 3.9x |

The ungrounded arm consistently adds verbose `if __name__ == "__main__"` demo blocks, extra methods, and elaborate error handling. The grounded arm produces focused, production-ready code.

### 3. Conciseness effect persists even without few-shot examples
factorial and flask-api retrieved no examples, yet still produced concise output from the grounded arm. This means the `generateCode` endpoint's system prompt and orchestration (not just few-shot examples) contributes to code conciseness.

### 4. Vector search found examples for 2 of 5 prompts
fibonacci matched `N8iZ6cVhNZ540DgAEvm9` and csv-parser matched `xvh1jzeSGgGTmZjQeD2L`. factorial and flask-api found no matches. The production collection (1025 documents) has domain coverage gaps.

### 5. Cold start latency is significant
The first grounded call per prompt took 25-62s (includes vector search + cold start), while subsequent calls took 3-9s (cache hit). This suggests `reviewExamples` or `generateCode` caching is effective but cold starts are expensive.

## Model Provenance

Both arms used `vertex_ai/gemini-3-flash-preview` (model parity confirmed).

| Arm | Execution Path | Model | How Resolved |
|---|---|---|---|
| grounded | `POST /generateCode` → `reviewExamples` → `code_generator()` | `vertex_ai/gemini-3-flash-preview` | Reported in `generateCode` response `modelName` field |
| ungrounded | `pdd --local --force --temperature 0.0 generate` | `vertex_ai/gemini-3-flash-preview` | Via `PDD_MODEL_DEFAULT` in `.env`; CSV records `local` (does not capture resolved model name) |

Note: The generation_stability.csv records `model_name=local` for the ungrounded arm rather than the resolved model. The actual model is `vertex_ai/gemini-3-flash-preview` per `PDD_MODEL_DEFAULT=vertex_ai/gemini-3-flash-preview` in `/Users/gregtanaka/Documents/pdd_cloud/.env`.

## Next Steps

1. **Backfill gen-no-match grounded data**: Refresh JWT and re-run only the gen-no-match grounded arm (3 calls).
2. **Re-run at temperature 0.3 or 0.7**: The stability hypothesis can only be tested meaningfully with nondeterministic sampling. Increase N to 10+ runs per arm.
3. **Investigate coverage gaps**: Why did factorial and flask-api not find examples? Check the 1025 prod `few_shot` documents for math/algorithm and web/API coverage.
4. **Cost analysis**: Grounded arm cost ~$0.10 total ($0.006/call avg). At scale, the question is whether the conciseness benefit justifies the vector search overhead.
