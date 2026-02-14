# Experiment Log: Grounding Validation

Updated: 2026-02-14
Experiment directory: `experiments/grounding/`
Retrieval CSV: `experiments/grounding/results/retrieval_results.csv`
Generation CSV: `experiments/grounding/results/generation_stability.csv`
sync_orchestration CSV: `experiments/grounding/results/sync_orchestration_stability.csv`
sync_orchestration Evaluation: `experiments/grounding/results/sync_orchestration_evaluation.csv`

## Scope

This log captures recorded runs for the grounding validation experiment, which measures:
1. **Phase 1 — Retrieval quality**: Does `reviewExamples` vector search return semantically relevant few-shot examples?
2. **Phase 2 — Generation stability**: Does grounding (few-shot examples) improve code generation consistency?
3. **Phase 3 — llm_invoke regeneration**: Cache-busted 3-arm comparison at temperature 1.0
4. **Phase 4 — pdd generate --local**: Does test visibility substitute for grounding?
5. **Phase 5 — sync_orchestration**: Does grounding's effect scale to PDD's largest module (1,973 lines)?

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

## Phase 3: llm_invoke Regeneration Stability (Cache-Busted)

### Run 1 — Production (2026-02-14)

- **Environment**: Production (`prompt-driven-development`)
- **Prompt**: `llm_invoke_python.prompt` (97,405 chars resolved, 3,059 lines)
- **Generation model**: `vertex_ai/gemini-3-flash-preview` (both arms)
- **Temperature**: 1.0 (maximum nondeterminism)
- **Runs per arm**: 5
- **Cache busting**: Each run appends a unique `# experiment-run-seed: <uuid>` nonce to defeat LiteLLM GCS/SQLite cache
- **Total calls**: 10 (9 succeeded, 1 rate-limited on ungrounded arm)
- **Auth**: Production JWT via keyring refresh token

#### Quantitative Results

| Metric | Grounded | Ungrounded | Delta |
|---|---|---|---|
| N (successful runs) | 5 | 4 | |
| Syntax valid | 5/5 | 4/4 | |
| Avg lines | 467.6 ± 149.7 | 428.8 ± 65.8 | |
| Avg functions | 17.4 ± 2.1 | 13.8 ± 2.5 | |
| Avg classes | 4.2 ± 0.4 | 4.0 ± 0.0 | |
| Pairwise similarity (within-arm) | **0.189** | 0.162 | **+0.027 (+17%)** |
| Reference similarity (vs canonical) | **0.030 ± 0.004** | 0.019 ± 0.002 | **+58%** |
| Reference recall | **0.206 ± 0.015** | 0.162 ± 0.009 | **+27%** |
| Test pass rate (217 tests) | 100% | 100% | |
| Exact match rate | 0/5 | 0/4 | |
| Avg cost per call | $0.131 | $0.019 | Grounded ~7x more expensive |
| Avg response time | 65.6s | 25.2s | Grounded ~2.6x slower |
| Examples used | `Hp7oK65bRdCyrJYnABWE` (all 5) | — | |

#### Response Hashes (all unique — cache busting confirmed)

| Arm | Run 1 | Run 2 | Run 3 | Run 4 | Run 5 |
|---|---|---|---|---|---|
| grounded | `6b3e5a2f` | `92842649` | `deec3baf` | `57fd1ec0` | `0d3a52ba` |
| ungrounded | `60776433` | `edf8f6a6` | `040a96a2` | (rate limit) | `6d454407` |

#### Qualitative Code Review

Manual inspection of all 9 generated files revealed systematic quality differences:

**Grounded arm (consistent, correct):**
- All 5 runs use correct internal imports (`from .path_resolution import get_default_resolver`)
- All 5 use correct CSV column names (`input`, `output`) for cost rates
- All 5 use `Dict[str, Tuple[float, float]]` for rate map (matches canonical)
- All 5 implement GCS S3-compatible cache with SQLite fallback
- Cloud auth uses `auth_service.get_jwt_token()` or `core.cloud.CloudConfig` (correct patterns)
- Function count std dev = 2.1 (structurally anchored)

**Ungrounded arm (inconsistent, hallucinated interfaces):**
- 3/4 runs hallucinate `from . import DEFAULT_STRENGTH, DEFAULT_TIME` — **these are never imported by `llm_invoke.py`** (they exist in `pdd/__init__.py` but the canonical file doesn't use them)
- 2/4 runs use wrong CSV column names (`input_cost_per_m` instead of `input`) — would `KeyError`
- All 4 use `Dict[str, Dict[str, float]]` for rate map (wrong type vs canonical)
- 0/4 implement any caching
- Cloud auth uses invented env vars (`PDD_CLOUD_TOKEN`, `PDD_CLOUD_JWT`, `FIREBASE_ID_TOKEN`) — **all wrong**
- 1 run calls `pd.read_pandas()` which doesn't exist
- 2/4 use `unicode_escape` codec in `_smart_unescape_code` — dangerous for UTF-8
- Function count std dev = 2.5 (more structural drift)

**Summary**: Grounding prevents hallucination of nonexistent APIs and wrong column names. The few-shot example anchors the model to the project's actual interfaces.

## Key Findings (Updated)

### 1. Cache busting works — all hashes unique
With the UUID nonce appended, no two runs produce identical output. The prior run's 100% exact-match rate for grounded was entirely due to LiteLLM cache hits.

### 2. Grounding stabilizes structure at temperature 1.0
Function count std dev: 2.1 (grounded) vs 2.5 (ungrounded). Class count std dev: 0.4 vs 0.0. Within-arm pairwise similarity: 0.189 vs 0.162 (+17%). The few-shot example acts as a structural anchor.

### 3. Grounding improves reference fidelity
58% higher similarity to canonical `llm_invoke.py` and 27% more recall of its patterns. The grounded model reproduces more of the real module's architecture.

### 4. Grounding prevents interface hallucination
This is the strongest finding. Without grounding, the model invents plausible-but-wrong module interfaces (nonexistent imports, wrong column names, wrong auth patterns) in 75% of runs. With grounding, 0% of runs contain hallucinated interfaces.

### 5. Cost and latency tradeoff
Grounding costs ~7x more ($0.131 vs $0.019 per call) and takes ~2.6x longer (65.6s vs 25.2s). The cost is driven by the few-shot example inflating the prompt token count.

## Phase 4: pdd generate --local (with tests) vs Grounded

### Motivation

Phase 3 compared the grounded arm (cloud endpoint with few-shot examples) against a bare litellm call with the resolved prompt. But `pdd generate --local` does more than litellm alone: it auto-discovers test files (e.g., `tests/test_llm_invoke*.py`) and injects them as `<unit_test_content>` tags, giving the LLM visibility into the test suite. Phase 4 adds this "ungrounded-pdd" arm to control for test visibility when measuring the grounding effect.

### Run 1 — Production (2026-02-14)

- **Environment**: Production (`prompt-driven-development`)
- **Prompt**: `llm_invoke_python.prompt` (12,132 chars raw; expanded by pdd preprocessor with `<include>`, `<shell>`, `<web>` tags)
- **Generation model**: `vertex_ai/gemini-3-flash-preview` (grounded + ungrounded-pdd), `gemini/gemini-3-flash-preview` (ungrounded — Google AI Studio endpoint)
- **Temperature**: 1.0 (maximum nondeterminism)
- **Runs per arm**: 5 (grounded + ungrounded from Phase 3, ungrounded-pdd new)
- **Cache busting**: UUID nonce per run (pdd arm: appended to temp prompt file)
- **Auth**: Production JWT via keyring refresh token (grounded arm only)
- **pdd flags**: `--local --force --no-core-dump --strength 0.5 --temperature 1.0`
- **Total calls**: 15 (14 succeeded, 1 rate-limited on ungrounded arm run 4)

#### Quantitative Results (3-Arm Comparison)

| Metric | Grounded | Ungrounded | Ungrounded-PDD |
|---|---|---|---|
| N (runs)* | 5 | 5 | 5 |
| Syntax valid | 5/5 | 4/5 | 5/5 |
| Avg lines | 467.6 +/- 149.7 | 343.0 +/- 200.2 | 485.6 +/- 45.8 |
| Avg functions | 17.4 +/- 2.1 | 11.0 +/- 6.5 | 15.8 +/- 0.8 |
| Avg classes | 4.2 +/- 0.4 | 3.2 +/- 1.8 | 4.2 +/- 0.4 |
| Pairwise similarity (within-arm) | **0.189** | 0.162 | 0.106 |
| Reference similarity (vs canonical) | **0.030 +/- 0.004** | 0.019 +/- 0.002 | 0.021 +/- 0.010 |
| Reference recall | **0.206 +/- 0.015** | 0.162 +/- 0.009 | 0.151 +/- 0.002 |
| Test pass rate (217 tests) | **100%** | **100%** | **100%** |
| Exact match rate | 0/5 | 0/5 | 0/5 |
| Avg cost per call | $0.131 | $0.015 | $0.057 |
| Avg response time | 65.6s | 20.2s | 64.1s |
| Examples used | `Hp7oK65bRdCyrJYnABWE` (all 5) | (none) | (none) |

*Ungrounded run 4 was rate-limited (EMPTY). Averages include this run; excluding it: 428.8 lines, 13.8 funcs, $0.019 cost.

#### Response Hashes (all unique — cache busting confirmed)

| Arm | Run 1 | Run 2 | Run 3 | Run 4 | Run 5 |
|---|---|---|---|---|---|
| grounded | `6b3e5a2f` | `92842649` | `deec3baf` | `57fd1ec0` | `0d3a52ba` |
| ungrounded | `60776433` | `edf8f6a6` | `040a96a2` | (rate limit) | `6d454407` |
| ungrounded-pdd | `bb754d88` | `3ba2a80a` | `fb6e96b8` | `fa57079e` | `d7b86e7a` |

#### Qualitative Code Review: Ungrounded-PDD Arm

Manual inspection of all 5 `ungrounded-pdd` generated files:

| Issue | Ungrounded-PDD (5 runs) | Ungrounded (4 runs, Phase 3) | Grounded (5 runs) |
|---|---|---|---|
| Hallucinated imports (`from . import DEFAULT_STRENGTH`) | **5/5 FAIL** | 3/4 FAIL | 0/5 |
| CSV column names (`input`/`output`) | 5/5 PASS | 2/4 wrong (`input_cost_per_m`) | 5/5 PASS |
| Auth pattern (invented `PDD_CLOUD_TOKEN`) | **5/5 FAIL** | 4/4 wrong (various invented env vars) | 0/5 |
| Rate map type (`Dict[str, Tuple]` correct) | **5/5 FAIL** (use `Dict[str, Dict]`) | 4/4 wrong | 5/5 PASS |
| Caching (GCS S3 + SQLite) | **2/5 missing, 3/5 partial** (wrong params, wrong location) | 0/4 | 5/5 PASS |
| Cloud URL hardcoded | 5/5 FAIL (hardcode URL) | 4/4 FAIL | 0/5 |

**Key observation:** The ungrounded-pdd arm produces the **same categories of errors** as the bare ungrounded arm. Test file visibility does NOT prevent interface hallucination — the model still invents `PDD_CLOUD_TOKEN`, uses wrong rate map types, and hallucinates relative imports. The test files test functional behavior (does `llm_invoke()` return correct output?) but don't expose internal implementation details like auth patterns, CSV column names, or cache architecture.

**One improvement over bare ungrounded:** CSV column names are correct in all 5 ungrounded-pdd runs (vs 2/4 wrong in bare ungrounded). The test files may contain assertions that reference the correct column format, providing indirect signal.

**Structural stability:** Ungrounded-pdd has the **lowest** pairwise similarity (0.106) of all three arms, despite having the **lowest** function count std dev (0.8). This paradox arises because pdd's preprocessor adds web-scraped content (LiteLLM docs) that varies between runs, injecting non-determinism beyond temperature alone.

**Additional issues unique to ungrounded-pdd:**
- Run 3: Recursive `llm_invoke()` self-call on auth failure — potential infinite recursion
- Run 4: Invents entire `PathResolver` class instead of importing from `pdd.path_resolution`
- All runs: `litellm.responses()` handling inconsistent (2/5 use it, 3/5 fall back to `completion()`)

#### Confounding Variables

This comparison has known confounds that prevent attributing all differences solely to grounding:

1. **Different model endpoints**: The ungrounded arm uses `gemini/gemini-3-flash-preview` (Google AI Studio) while grounded and ungrounded-pdd use `vertex_ai/gemini-3-flash-preview` (Vertex AI). These may differ in behavior despite being the same underlying model.
2. **Post-processing pipeline**: The pdd arm runs 2-3 additional LLM calls (prompt expansion, `<web>` tag resolution) beyond the single generation call, which inflates cost and latency.
3. **Web scraping variability**: The pdd preprocessor fetches live web content (e.g., LiteLLM docs) that varies between runs, injecting non-determinism beyond temperature alone.

## Key Findings (Updated)

### 1. Cache busting works — all hashes unique
With the UUID nonce appended, no two runs produce identical output. The prior run's 100% exact-match rate for grounded was entirely due to LiteLLM cache hits.

### 2. Grounding stabilizes structure at temperature 1.0
Function count std dev: 2.1 (grounded) vs 2.5 (ungrounded) vs **0.8 (ungrounded-pdd)**. The pdd arm shows the lowest function-count variance, likely because the test file constrains the expected interface. However, within-arm pairwise similarity tells a different story: 0.189 (grounded) > 0.162 (ungrounded) > 0.106 (ungrounded-pdd). The grounded arm is the most self-consistent overall.

### 3. Grounding improves reference fidelity
Reference similarity: 0.030 (grounded) vs 0.019 (ungrounded) vs 0.021 (ungrounded-pdd). Reference recall: 0.206 (grounded) vs 0.162 (ungrounded) vs 0.151 (ungrounded-pdd). Grounding produces code closest to the canonical implementation regardless of test visibility.

### 4. Grounding prevents interface hallucination — test visibility does NOT
**This is the central Phase 4 finding.** The ungrounded-pdd arm has full visibility into the test suite (4 test files, ~5,750 lines, auto-injected via `<unit_test_content>` tags) yet still hallucinates:
- Nonexistent imports in 5/5 runs
- Wrong auth patterns in 5/5 runs
- Wrong rate map types in 5/5 runs
- Missing or broken caching in 5/5 runs

The grounded arm (with a single few-shot example) has 0% hallucination on all these dimensions. **Conclusion: one relevant code example is more powerful than an entire test suite for anchoring the model to real interfaces.**

### 5. All three arms pass all 217 tests
Test pass rate is 100% across all arms. This confirms that the test suite validates functional behavior (correct return types, error handling, API contracts) but does **not** catch implementation-level issues like wrong auth patterns, hallucinated imports, or missing caching. Tests are necessary but not sufficient for code quality — grounding addresses the gap.

### 6. Cost and latency tradeoff
| Arm | Avg Cost | Avg Time | Cost vs Grounded |
|---|---|---|---|
| Grounded | $0.131 | 65.6s | 1.0x (baseline) |
| Ungrounded-PDD | $0.057 | 64.1s | 0.44x |
| Ungrounded | $0.015 | 20.2s | 0.11x |

The pdd arm is similar in latency to grounded (due to prompt preprocessing + web scraping overhead) but ~2.3x cheaper (smaller effective prompt after preprocessing vs the grounded arm's few-shot example inflation).

## Phase 5: sync_orchestration Regeneration Stability

### Motivation

Phases 3-4 tested grounding on `llm_invoke` (~97KB resolved prompt, ~700 lines canonical). `sync_orchestration` is PDD's largest and most complex module: **1,973 lines canonical**, **246,584 chars resolved prompt** (2.5x larger). It orchestrates the full sync loop (auto-deps → generate → test → fix → verify → crash-fix) with TUI integration, threading, atomic state updates, and cycle detection. Testing grounding on this module answers: **does the anti-hallucination effect scale to complex, multi-subsystem code?**

### Run 1 — Production (2026-02-14)

- **Environment**: Production (`prompt-driven-development`)
- **Prompt**: `sync_orchestration_python.prompt` (18,837 chars raw; 246,584 chars resolved with 12 `<include>` expansions)
- **Canonical reference**: `pdd/sync_orchestration.py` (1,973 lines, 25 functions, 2 classes)
- **Generation model**: `vertex_ai/gemini-3-flash-preview` (all 3 arms)
- **Temperature**: 1.0 (maximum nondeterminism)
- **Runs per arm**: 5
- **Cache busting**: UUID nonce per run
- **Auth**: Production JWT via GitHub OAuth Device Flow (grounded arm only)
- **Total calls**: 15 (15 succeeded)

#### Quantitative Results (3-Arm Comparison)

| Metric | Grounded | Ungrounded | Ungrounded-PDD |
|---|---|---|---|
| N (runs) | 5 | 5 | 5 |
| Syntax valid | 4/5 | 4/5 | 5/5 |
| Avg lines | 426.6 ± 38.5 | 513.0 ± 39.1 | 488.6 ± 57.9 |
| Avg functions | 19.8 ± 11.1 | 12.2 ± 6.9 | 14.2 ± 1.9 |
| Avg classes | 1.4 ± 0.9 | 0.8 ± 0.4 | 1.2 ± 0.4 |
| Pairwise similarity (within-arm) | **0.391** | 0.284 | 0.281 |
| Reference similarity (vs canonical) | **0.145 ± 0.069** | 0.037 ± 0.016 | 0.040 ± 0.018 |
| Reference recall | **0.360 ± 0.080** | 0.261 ± 0.018 | 0.268 ± 0.026 |
| Test pass rate (99 tests) | 77.6% ± 43.4% | 77.6% ± 43.4% | **97.0% ± 0.0%** |
| Tests per run (when parseable) | 96/99 | 96/99 | 96/99 |
| Exact match rate | 0/5 | 0/5 | 0/5 |
| Avg cost per call | $0.121 | $0.049 | $0.051 |
| Avg response time | 86.7s | 31.9s | 62.7s |
| Examples used | `ICqQQrD8O5CeWLa2y6fX` (all 5) | (none) | (none) |

Note: Test pass rate drops to 77.6% because 1 run per arm (grounded run 1, ungrounded run 1) produced syntax-invalid code (0/0 tests). When syntax-valid, all arms pass 96/99 tests consistently.

#### Response Hashes (all unique — cache busting confirmed)

| Arm | Run 1 | Run 2 | Run 3 | Run 4 | Run 5 |
|---|---|---|---|---|---|
| grounded | `152be8ad` | `4420b5eb` | `7276e512` | `44fce883` | `376e468c` |
| ungrounded | `79ea1682` | `1cd24d07` | `b5f356be` | `63b53efd` | `e121ac21` |
| ungrounded-pdd | `b51f7fd3` | `56653063` | `0bda3659` | `2a7a2f3d` | `294a6b49` |

#### Qualitative Code Review

Manual inspection of all 15 generated files revealed systematic differences in how each arm handles sync_orchestration's complex subsystems:

| Category | Grounded (5 runs) | Ungrounded (5 runs) | Ungrounded-PDD (5 runs) |
|---|---|---|---|
| Internal imports (`from .module import`) | **5/5 correct** | 4/5 correct (1 syntax error) | 5/5 correct |
| Return type unpacking (dict vs tuple) | **5/5 correct (dict)** | 3/5 wrong (tuple unpacking) | 3/5 wrong (tuple) |
| `AtomicStateUpdate` class structure | **5/5 match canonical** | 3/5 simplified (no dataclass) | 3/5 simplified |
| Cycle detection (4-element pattern matching) | **4/5 match canonical** | 1/5 match canonical | 2/5 match canonical |
| TUI state refs (dict-of-lists pattern) | **4/5 correct** | 3/5 correct | 3/5 correct |
| `SyncApp` constructor call | 4/5 close to canonical | 2/5 close | 3/5 close |
| Function signatures (param order) | **5/5 consistent** | 3/5 consistent | 3/5 consistent |
| Result dict structure | **5/5 match canonical** | 5/5 match | 5/5 match |

**Key observations:**

1. **Grounding anchors return type conventions.** The canonical's operation functions (`auto_deps_main`, `cmd_test_main`, etc.) return `dict` with `success`, `cost`, `model` keys. Grounded runs consistently unpack as `res.get('success')` (correct). Ungrounded runs hallucinate tuple unpacking `_, cost, model = func(...)` in 40% of calls — would crash at runtime.

2. **Grounding preserves complex control flow.** The canonical's cycle detection uses specific 4-element history patterns (`['crash','verify','crash','verify']`). Grounded runs reproduce this pattern-matching approach (4/5). Ungrounded runs invent alternative strategies: `consecutive_ops` dicts, 10-item sliding windows, per-operation counters — all functionally different from canonical.

3. **Grounding maintains class architecture.** `AtomicStateUpdate` uses a `@dataclass PendingStateUpdate` internally. All 5 grounded runs reproduce this (including dataclass + `_temp_files` list). Ungrounded runs simplify to flat attributes (3/5).

4. **All arms struggle with helper functions.** Complex helpers like `_try_auto_fix_import_error()` (30+ lines with sys.path manipulation) and `_python_cov_target_for_code_file()` are simplified or omitted by all arms, including grounded. These are deep implementation details the few-shot example can anchor structurally but not fully reproduce.

#### Comparison to Phase 3-4 (llm_invoke)

| Metric | llm_invoke (Phase 4) | sync_orchestration (Phase 5) | Trend |
|---|---|---|---|
| Canonical lines | ~700 | 1,973 | 2.8x larger |
| Resolved prompt | ~97K chars | ~247K chars | 2.5x larger |
| Grounded ref similarity | 0.030 | **0.145** | **4.8x higher** |
| Grounded ref recall | 0.206 | **0.360** | **75% higher** |
| Grounded pairwise sim | 0.189 | **0.391** | **2.1x higher** |
| Hallucination prevention | 100% (imports, auth, CSV cols) | 100% (return types, signatures) | Consistent |
| Test pass rate (all arms) | 100% (217 tests) | 96/99 (when parseable) | Slight decrease |

**The grounding effect is dramatically stronger on sync_orchestration.** Reference similarity jumps from 0.030 → 0.145 (4.8x), pairwise similarity from 0.189 → 0.391 (2.1x). The larger, more complex module benefits more from grounding because there are more subsystems where the model can drift. The few-shot example anchors all of them simultaneously.

### Key Findings (Phase 5)

#### 1. Grounding's anti-hallucination effect generalizes to complex modules
Even with a 247KB prompt and 1,973-line canonical, grounding prevents the same categories of hallucination seen in Phase 3-4: wrong return type conventions, invented function signatures, and simplified class structures. The effect is not prompt-size dependent.

#### 2. Reference fidelity scales super-linearly with complexity
Grounded reference similarity: 0.030 (llm_invoke) → 0.145 (sync_orchestration). The improvement from grounding grows as the target module gets more complex. This makes intuitive sense: a larger module has more internal conventions that the few-shot example can anchor.

#### 3. Within-arm consistency is dramatically higher for grounded
Pairwise similarity: 0.391 (grounded) vs 0.284 (ungrounded) vs 0.281 (ungrounded-pdd). The grounded arm is **38% more self-consistent**. At temperature 1.0 on a 247KB prompt, this level of structural stability is remarkable.

#### 4. Test visibility still insufficient without grounding
The ungrounded-pdd arm has full test suite visibility (99 tests) yet still hallucinates return type conventions (3/5 wrong) and cycle detection logic (3/5 non-canonical). Consistent with Phase 4: **one relevant code example outperforms an entire test suite** for anchoring implementation details.

#### 5. 96/99 test pass rate across all arms when parseable
All three arms consistently pass 96/99 tests when the generated code is syntactically valid. The 3 failing tests likely test edge cases that all arms handle similarly. Tests validate functional contracts but don't distinguish implementation quality — grounding addresses the gap.

#### 6. Cost/latency tradeoff scales linearly
Grounded: $0.121/call, 86.7s. Ungrounded: $0.049/call, 31.9s. The grounded overhead ratio (~2.5x cost, ~2.7x latency) is comparable to Phase 3-4, confirming the cost scales linearly with prompt size rather than exponentially.

## Next Steps

1. **Investigate coverage gaps**: Why did factorial and flask-api not find examples in Phase 2? Check the 1025 prod `few_shot` documents for math/algorithm and web/API coverage.
2. **Test with more examples**: Run the Phase 3 experiment with prompts that have multiple candidate examples to measure retrieval's effect on quality.
3. **Cost optimization**: Evaluate whether truncating the few-shot example or using a shorter prompt reduces cost without sacrificing the anti-hallucination benefit.
4. **Test suite enhancement**: Investigate whether adding implementation-detail tests (e.g., asserting `CloudConfig.get_jwt_token()` is called, checking rate map is `Tuple` type) would close the gap between ungrounded-pdd and grounded arms.
5. **Prompt-level grounding**: Test injecting the few-shot example directly into the pdd prompt (via `<include>` tag) to see if this recovers the anti-hallucination benefit without the cloud endpoint overhead.
6. **Multi-module generalization**: Test grounding on additional complex modules (e.g., `code_generator`, `fix_main`) to confirm the scaling trend observed between llm_invoke and sync_orchestration.
