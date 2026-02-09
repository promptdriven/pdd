# Experiment Log: Replay Stability A/B

Updated: 2026-02-09
Experiment directory: `experiments/replay_stability_ab/`
Raw results CSV: `experiments/replay_stability_ab/results/run_results.csv`

## Scope
This log captures recorded runs comparing:
1. `agentic` arm (direct code patch workflow)
2. `pdd` arm (prompt-first workflow, including real `pdd sync` runs)

Task profiles used:
1. Easy: `tests/test_task_acceptance.py`
2. Medium: `tests/test_task_acceptance_medium.py`

## Explicit Model Summary
1. PDD model used in real sync runs: `vertex_ai/gemini-3-pro-preview` (`run_02` through `run_06`).
2. Agentic model used in recorded runs: `gpt-5.3-codex` via Codex CLI with max effort (`run_01`, `run_03`, `run_04`, `run_05`, `run_06`).
3. **Model-parity runs (07-09)**: Both arms use `anthropic/claude-opus-4-6`. PDD via `--local` flag + `.pdd/llm_model.csv` pin. Agentic via Claude Code CLI.

## Model Provenance

| Arm | How It Was Executed | Model Used |
|---|---|---|
| agentic | Direct code patching in workspace via Codex CLI | `gpt-5.3-codex` (max effort) |
| agentic (model-parity) | Direct code patching via Claude Code CLI | `anthropic/claude-opus-4-6` (`run_07`-`run_09`) |
| pdd | `pdd sync` / prompt-first workflow | `vertex_ai/gemini-3-pro-preview` for real sync runs (`run_02`-`run_06`) |
| pdd (model-parity) | `pdd --force --local sync` with CSV model pin | `anthropic/claude-opus-4-6` (`run_07`-`run_09`) |
| pdd (manual) | Prompt updated first, then code edited manually | N/A for `run_01` (no `pdd sync` model invocation) |

## Rollup Metrics

### Easy Profile
Runs included: 3 total (`agentic`: 1, `pdd`: 2)

| Arm | Runs | Pass Rate | Avg Active Minutes | Avg API Cost | Drift Rate |
|---|---:|---:|---:|---:|---:|
| agentic | 1 | 100.00% | 6.00 | $0.0000 | 100.00% |
| pdd | 2 | 50.00% | 4.75 | $0.0095 | 0.00% |

### Medium Profile (Mixed Models: runs 03-06)
Runs included: 8 total (`agentic`: 4, `pdd`: 4)

| Arm | Runs | Pass Rate | Avg Active Minutes | Avg API Cost | Drift Rate |
|---|---:|---:|---:|---:|---:|
| agentic | 4 | 100.00% | 8.00 | $0.0000 | 100.00% |
| pdd | 4 | 100.00% | 3.12 | $0.0651 | 0.00% |

### Medium Profile — Model Parity (runs 07-09, both = `anthropic/claude-opus-4-6`)
Runs included: 6 total (`agentic`: 3, `pdd`: 3)

| Arm | Runs | Pass Rate | Avg Active Minutes | Avg API Cost | Drift Rate |
|---|---:|---:|---:|---:|---:|
| agentic | 3 | 100.00% | 0.38 | ~$0.03 | 0.00% |
| pdd | 3 | 100.00% | 9.61 | $1.27 | 0.00% |

Note: PDD drift column shows 0% because the minor try/except wrapper is not
counted as a functional drift (all acceptance tests pass, behavior matches spec).
Agentic drift also 0% — model parity eliminated the drift seen in runs 03-06.

## Per-Run Ledger

| Run | Arm | Profile | Pass | Active Min | API Cost | Drift | Source-of-Truth Updated | Model Used | Notes |
|---|---|---|---:|---:|---:|---:|---:|---|---|
| 01 | agentic | easy | 1 | 6.000 | 0.0000 | 1 | 0 | `gpt-5.3-codex` (Codex CLI, max effort) | Direct code patch only; prompt unchanged |
| 01 | pdd | easy | 1 | 7.000 | 0.0000 | 0 | 1 | N/A (manual prompt+code edit) | Prompt updated first; code regenerated manually |
| 02 | pdd | easy | 0 | 2.500 | 0.0189 | 0 | 1 | `vertex_ai/gemini-3-pro-preview` | Real `pdd --force sync user_id_parser` |
| 03 | agentic | medium | 1 | 8.000 | 0.0000 | 1 | 0 | `gpt-5.3-codex` (Codex CLI, max effort) | Medium task direct code patch |
| 03 | pdd | medium | 1 | 2.000 | 0.0135 | 0 | 1 | `vertex_ai/gemini-3-pro-preview` | Real `pdd --force sync` |
| 04 | agentic | medium | 1 | 8.000 | 0.0000 | 1 | 0 | `gpt-5.3-codex` (Codex CLI, max effort) | Medium task direct code patch |
| 05 | agentic | medium | 1 | 8.000 | 0.0000 | 1 | 0 | `gpt-5.3-codex` (Codex CLI, max effort) | Medium task direct code patch |
| 04 | pdd | medium | 1 | 5.500 | 0.1829 | 0 | 1 | `vertex_ai/gemini-3-pro-preview` | Real `pdd --force sync`; model pin attempt |
| 05 | pdd | medium | 1 | 3.500 | 0.0453 | 0 | 1 | `vertex_ai/gemini-3-pro-preview` | Real `pdd --force sync`; model pin attempt |
| 06 | agentic | medium | 1 | 8.000 | 0.0000 | 1 | 0 | `gpt-5.3-codex` (Codex CLI, max effort) | Medium task direct code patch |
| 06 | pdd | medium | 1 | 1.500 | 0.0187 | 0 | 1 | `vertex_ai/gemini-3-pro-preview` | Real `pdd --force --strength 1.0 sync` |
| 07 | pdd | medium | 1 | 20.740 | 3.4313 | 0 | 1 | `anthropic/claude-opus-4-6` | **MODEL PARITY** `pdd --force --local sync`; minor try/except drift |
| 08 | pdd | medium | 1 | 4.380 | 0.2064 | 0 | 1 | `anthropic/claude-opus-4-6` | **MODEL PARITY** `pdd --force --local sync`; minor try/except drift |
| 09 | pdd | medium | 1 | 3.700 | 0.1798 | 0 | 1 | `anthropic/claude-opus-4-6` | **MODEL PARITY** `pdd --force --local sync`; identical to run_08 (cache hit) |
| 07 | agentic | medium | 1 | 0.420 | ~0.03 | 0 | 0 | `anthropic/claude-opus-4-6` | **MODEL PARITY** Claude Code direct patch; no drift |
| 08 | agentic | medium | 1 | 0.420 | ~0.03 | 0 | 0 | `anthropic/claude-opus-4-6` | **MODEL PARITY** Claude Code direct patch; no drift |
| 09 | agentic | medium | 1 | 0.300 | ~0.03 | 0 | 0 | `anthropic/claude-opus-4-6` | **MODEL PARITY** Claude Code direct patch; no drift |

## PDD Model Trace
From sync logs in:
`experiments/replay_stability_ab/runs/pdd/run_*/workspace/.pdd/meta/user_id_parser_python_sync.log`

Observed model by run:
1. `run_02`: `vertex_ai/gemini-3-pro-preview`
2. `run_03`: `vertex_ai/gemini-3-pro-preview`
3. `run_04`: `vertex_ai/gemini-3-pro-preview`
4. `run_05`: `vertex_ai/gemini-3-pro-preview`
5. `run_06`: `vertex_ai/gemini-3-pro-preview` (with explicit `--strength 1.0`)
6. `run_07`: `anthropic/claude-opus-4-6` (via `--local` + `.pdd/llm_model.csv` pin)
7. `run_08`: `anthropic/claude-opus-4-6` (via `--local` + `.pdd/llm_model.csv` pin)
8. `run_09`: `anthropic/claude-opus-4-6` (via `--local` + `.pdd/llm_model.csv` pin)

## Agentic Model Trace
Execution context provided by operator:
1. `run_01`: Codex CLI `gpt-5.3-codex` (max effort)
2. `run_03`: Codex CLI `gpt-5.3-codex` (max effort)
3. `run_04`: Codex CLI `gpt-5.3-codex` (max effort)
4. `run_05`: Codex CLI `gpt-5.3-codex` (max effort)
5. `run_06`: Codex CLI `gpt-5.3-codex` (max effort)
6. `run_07`: Claude Code `anthropic/claude-opus-4-6` (**model-parity**)
7. `run_08`: Claude Code `anthropic/claude-opus-4-6` (**model-parity**)
8. `run_09`: Claude Code `anthropic/claude-opus-4-6` (**model-parity**)

## Key Observations
1. Medium profile currently shows equal acceptance pass rate (100% vs 100%).
2. Medium profile shows lower recorded drift incidents in PDD runs (0% vs 100%).
3. Medium profile shows lower recorded active minutes in PDD runs.
4. PDD runs incur API cost due to sync orchestration and LLM calls.
5. Easy profile contains one failed real `pdd sync` run (`run_02`), highlighting why independent acceptance tests are necessary.

## Model-Parity Observations (runs 07-09)
6. With model parity (both arms = Claude Opus 4.6), pass rate is tied at 100%.
7. Drift is eliminated in the agentic arm (0% vs 100% in runs 03-06), suggesting prior drift was model-specific (gpt-5.3-codex), not workflow-specific.
8. PDD is ~25x slower and ~42x more expensive than agentic for single-shot medium tasks (PDD's verify/test/fix pipeline adds overhead).
9. PDD runs 08 and 09 produced identical code (LLM cache hit), demonstrating deterministic reproducibility.
10. The `--local` flag is required for PDD to honor `.pdd/llm_model.csv`; without it, cloud execution silently selects a different model.
11. The CW-1 context-window advantage (661x overhead ratio) did NOT translate to quality differences at this task complexity (~500 token spec).

## SCR — Sequential Change Resilience (runs 10-15)

### Overview

The SCR experiment tests PDD's strongest untested claim: **drift prevention across sequential changes**. Because PDD regenerates from the cumulative prompt (full spec) each step, it should stay aligned with the spec as requirements evolve. Agentic patching accumulates code without regenerating, potentially introducing dead code, inconsistent patterns, and missed interactions between features.

Both arms use `anthropic/claude-opus-4-6`. Model parity confirmed from runs 07-09.

### Design

- **6 steps** (0-5) applied sequentially to `user_id_parser.py`
- **3 agentic runs** (10, 11, 12): Fresh Claude Code session per step. Receives only the **change request** (delta) + reference to step's test file.
- **3 PDD runs** (13, 14, 15): Operator updates prompt with **cumulative requirements** (full spec), then runs `pdd --force --local sync`.
- **Information asymmetry**: Intentional. Agentic gets deltas; PDD gets full spec. Mirrors real-world usage.
- **Retry parity**: Both arms get up to 3 attempts per step.

**The 5 sequential changes:**

| Step | Change | Drift Risk | Cumulative Tests |
|---:|--------|-----------|---:|
| 0 | Medium baseline (parse_user_id with str/dict input) | — | 4 |
| 1 | Add batch processing (parse_user_ids) | Low | 6 |
| 2 | Add email-based input (email:user@example.com) | Moderate | 8 |
| 3 | Configurable reserved IDs (reserved_ids param) | Moderate | 10 |
| 4 | **BREAKING CHANGE**: Structured result (ParseResult namedtuple) | **HIGH** | 12 |
| 5 | Strict mode (reject consecutive special chars) | Moderate | 14 |

### Results

#### Pass Rate (all runs: 100% across all steps)

| Step | Agentic (3 runs) | PDD (3 runs) |
|---:|---:|---:|
| 0 | 3/3 (100%) | 3/3 (100%) |
| 1 | 3/3 (100%) | 3/3 (100%) |
| 2 | 3/3 (100%) | 3/3 (100%) |
| 3 | 3/3 (100%) | 3/3 (100%) |
| 4 | 3/3 (100%) | 3/3 (100%) |
| 5 | 3/3 (100%) | 3/3 (100%) |

**Both arms achieved 36/36 (100%) across all steps and runs.** No regressions detected. Survival curve: no run in either arm experienced a first failure.

#### Code Metrics (averaged across 3 runs per arm)

| Step | Agentic Lines | PDD Lines | Agentic Complexity | PDD Complexity |
|---:|---:|---:|---:|---:|
| 0 | 43 | 56 | 8.3 | 4.0 |
| 1 | 48 | 57 | 8.3 | 4.0 |
| 2 | 54 | 64 | 13.3 | 5.0 |
| 3 | 56 | 72 | 13.7 | 8.7 |
| 4 | 61 | 79 | 13.7 | 9.0 |
| 5 | 64 | 78 | 14.3 | 9.0 |

**Key observations:**
- PDD produces **~22% more code** (avg 78 vs 64 lines at step 5), contrary to hypothesis.
- Agentic has **higher measured complexity** (14.3 vs 9.0 at step 5 using `radon cc -nc`). However, this metric is skewed: it counts only functions with complexity >= C (11+), and varies by how functions are decomposed.
- Both arms converge to 3 functions at step 5 (parse_user_id, parse_user_ids, _extract).
- PDD code varies more between runs (lines: 76-84 at step 5) vs agentic (60-67).

#### Qualitative Code Review

**Agentic arm (run_10 final code — 57 lines, step 4 preserved):**
- Clean, minimal implementation
- No dead code or vestigial patterns
- Consistent naming conventions throughout
- No exception handling (trusts input shapes)
- Modern Python syntax (type unions with `|`)
- Well-organized: public API → batch → private helper

**PDD arm (runs 13-15 final code):**
- Run 13 (84 lines): Uses explicit `typing` module imports (`Optional`, `List`, `Set`). Comprehensive docstrings. Try/except in parse_user_id.
- Run 14 (75 lines): Modern syntax without typing module. Defensive try/except in both _extract and parse_user_id. Uses `frozenset` for reserved IDs.
- Run 15 (76 lines): Extracts `_CONSECUTIVE_SPECIALS_RE` as module-level constant. Brief docstrings.
- **Variation between runs**: PDD generates different code structure each time despite identical prompts. Import styles, naming conventions, and error handling vary across runs.

**Step 4 handling (ParseResult breaking change):**
- Agentic: Correctly added namedtuple, updated all return paths, added source tracking to _extract. Clean refactor.
- PDD: Regenerated entire file with ParseResult built in from scratch. All three PDD runs handled it cleanly.

### Interpretation

**Primary finding**: The "most likely" outcome materialized — both arms pass all tests, but with code metric differences. However, the direction of some metrics was unexpected:
- PDD produces MORE code, not less (the regeneration includes more boilerplate/defensiveness)
- PDD code varies more between runs than agentic code
- Agentic code shows HIGHER measured complexity, but this reflects function decomposition style rather than true drift

**Drift hypothesis**: Not supported at this task scale. Opus 4.6 is capable enough to maintain coherence across 5 sequential patches without accumulating drift. The breaking change (step 4) — designed to be the strongest test of regeneration vs patching — was handled cleanly by both arms.

**Information asymmetry effect**: Providing agentic with only deltas (not full spec) did NOT cause failures. Opus 4.6 reads existing code thoroughly before patching and maintains consistency.

### Limitations

1. **Single module**: All changes affect one file. Multi-file drift may show different results.
2. **Opus 4.6 is very capable**: Weaker models may drift earlier. Results may not generalize.
3. **Fresh sessions per step**: Real developers often continue sessions across changes. Accumulated context could compound drift.
4. **Run 14 data note**: Steps 0-4 data was reconstructed from workspace artifacts after a data integrity issue (branch switch during background execution). Step 3 line count (69) is estimated from surrounding steps. All pass/fail results are confirmed from task execution logs.
5. **Runs 11-12 workspace files lost**: Due to branch-switch incidents during the experiment, the final source code for agentic runs 11 and 12 was not preserved. CSV metric data was collected during the actual runs and is accurate.

### Cost & Time

| Arm | Runs | Steps | Total Time | Total Cost |
|-----|------|-------|------------|------------|
| Agentic | 3 | 18 | ~12 min | ~$5 |
| PDD | 3 | 18 | ~4.5 hours | ~$30 |
| **Total** | **6** | **36** | **~5 hours** | **~$35** |

PDD remains ~22x slower and ~6x more expensive per step, consistent with runs 07-09.

## Caveats
1. Model parity is not controlled in runs 01-06 (`agentic`: `gpt-5.3-codex`; `pdd`: `vertex_ai/gemini-3-pro-preview`), so outcome differences can reflect both workflow and model effects.
2. ~~A same-model A/B should be run next to isolate workflow effect cleanly.~~ **Done in runs 07-09.**
3. Paths embedded in historical CSV rows may reference the old `examples/` location from before the directory move; artifacts now live under `experiments/`.
4. ~~CW-1 hypothesis (context window overhead degrades quality) remains untested — needs a harder task or longer session to stress the context window.~~ **Tested in SCR (runs 10-15). No quality difference at this task complexity.**
5. SCR experiment results suggest drift prevention is not a differentiator for Opus 4.6 on single-module, 5-step sequential changes. A harder test (multi-file, weaker model, continuous session) is needed to stress this claim.
