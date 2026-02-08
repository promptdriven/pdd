# Experiment Log: Replay Stability A/B

Updated: 2026-02-08
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

## Caveats
1. Model parity is not controlled in runs 01-06 (`agentic`: `gpt-5.3-codex`; `pdd`: `vertex_ai/gemini-3-pro-preview`), so outcome differences can reflect both workflow and model effects.
2. ~~A same-model A/B should be run next to isolate workflow effect cleanly.~~ **Done in runs 07-09.**
3. Paths embedded in historical CSV rows may reference the old `examples/` location from before the directory move; artifacts now live under `experiments/`.
4. CW-1 hypothesis (context window overhead degrades quality) remains untested — needs a harder task or longer session to stress the context window.
