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

## Model Provenance

| Arm | How It Was Executed | Model Used |
|---|---|---|
| agentic | Direct code patching in workspace via Codex CLI | `gpt-5.3-codex` (max effort) |
| pdd | `pdd sync` / prompt-first workflow | `vertex_ai/gemini-3-pro-preview` for real sync runs (`run_02`-`run_06`) |
| pdd (manual) | Prompt updated first, then code edited manually | N/A for `run_01` (no `pdd sync` model invocation) |

## Rollup Metrics

### Easy Profile
Runs included: 3 total (`agentic`: 1, `pdd`: 2)

| Arm | Runs | Pass Rate | Avg Active Minutes | Avg API Cost | Drift Rate |
|---|---:|---:|---:|---:|---:|
| agentic | 1 | 100.00% | 6.00 | $0.0000 | 100.00% |
| pdd | 2 | 50.00% | 4.75 | $0.0095 | 0.00% |

### Medium Profile
Runs included: 8 total (`agentic`: 4, `pdd`: 4)

| Arm | Runs | Pass Rate | Avg Active Minutes | Avg API Cost | Drift Rate |
|---|---:|---:|---:|---:|---:|
| agentic | 4 | 100.00% | 8.00 | $0.0000 | 100.00% |
| pdd | 4 | 100.00% | 3.12 | $0.0651 | 0.00% |

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

## PDD Model Trace
From sync logs in:
`experiments/replay_stability_ab/runs/pdd/run_*/workspace/.pdd/meta/user_id_parser_python_sync.log`

Observed model by run:
1. `run_02`: `vertex_ai/gemini-3-pro-preview`
2. `run_03`: `vertex_ai/gemini-3-pro-preview`
3. `run_04`: `vertex_ai/gemini-3-pro-preview`
4. `run_05`: `vertex_ai/gemini-3-pro-preview`
5. `run_06`: `vertex_ai/gemini-3-pro-preview` (with explicit `--strength 1.0`)

## Agentic Model Trace
Execution context provided by operator:
1. `run_01`: Codex CLI `gpt-5.3-codex` (max effort)
2. `run_03`: Codex CLI `gpt-5.3-codex` (max effort)
3. `run_04`: Codex CLI `gpt-5.3-codex` (max effort)
4. `run_05`: Codex CLI `gpt-5.3-codex` (max effort)
5. `run_06`: Codex CLI `gpt-5.3-codex` (max effort)

## Key Observations
1. Medium profile currently shows equal acceptance pass rate (100% vs 100%).
2. Medium profile shows lower recorded drift incidents in PDD runs (0% vs 100%).
3. Medium profile shows lower recorded active minutes in PDD runs.
4. PDD runs incur API cost due to sync orchestration and LLM calls.
5. Easy profile contains one failed real `pdd sync` run (`run_02`), highlighting why independent acceptance tests are necessary.

## Caveats
1. Model parity is not controlled in current runs (`agentic`: `gpt-5.3-codex`; `pdd`: `vertex_ai/gemini-3-pro-preview`), so outcome differences can reflect both workflow and model effects.
2. A same-model A/B should be run next to isolate workflow effect cleanly.
3. Paths embedded in historical CSV rows may reference the old `examples/` location from before the directory move; artifacts now live under `experiments/`.
