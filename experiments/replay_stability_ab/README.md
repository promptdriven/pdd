# Replay Stability A/B (PDD vs Agentic-Only)

This example is a small, repeatable experiment you can run by yourself to compare:

1. `PDD` workflow (prompt-first, regenerate, test)
2. `Agentic-Only` workflow (direct code patching)

The goal is to measure replay stability, drift incidents, and effort/cost for the same change request.

Current recorded outcomes are tracked in:
`EXPERIMENT_LOG.md`

## What This Includes

1. `baseline/`:
   a small Python module, prompt, and failing acceptance tests for a change request.
2. `TASK_SPEC.md`:
   exact requirements both arms must implement.
3. `scripts/create_run_workspace.sh`:
   creates a clean workspace for each run.
4. `scripts/evaluate_run.py`:
   runs tests, captures metrics, and appends a row to `results/run_results.csv`.
5. `scripts/summarize_results.py`:
   prints per-arm metrics and a simple win signal.

The package provides two task profiles:

1. `TASK_SPEC.md` (easy starter)
2. `TASK_SPEC_MEDIUM.md` (recommended; harder and less likely to be solved by trivial edits)

## Quick Start

From repo root:

```bash
cd experiments/replay_stability_ab
make init
```

Create a clean workspace for run 1 in each arm:

```bash
make new-agentic RUN_ID=01
make new-pdd RUN_ID=01
```

Workspaces are created at:

- `runs/agentic/run_01/workspace`
- `runs/pdd/run_01/workspace`

Each workspace includes a local `.pddrc` so `pdd sync` resolves `prompts/`, `src/`, `tests/`, and `examples/` inside that workspace (not the repo root).

## Run Procedure

### Agentic-Only Arm

1. Open `runs/agentic/run_01/workspace`.
2. Implement `TASK_SPEC.md` by directly editing code with your agentic CLI workflow.
3. Do not use a prompt-first regeneration loop.
4. Record results:

```bash
python3 scripts/evaluate_run.py \
  --arm agentic \
  --run-id 01 \
  --workspace runs/agentic/run_01/workspace \
  --active-minutes 12.5 \
  --api-cost-usd 0.40
```

### PDD Arm

1. Open `runs/pdd/run_01/workspace`.
2. Update `prompts/user_id_parser_python.prompt` first.
3. Regenerate with real sync flow (recommended):

```bash
pdd --force sync user_id_parser
```

4. Then fix and re-test as needed.
4. Record results:

```bash
python3 scripts/evaluate_run.py \
  --arm pdd \
  --run-id 01 \
  --workspace runs/pdd/run_01/workspace \
  --active-minutes 10.0 \
  --api-cost-usd 0.35
```

Repeat for runs `02` to `05` for each arm.

## Model Reporting (Required)

For each recorded run, include the model used in `--notes`.

Use this format:
1. Agentic arm: `agentic_cli=<tool>;model=<model-id>`
2. PDD arm: `pdd_model=<model-id>;strength=<value>`

If no model was used (manual patch), record:
1. `agentic_cli=manual;model=N/A`

## Recommended Medium Task Run

Use the medium acceptance tests for stronger signal:

```bash
python3 scripts/evaluate_run.py \
  --arm pdd \
  --run-id 02 \
  --workspace runs/pdd/run_02/workspace \
  --active-minutes 12.0 \
  --api-cost-usd 0.42 \
  --test-command "pytest -q tests/test_task_acceptance_medium.py"
```

Use `TASK_SPEC_MEDIUM.md` as the change request in both arms.

## Summarize

```bash
make summarize
# Optional: medium-only summary
python3 scripts/summarize_results.py --results results/run_results.csv --test-command-contains test_task_acceptance_medium.py
```

This prints:

1. pass rate by arm
2. average active minutes
3. average API cost
4. drift incident rate
5. basic win signal

## Notes

1. `drift_incident` is computed automatically as:
   tests pass but source-of-truth prompt file did not change.
2. Source-of-truth file defaults to:
   `prompts/user_id_parser_python.prompt`
3. Acceptance command defaults to:
   `pytest -q tests/test_task_acceptance.py`
