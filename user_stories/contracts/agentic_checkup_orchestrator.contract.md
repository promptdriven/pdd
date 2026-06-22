<!-- pdd-story-contract derived-from-story="../story__agentic_checkup_orchestrator.md" story-hash="4cf2d777d1d982f7" issue-ref="https://github.com/promptdriven/pdd/issues/1709" -->

# Contract: feat(checkup): persist per-step telemetry (status + cost + model + stable id) in workflow state for pdd_cloud durable runs

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__agentic_checkup_orchestrator.md`), not this contract.

## Covers
- AC1: A completed `pdd checkup` run writes a `step_telemetry` entry for every reached step, each with a stable `step_id`, `status`, `cost_usd`, and `model`.
- AC2: `sum(entry.cost_usd)` reconciles with the persisted `total_cost` (± rounding).
- AC3: Skipped steps (e.g. `--no-fix`) are recorded with `status: "skipped"` and `cost_usd: 0`.
- AC4: On resume, telemetry for already-completed steps is preserved (not duplicated or zeroed).
- AC5: No change to existing keys; a state file without `step_telemetry` still loads and resumes.
- R1: Each telemetry entry uses a stable string `step_id` that does not depend on internal `STEP_ORDER` float numbering.
- R2: The existing `total_cost`, `step_outputs`, `last_completed_step`, and `pr_head_sha` keys are untouched.

## Context
A `pdd checkup` run has been invoked against a PR (with or without an associated issue). The orchestrator executes a sequence of internal steps (research, fix, validation, verdict, PR post, etc.). Each step already produces a cost, model, success flag, and description at `_handle_step_result`. The workflow state is persisted to `.pdd/checkup-state/checkup_state_<issue>.json` and may be harvested by pdd_cloud for durable, resumable runs. The state file may already exist from a prior partial run (resume scenario).

## Acceptance Criteria
1. Given a fresh `pdd checkup` run that completes all steps, when the run finishes, then the persisted state file contains a `step_telemetry` list with one entry per reached step, each entry having a stable string `step_id`, a `status` of `"completed"`, a `cost_usd` number, and a `model` string.
2. Given a `pdd checkup` run where some steps are skipped (e.g. `--no-fix`), when the run finishes, then the skipped steps appear in `step_telemetry` with `status: "skipped"` and `cost_usd: 0`.
3. Given a completed run with `step_telemetry` present, when the `cost_usd` values across all entries are summed, then the sum equals the persisted `total_cost` within a rounding tolerance of ±0.01 USD.
4. Given a state file from a prior partial run that already contains `step_telemetry` entries for steps 1–3, when the run resumes and completes steps 4–8, then the final state file contains exactly one entry per step (no duplicates for steps 1–3) and the pre-existing entries retain their original `started_at`, `completed_at`, `cost_usd`, and `model` values.
5. Given a state file that lacks a `step_telemetry` key (legacy format), when `pdd checkup` loads and resumes from it, then the run proceeds without error and the final state file includes the new `step_telemetry` key alongside all original keys.

## Oracle
These details matter for pass/fail:
- The state file contains a top-level key named `step_telemetry` whose value is a JSON array.
- Every element in `step_telemetry` has the keys `step_id` (string), `status` (one of `"completed"`, `"failed"`, `"skipped"`), `cost_usd` (number), and `model` (string).
- The `step_id` values are stable strings (e.g. `"fix"`, `"verdict"`, `"validate_1"`) — not floats or strings derived from `STEP_ORDER` numbers like `"5"` or `"6_1"`.
- `sum(entry.cost_usd for entry in step_telemetry)` is within 0.01 of the persisted `total_cost`.
- The existing keys `total_cost`, `step_outputs`, `last_completed_step`, `pr_head_sha`, `model_used`, `mode`, `pr_*`, and `step_comments` are present and unchanged in structure.
- On resume, the number of entries in `step_telemetry` equals the number of distinct steps that have been reached (no duplicate `step_id` values).

## Non-Oracle
These details should not matter:
- The exact string values of `step_id` (e.g. `"fix"` vs `"apply_fix"`) — only that they are stable strings, not derived from internal float step numbers.
- The presence or absence of optional fields like `iteration`, `started_at`, `completed_at`, `name`, or `internal_step` — these are additive metadata and their omission does not break the contract.
- The order of entries in the `step_telemetry` array.
- The internal `STEP_ORDER` list values or `TOTAL_STEPS` constant.
- Whether the final JSON report (Step 7 output) also includes `step_telemetry` — that is optional per the issue.
- The exact model name string (e.g. `"claude-opus-4-8"` vs any other model identifier).

## Negative Cases
- A completed run produces a state file with `step_telemetry` missing entirely.
- A step that ran and incurred cost is recorded with `cost_usd: 0` or `status: "skipped"`.
- A skipped step is recorded with `status: "completed"` or a non-zero `cost_usd`.
- On resume, previously completed steps are duplicated in `step_telemetry` (two entries with the same `step_id`).
- On resume, previously recorded `cost_usd` or `model` values are overwritten with `null` or zero.
- The `step_id` values are floats or strings that encode `STEP_ORDER` positions (e.g. `"5"`, `"6.1"`), coupling consumers to internal numbering.
- Adding `step_telemetry` removes or renames any existing top-level key in the state file.
- A legacy state file (no `step_telemetry`) causes a load error or prevents the run from proceeding.

## Non-Goals
- The cloud-side harvesting, mapping, or durable-run wiring — this contract only covers what the CLI persists to disk.
- Changes to `last_completed_step` or `step_outputs` resume mechanics.
- Changes to `pr_head_sha` computation or checkpoint invalidation logic.
- Surfacing `step_telemetry` in the final machine-readable JSON report (optional per the issue, not required by the Story).

## Candidate Prompts
- `agentic_checkup_orchestrator_python.prompt` — primary target; owns `_handle_step_result`, `_build_state`, and `_save_state` (primary)
- `agentic_checkup_python.prompt` — entry point that invokes the orchestrator; may need to pass through or not interfere with telemetry accumulation (related)
- `agentic_common_python.prompt` — shared agentic CLI execution with state persistence; may interact with how state is saved or restored (possible)

## Notes
- The issue explicitly states the exact `step_id` names are negotiable; the contract enforces only that they are stable strings decoupled from `STEP_ORDER` floats.
- The `±0.01` rounding tolerance for cost reconciliation accounts for floating-point summation across multiple LLM API calls.
- The issue confirms that `_handle_step_result` already receives `cost`, `model`, `success`, and `description` per step — the contract requires that this data is now persisted per-step rather than only aggregated into `total_cost`.
- Cross-reference: pdd_cloud consumes this data in `promptdriven/pdd_cloud#2297` under epic `promptdriven/pdd_cloud#2294`.
