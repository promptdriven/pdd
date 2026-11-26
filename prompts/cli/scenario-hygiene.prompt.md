# Scenario size hygiene

Own `src/core/lint/scenario-hygiene.mjs`. Evaluate parsed PDD scenario documents offline against configurable step, serialized state byte, and lower-bound call-budget limits so oversized scenarios surface as non-blocking `scenario-oversized` advisories recommending focused companion files (`tests/<story>.<focus>.json`). Run purely in memory with zero AI calls, zero network calls, and zero file writes.

## Domain decisions

- **Evidence-calibrated defaults:** Default `DEFAULT_SCENARIO_MAX_STEPS` is `15` (matching `stories.md` cap `15` steps; live hosted-interpreter scaling confirmed 10–15 sequential mutating steps pass cleanly without state-copy drift) and `DEFAULT_SCENARIO_MAX_WORLD_BYTES` is `16384` bytes (16 KiB across serialized `initial_world` and `seeds`).
- **Non-blocking default:** `scenario-oversized` always emits `defaultSeverity: 'warn'` so offline lint exits `0` unless a repository explicitly sets `"rules": { "scenario-oversized": "error" }` in `pdd.json` (or `"off"` to suppress).
- **Zero-false-positive call lower bound:** Never multiply declared `simulation` port totals by step count (a scenario's `simulation` map may list ports unused on most steps). Instead, compute `default_call_cap` using the exact per-request cap rule and compare against a strict lower bound `min_estimated_calls` derived only from steps and each step's own positive `calls` checks or `simulation_overrides`.
- **Companion path guidance:** Given scenario path `dir/stem.json`, derive `<story>` as the prefix before the first `.` in `stem` (or `stem` when no `.` exists) and suggest `dir/<story>.<focus>.json` (defaulting to `tests/<story>.<focus>.json`).

| Metric | Formula | Default limit | Reason string when exceeded |
| --- | --- | --- | --- |
| `steps` | `doc.steps.length` | `15` (`maxSteps`) | `<steps> scenario steps (limit: <maxSteps>)` |
| `state_bytes` | UTF-8 byte length of compact JSON `initial_world` (when present) + `seeds` (when present) | `16384` (`maxWorldBytes`) | `<state_bytes> serialized state bytes (limit: <maxWorldBytes>)` |
| `min_estimated_calls` | Sum across steps of `1 + positiveCallsChecks(step) + overrideCount(step)` | `default_call_cap` | `minimum <min_estimated_calls> estimated calls exceeding default per-request cap <default_call_cap>` |

## Default per-request call cap (`computeDefaultScenarioCallCap`)

- Let `steps = Array.isArray(doc?.steps) ? doc.steps.length : 0`. When `steps === 0`, return `0`.
- Let `fallback = Math.min(1000, Math.max(18, steps * 12))`.
- When `steps <= 2`, return `fallback`.
- Otherwise, let `hasWorldOrPorts` be `true` when `doc.initial_world` is a non-empty plain object, `doc.simulation` is a non-empty plain object, or any step has non-empty `simulation_overrides`.
- Let `perStep = 4 + (hasWorldOrPorts ? 1 : 0)`. Return `Math.min(fallback, Math.max(24, steps * perStep + 6))`.

## Positive calls check counting

For each step in `doc.steps`:
- Count `1` base model call for the step.
- Inspect `step.checks` (array of check objects/tuples, or plain-object criterion map whose values are a single tuple or array of tuples/objects): count each check whose target is `"calls"` and whose operator is `"equals"`, `"="`, `"=="`, `"count"`, `"at_least"`, `">="`, `"gte"`, `"gt"`, or `">"` with a finite numeric value `> 0` (or `>= 0` for strict `"gt"` / `">"`).
- Count each entry in `step.simulation_overrides` (array length or plain-object key count).

## Public contract

- `DEFAULT_SCENARIO_MAX_STEPS = 15`, `DEFAULT_SCENARIO_MAX_WORLD_BYTES = 16384`.
- `computeDefaultScenarioCallCap(doc)`: pure. Return the integer default per-request call cap as above.
- `evaluateScenarioHygiene(doc, { path = 'tests/story.json', maxSteps = 15, maxWorldBytes = 16384 } = {})`: pure, never mutates `doc`.
  - When `doc` is not a plain object or `!Array.isArray(doc.steps)` or `Array.isArray(doc.cases)`, return `{ oversized: false, metrics: { steps: 0, state_bytes: 0, min_estimated_calls: 0, default_call_cap: 0 }, reasons: [], finding: null }`.
  - Use integer `maxSteps` (`>= 1`, fallback `15`) and `maxWorldBytes` (`>= 1`, fallback `16384`).
  - Collect exceeded reasons in table order (`steps`, `state_bytes`, `min_estimated_calls`).
  - When `reasons` is empty, return `{ oversized: false, metrics, reasons: [], finding: null }`.
  - When `reasons` is non-empty, return `{ oversized: true, metrics, reasons, finding }` where `finding` is `{ filePath: path, line: 1, order: 12, code: 'scenario-oversized', category: 'scenario hygiene', defaultSeverity: 'warn', detail, fix, rerun: 'pdd lint' }`, with `detail` naming `path`, joined `reasons`, and `default per-request cap: <default_call_cap> calls`, and `fix` advising splitting into focused companion scenarios (`<companionPath>`) or adjusting `"lint.scenario"` in `pdd.json`.
- `collectScenarioHygieneFindings({ realRoot, scenarioPaths = [], readFile, scenarioConfig = {} } = {})`: read candidate scenario JSON files safely (skipping unreadable, non-JSON, native-cases, and fixture files), evaluate each with `evaluateScenarioHygiene`, and return the array of non-null `finding` objects.

## Dependencies

None.
