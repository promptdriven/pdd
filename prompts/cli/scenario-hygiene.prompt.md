# Scenario size hygiene

Own `src/core/lint/scenario-hygiene.mjs`. Evaluate parsed PDD scenario documents offline against configurable step and serialized state byte limits while tracking declared simulated ports as factual structural context, so oversized scenarios surface as non-blocking `scenario-oversized` advisories recommending focused companion files (`tests/<story>.<focus>.json`). Run purely in memory with zero AI calls, zero network calls, and zero file writes.

## Domain decisions

- **Evidence-calibrated defaults:** Default `DEFAULT_SCENARIO_MAX_STEPS` is `15` (matching `stories.md` cap `15` steps; live hosted-interpreter scaling confirmed 10–15 sequential mutating steps pass cleanly without state-copy drift) and `DEFAULT_SCENARIO_MAX_WORLD_BYTES` is `16384` bytes (16 KiB across serialized `initial_world` and `seeds`).
- **Non-blocking default:** `scenario-oversized` always emits `defaultSeverity: 'warn'` so offline lint exits `0` unless a repository explicitly sets `"rules": { "scenario-oversized": "error" }` in `pdd.json` (or `"off"` to suppress).
- **No client-side call-cap guesswork:** `pdd` does not impose a client-side `max_calls` shrink-clamp (`prompt-runtime` owns execution caps). Never compare scenarios against a guessed client call cap and never multiply declared `simulation` port totals by step count (a scenario's `simulation` map may list ports unused on most steps). Count distinct keys in plain-object `doc.simulation` as `simulated_ports` for informational context only; when an oversized scenario declares simulated ports, include `(<simulated_ports> simulated port[s])` in the finding detail.
- **Companion path guidance:** Given scenario path `dir/stem.json`, derive `<story>` as the prefix before the first `.` in `stem` (or `stem` when no `.` exists) and suggest `dir/<story>.<focus>.json` (defaulting to `tests/<story>.<focus>.json`).

| Metric | Formula | Default limit | Reason string when exceeded |
| --- | --- | --- | --- |
| `steps` | `doc.steps.length` | `15` (`maxSteps`) | `<steps> scenario steps (limit: <maxSteps>)` |
| `state_bytes` | UTF-8 byte length of compact JSON `initial_world` (when present) + `seeds` (when present) | `16384` (`maxWorldBytes`) | `<state_bytes> serialized state bytes (limit: <maxWorldBytes>)` |
| `simulated_ports` | Key count of plain-object `doc.simulation` (`0` otherwise) | Informational only (no limit) | Never triggers `scenario-oversized` on its own; shown as `(<simulated_ports> simulated port[s])` when non-zero on an oversized finding |

## Public contract

- `DEFAULT_SCENARIO_MAX_STEPS = 15`, `DEFAULT_SCENARIO_MAX_WORLD_BYTES = 16384`.
- `evaluateScenarioHygiene(doc, { path = 'tests/story.json', maxSteps = 15, maxWorldBytes = 16384 } = {})`: pure, never mutates `doc`.
  - When `doc` is not a plain object, `!Array.isArray(doc.steps)`, `Array.isArray(doc.cases)`, or `String(doc.schema_version ?? '').startsWith('pdd.native-cases.')`, return `{ oversized: false, metrics: { steps: 0, state_bytes: 0, simulated_ports: 0 }, reasons: [], finding: null }`.
  - Use integer `maxSteps` (`>= 1`, fallback `15`) and `maxWorldBytes` (`>= 1`, fallback `16384`).
  - Collect exceeded reasons in table order (`steps`, `state_bytes`).
  - When `reasons` is empty, return `{ oversized: false, metrics, reasons: [], finding: null }`.
  - When `reasons` is non-empty, return `{ oversized: true, metrics, reasons, finding }` where `finding` is `{ filePath: path, line: 1, order: 12, code: 'scenario-oversized', category: 'scenario hygiene', defaultSeverity: 'warn', detail, fix, rerun: 'pdd lint' }`, with `detail` formatted as `Scenario "<path>" has <reasons joined by " and "><portNote>.` (where `<portNote>` is `""` when `simulated_ports === 0`, `" (1 simulated port)"` when `simulated_ports === 1`, and `" (<simulated_ports> simulated ports)"` when `simulated_ports > 1`), and `fix` set to `Split into focused companion scenarios (<companionPath>) or adjust "lint.scenario" in pdd.json`.
- `collectScenarioHygieneFindings({ realRoot, scenarioPaths = [], readFile, scenarioConfig = {} } = {})`: deduplicate and sort candidate scenario paths (skipping fixtures, tooling configs, `cases.json` / `*-cases.json`, unreadable, non-JSON, and native-cases files), evaluate each with `evaluateScenarioHygiene` using `scenarioConfig` overrides (`{ maxSteps, maxWorldBytes }`), and return the array of non-null `finding` objects.

## Dependencies

None.
