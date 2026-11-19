# Short scenario compiler

Own `src/scenario-compile.mjs`. Compile authored PDD Short JSON scenario documents and omitted-`criteria` `prompt-runtime.program-scenario.v1` scenarios deterministically into canonical `prompt-runtime.program-scenario.v1` JSON without network, model, GitHub, Herdr, or automatic filesystem writes, and provide reviewable explicit-criterion content-ID binding for `pdd lint --bind-criteria`.

| Export | Input | Output / Role |
| :--- | :--- | :--- |
| `parseExactScenarioJson` / `stringifyExactScenarioJson` | UTF-8 JSON text or value | `BigInt`-preserving exact integer parse and `JSON.rawJSON` serialization |
| `isShortScenarioDoc` / `needsScenarioCompile` | Parsed scenario object | Detect Short JSON constructs or omitted-`criteria` `program-scenario.v1` documents |
| `compileScenario` / `compileScenarioText` | Scenario object or JSON text + Story context | Canonical `program-scenario.v1` document/text with `ac-sha256-...` criteria or compile refusal |
| `classifyExplicitCriteriaBinding` / `bindScenarioCriteriaText` | Scenario object or JSON text + Story context | Classify explicit IDs (`already-bound`, `legacy-unbound`, `stale-content-id`, `text-mismatch`) and bind matching legacy IDs on disk |

## Exact JSON codec and classification

Preserve exact whole numbers outside IEEE-754 `Number.MAX_SAFE_INTEGER` using `BigInt` during parsing and `JSON.rawJSON` during serialization:

- `parseExactScenarioJson(text)`: parse UTF-8 JSON text, turning unsafe exact integer tokens (`/^-?(?:0|[1-9][0-9]*)$/`) into `BigInt` values.
- `stringifyExactScenarioJson(value, space)`: serialize JSON values while writing `BigInt` leaves via `JSON.rawJSON`.
- `jsonSafeScenario(value)`: convert any `BigInt` leaves to JavaScript `Number` values for callers that store `JSON.parse`-compatible discovery documents.

`V1_SCENARIO_SCHEMA` is `'prompt-runtime.program-scenario.v1'`. `SHORT_SCENARIO_SCHEMA` is `'pdd.scenario.short.v1'`.

`criterionContentId(text, storyPath = '')` computes `'ac-sha256-' + sha256(storyPath + '\0' + text).slice(0, 48)`, matching `@promptdriven/runtime-client`.

`isShortScenarioDoc(doc)` returns `true` only when `doc` is a plain JSON object that uses at least one Short JSON construct:

- `doc.schema_version === SHORT_SCENARIO_SCHEMA`, top-level `seeds`, or top-level singular `entry_path`;
- `Array.isArray(doc.steps)` while omitting `schema_version`, or omitting `initial_world` when `doc.schema_version` is omitted;
- `Array.isArray(doc.criteria)` containing a number (`1`), numeric or labeled string (`"1"`, `"2: ..."`), or object with a numeric/labeled `id`;
- any nested plain object using `$use`, `$from`, `$json`, `$step`, or inline `$seed` naming a key of `doc.seeds`;
- any step in `doc.steps` that is a plain object using `id`, `op`, `error`, `from`, `patch`, `set`, omitted `step_id` / `entry_path` / `operation` / `input` when `doc.schema_version !== V1_SCENARIO_SCHEMA`, a plain-object `checks` map keyed by criterion ID, an array `checks` containing tuple arrays, or a check object with omitted or numeric/labeled `criterion_id` or Short JSON operator aliases.

`needsScenarioCompile(doc)` returns `true` when `isShortScenarioDoc(doc)` is `true` or when `doc` is a `V1_SCENARIO_SCHEMA` plain object with `Array.isArray(doc.steps)` that omits top-level `criteria`. Standard `V1_SCENARIO_SCHEMA` documents that explicitly declare `criteria` pass through unchanged (`changed: false`) without rewriting explicit criterion IDs in memory.

## Compilation rules

`compileScenario(doc, { path = 'tests/story.json', storyPath = null, storySource = null } = {})` returns `{ doc: compiledDoc, changed: boolean, refusal }` and never mutates its input:

1. **Omitted-`criteria` `V1_SCENARIO_SCHEMA` binding:**
   - When `!isShortScenarioDoc(doc)` and `doc.schema_version === V1_SCENARIO_SCHEMA`, `!Object.hasOwn(doc, 'criteria')`, and `Array.isArray(doc.steps)`, extract numbered Story acceptance criteria under `## Acceptance criteria` (`numberedStoryCriteria(storySource, { requireHeading: true })`). When `effectiveStoryPath` and numbered Story criteria are available, synthesize `criteria: [{ id: criterionContentId(text, effectiveStoryPath), text }, ...]` and map positional `criterion_id` references (`"AC1"`, `"ac-1"`, `"1"`, `1`, or omitted `criterion_id` on a single-criterion Story) across `steps[*].checks`, `steps[*].simulation_overrides`, `check_exemptions`, and `criteria_scope` to those `ac-sha256-...` IDs, leaving out-of-range or unknown IDs unmapped for normal preflight validation. When numbered Story criteria are absent, return `{ doc, changed: false, refusal: null }` so normal preflight reports `story-criteria-missing`.

2. **Short JSON top-level fields and defaults:**
   - Allow `schema_version` to be omitted, `SHORT_SCENARIO_SCHEMA`, or `V1_SCENARIO_SCHEMA`, and emit `schema_version: V1_SCENARIO_SCHEMA`. Refuse any other `schema_version` (`invalid-document`).
   - Default `story_path` to `storyPath` when omitted and `storyPath` is a nonblank string.
   - Default `initial_world` to `{}` when omitted.
   - Read optional top-level `entry_path` (nonblank string) as the default `step.entry_path` (or `doc.entry_paths[0]` when `entry_paths` has length 1), and strip `entry_path` and `seeds` from the emitted `v1` top-level object. Refuse unknown top-level keys outside `v1` keys plus `seeds` and `entry_path` (`invalid-document`).

3. **Criteria resolution and content-bound IDs:**
   - Extract Story acceptance criteria from `storySource` (`extractStoryCriteria(storySource)`), matching numbered items from `1` under `## Acceptance criteria` (`## Acceptance`) or top-level bullets when no numbered items exist.
   - When `doc.criteria` is omitted and `storySource` criteria are available, emit `criteria` directly with content-bound IDs `criterionContentId(text, effectiveStoryPath)` when `effectiveStoryPath` is a nonblank string (falling back to `AC1..ACn` only when no `storyPath` is supplied), and map positional criterion references (`1`, `"1"`, `"AC1"`, `"ac-1"`, labeled `"2: label"`, or omitted `criterion_id` on a single-criterion Story) across `steps[*].checks`, `steps[*].simulation_overrides`, `check_exemptions`, and `criteria_scope` to the matching criterion ID.
   - When a `: label` suffix is supplied and `storySource` criteria are available, verify that the referenced Story criterion text contains `label` (case-insensitively after collapsing whitespace and normalizing curly quotes to straight quotes); otherwise return `refusal('story-criterion-mismatch', section, ...)`. When `storySource` criteria are available and a positional index exceeds the Story criterion count, return `refusal('unknown-criterion', section, ...)`.
   - When `doc.criteria` explicitly provides `{ id, text }` items, preserve explicit string IDs (`"AC1"`, `"ac-sha256-..."`, etc.) without silently rewriting legacy IDs in memory, and map unambiguous positional check keys (`1`, `"1"`, `"AC1"`) to `criteria[index - 1].id` so bound `ac-sha256-...` explicit criteria work with Short JSON numeric check keys. When `doc.criteria` lists shorthand items (`1`, `"1"`, `"AC1"`, `{"id": "1"}`) without `text`, expand them against `storySource` criteria, refusing duplicates (`duplicate-criterion`).

4. **Named `seeds` and recursive value macros:**
   - Resolve `doc.seeds` entries lazily with cycle detection (`seed-cycle`).
   - Expand value macros recursively inside `initial_world`, `steps[*].input`, `simulation`, and `steps[*].simulation_overrides`:
     - `{"$use": ref, "patch"?: mergePatch, "set"?: pointerMap}` (also `$from`, or `$seed` when `ref` is an own key of `doc.seeds`; external file `{"$seed": "path.json"}` stays untouched): clone the named seed (`ref` or `$seed.<name>`) or earlier compiled step input (`step:<step_id>`), apply RFC 7386 JSON Merge Patch `patch` (recursively merging plain objects and deleting `null` keys), then apply RFC 6901 JSON Pointer overrides in `set`. Refuse unknown seed/step names, invalid pointers, or extra keys (`invalid-seed`).
     - `{"$json": inner}`: recursively expand `inner` and return `stringifyExactScenarioJson(expandedInner)`.
     - `{"$step": spec}`: accept `"<step_id>"`, `"<step_id>#<pointer>"`, or `["<step_id>", "<pointer>"]` and emit `{"$step_result": {"step_id": stepId, "path": pointer}}`. Refuse malformed specs (`invalid-step-ref`).

5. **Steps and checks (`doc.steps`):**
   - Require a nonempty `steps` array (`missing-steps`).
   - Map `id` -> `step_id` (defaulting to `"step-" + (index + 1)`), `op` -> `operation`, `error` -> `expected_error` (normalizing `{"code": "<code>"}` to `"<code>"`, and when both `error` and `expected_error` are omitted, auto-inferring `expected_error` when step `checks` assert a single distinct `target: "error", path: "/code", op: "equals"` nonblank string code), and default `entry_path` from top-level `entry_path` (or single `entry_paths[0]`). Refuse conflicting duplicate aliases or unknown step keys (`invalid-step`), and refuse specifying both `from` and `input` (`invalid-step`).
   - Accept `step.checks` as an array of check items or a plain object mapping criterion keys to check items (or a single tuple when its first item is a string). Normalize operator aliases (`=`, `==`, `!=`, `>=`, `<=`, `len>=`, `length_at_least`, `len<=`, `length_at_most`, `>`, `<`, `contains_all`, `includes_all`), `calls` path shorthands (`internal:<node>`, `<node>.<resource>.<op>`, `<resource>.<op>`), `["error", op, code]`, and HTML tuples (`html_exists`, `html_text`, `html_attr`, `["html", selector, "labels_include", [...]]`). Preserve any optional `"derivation"` field on check objects unchanged in the expanded check, and allow an optional trailing `{"derivation": "<expr>"}` metadata object on Short JSON value-check tuples (such as `[target, path, op, value, {"derivation": "<expr>"}]` or `["criterion", target, path, op, value, {"derivation": "<expr>"}]`) that expands to `"derivation": "<expr>"` on the compiled check (refusing unknown metadata keys as `invalid-check`). Also preserve `"derivation"` untouched during `--bind-criteria` rewrites (`bindScenarioCriteriaText`).

`compileScenarioText(text, { path, storyPath, storySource, space = 2 } = {})` parses `text` with `parseExactScenarioJson`, runs `compileScenario`, and returns `{ text: outText, doc: jsonSafeDoc, exactDoc, changed, refusal }`.

## Explicit criterion binding inspection and `--bind-criteria` rewrite

- `classifyExplicitCriteriaBinding(doc, { storyPath, storySource } = {})`: inspect a parsed scenario document with explicit `criteria` against `numberedStoryCriteria(storySource, { requireHeading: true })`. Return `{ kind: 'stale-content-id', criterionId, text }` whenever any `ac-sha256-` criterion ID no longer matches a current Story criterion text or its computed `criterionContentId(text, effectiveStoryPath)`; return `{ kind: 'text-mismatch' }` whenever `criteria` texts do not match the Story's numbered `## Acceptance criteria` 1-for-1 word for word; return `{ kind: 'already-bound' }` when all IDs already equal `criterionContentId(text, effectiveStoryPath)`; and return `{ kind: 'legacy-unbound', legacyIds, bindings }` only when every criterion text matches the Story word for word with zero stale `ac-sha256-` IDs and at least one non-`ac-sha256-` legacy ID.
- `bindScenarioCriteriaText(text, { path, storyPath, storySource, space = 2 } = {})`: for `pdd lint --bind-criteria`, refuse without changing `text` whenever Story numbered `## Acceptance criteria` are missing, whenever `classifyExplicitCriteriaBinding` reports `stale-content-id` or `text-mismatch`, or whenever an omitted-`criteria` or bound Short JSON scenario has a compile/criterion refusal. When explicit legacy IDs match the Story word for word, rewrite only `criteria[*].id` and matching `criterion_id` references (`steps[*].checks`, `steps[*].simulation_overrides`, `check_exemptions`, `criteria_scope`) to `criterionContentId(text, effectiveStoryPath)`—using token-preserving JSON string replacement verified by exact `BigInt`-preserving deep equality before falling back to `stringifyExactScenarioJson`, verifying `compileScenarioText` succeeds on bound Short JSON output, and preserving 100% of check expectations. When `criteria` is omitted on disk, materialize `criteria` and mapped `criterion_id` references with `ac-sha256-...` content IDs while preserving all check expectations.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"approved","prose_sha256": "b3ba81a163d83ad359dea0b5a6200bd2cc26d4387ab8d82d04742f3a9c73a85c","reason":"Pure synchronous BigInt-preserving JSON compiler leaf loaded directly by src/runtime-seam.mjs without external ports."}
```
</details>
