# Short scenario compiler

Own `src/scenario-compile.mjs`. Compile authored PDD Short JSON scenario documents deterministically into canonical `prompt-runtime.program-scenario.v1` JSON without network, model, GitHub, Herdr, or filesystem writes, while passing standard `prompt-runtime.program-scenario.v1` documents through unchanged.

## Exact JSON codec and pass-through

Preserve exact whole numbers outside IEEE-754 `Number.MAX_SAFE_INTEGER` using `BigInt` during parsing and `JSON.rawJSON` during serialization:

- `parseExactScenarioJson(text)`: parse UTF-8 JSON text, turning unsafe exact integer tokens (`/^-?(?:0|[1-9][0-9]*)$/`) into `BigInt` values.
- `stringifyExactScenarioJson(value, space)`: serialize JSON values while writing `BigInt` leaves via `JSON.rawJSON`.
- `jsonSafeScenario(value)`: convert any `BigInt` leaves to JavaScript `Number` values for callers that store `JSON.parse`-compatible discovery documents.

`V1_SCENARIO_SCHEMA` is `'prompt-runtime.program-scenario.v1'`. `SHORT_SCENARIO_SCHEMA` is `'pdd.scenario.short.v1'`.

`isShortScenarioDoc(doc)` returns `true` only when `doc` is a plain JSON object that uses at least one Short JSON construct:

- `doc.schema_version === SHORT_SCENARIO_SCHEMA`, top-level `seeds`, or top-level singular `entry_path`;
- `Array.isArray(doc.steps)` while omitting `schema_version` or `initial_world`;
- `Array.isArray(doc.criteria)` containing a number (`1`), numeric or labeled string (`"1"`, `"2: ..."`), or object with a numeric/labeled `id`;
- any nested plain object using `$use`, `$from`, `$json`, `$step`, or inline `$seed` naming a key of `doc.seeds`;
- any step in `doc.steps` that is a plain object using `id`, `op`, `error`, `from`, `patch`, `set`, omitted `step_id` / `entry_path` / `operation` / `input`, a plain-object `checks` map keyed by criterion ID, an array `checks` containing tuple arrays, or a check object with omitted or numeric/labeled `criterion_id`.

When `isShortScenarioDoc(doc)` is `false`, `compileScenario(doc)` returns `{ doc, changed: false, refusal: null }` without altering member order or values.

## Compilation rules

`compileScenario(doc, { path = 'tests/story.json', storyPath = null, storySource = null } = {})` returns `{ doc: compiledDoc, changed: boolean, refusal }` and never mutates its input:

1. **Top-level fields and defaults:**
   - Allow `schema_version` to be omitted, `SHORT_SCENARIO_SCHEMA`, or `V1_SCENARIO_SCHEMA`, and emit `schema_version: V1_SCENARIO_SCHEMA`. Refuse any other `schema_version` (`invalid-document`).
   - Default `story_path` to `storyPath` when omitted and `storyPath` is a nonblank string.
   - Default `initial_world` to `{}` when omitted.
   - Read optional top-level `entry_path` (nonblank string) as the default `step.entry_path` (or `doc.entry_paths[0]` when `entry_paths` has length 1), and strip `entry_path` and `seeds` from the emitted `v1` top-level object. Refuse unknown top-level keys outside `v1` keys plus `seeds` and `entry_path` (`invalid-document`).

2. **Criteria resolution and criterion IDs:**
   - Extract Story acceptance criteria from `storySource` (`extractStoryCriteria(storySource)`), matching numbered items from `1` under `## Acceptance criteria` (`## Acceptance`) or top-level bullets when no numbered items exist.
   - Normalize criterion references (`1`, `"1"`, `"AC1"`, `"ac-1"`, or labeled `"2: Snake grows"` -> `"AC2"`). When a `: label` suffix is supplied and `storySource` criteria are available, verify that the referenced Story criterion text contains `label` (case-insensitively after collapsing whitespace and normalizing curly quotes to straight quotes); otherwise return `refusal('story-criterion-mismatch', section, ...)`. When `storySource` criteria are available and an `ACn` index exceeds the Story criterion count, return `refusal('unknown-criterion', section, ...)`.
   - When `doc.criteria` is omitted and `storySource` criteria are available, emit `criteria: [{ id: 'AC1', text }, ...]`. When `doc.criteria` lists shorthand items (`1`, `"1"`, `"AC1"`, `{"id": "1"}`), expand them against `storySource` criteria, refusing duplicates (`duplicate-criterion`) or missing Story criteria (`story-criteria-missing`).

3. **Named `seeds` and recursive value macros:**
   - Resolve `doc.seeds` entries lazily with cycle detection (`seed-cycle`).
   - Expand value macros recursively inside `initial_world`, `steps[*].input`, `simulation`, and `steps[*].simulation_overrides`:
     - `{"$use": ref, "patch"?: mergePatch, "set"?: pointerMap}` (also `$from`, or `$seed` when `ref` is an own key of `doc.seeds`; external file `{"$seed": "path.json"}` stays untouched): clone the named seed (`ref` or `$seed.<name>`) or earlier compiled step input (`step:<step_id>`), apply RFC 7386 JSON Merge Patch `patch` (recursively merging plain objects and deleting `null` keys), then apply RFC 6901 JSON Pointer overrides in `set`. Refuse unknown seed/step names, invalid pointers, or extra keys (`invalid-seed`).
     - `{"$json": inner}`: recursively expand `inner` and return `stringifyExactScenarioJson(expandedInner)`.
     - `{"$step": spec}`: accept `"<step_id>"`, `"<step_id>#<pointer>"`, or `["<step_id>", "<pointer>"]` and emit `{"$step_result": {"step_id": stepId, "path": pointer}}`. Refuse malformed specs (`invalid-step-ref`).

4. **Steps (`doc.steps`):**
   - Require a nonempty `steps` array (`missing-steps`).
   - Map `id` -> `step_id` (defaulting to `"step-" + (index + 1)`), `op` -> `operation`, `error` -> `expected_error` (normalizing `{"code": "<code>"}` to `"<code>"`, and when both `error` and `expected_error` are omitted, auto-inferring `expected_error` when step `checks` assert a single distinct `target: "error", path: "/code", op: "equals"` nonblank string code), and default `entry_path` from top-level `entry_path` (or single `entry_paths[0]`). Refuse conflicting duplicate aliases (such as both `id` and `step_id` with different values) or unknown step keys (`invalid-step`).
   - Build `input` from `step.from` (resolving a seed name, `$seed.<name>`, or an earlier step's `step_id`) or `step.input` (default `{}`), then apply optional `step.patch` and `step.set`. Refuse specifying both `from` and `input` (`invalid-step`).

5. **Checks (`step.checks`):**
   - Accept either an array of check items or a plain object mapping criterion keys (`"1"`, `"AC1"`, `"2: ..."`) to a list of check items (or a single tuple when its first item is a string).
   - Normalize operator aliases: `"="` / `"=="` -> `"equals"`, `"!="` -> `"not_equals"`, `">="` -> `"at_least"` (`measure: "value"`), `"<="` -> `"at_most"` (`measure: "value"`), `"len>="` / `"length_at_least"` -> `"at_least"` (`measure: "length"`), `"len<="` / `"length_at_most"` -> `"at_most"` (`measure: "length"`), `">"` -> `"gt"`, `"<"` -> `"lt"`, plus canonical `v1` operators (`equals`, `not_equals`, `contains`, `not_contains`, `count`, `exists`, `one_of`, `all_in`, `equals_ignore_case`, `at_least`, `at_most`, `lt`, `lte`, `gt`, `gte`, `integer_relation`). When `at_least` or `at_most` omits `measure`, default `measure` to `"value"`. Refuse any unknown operator (`invalid-check`).
   - Support check tuples (prefixed with `criterionId` inside array `checks`, or unprefixed inside keyed `checks[criterionKey]`):
     - `[target, path, op, value]` and `[target, path, "exists"]` (`value: true`) for `target` in `result`, `world`, `calls`, `error`;
     - `[target, path, "contains_all" | "includes_all", [s1, s2, ...]]` for `result` or `world`, expanding into one `contains` check per nonempty string;
     - `["error", op, code]` -> `{ criterion_id, target: "error", path: "/code", op, value: code }`;
     - `calls` path shorthand: keep paths starting with `"/"`, map `"internal:<node>"` -> `"/internal/<node>"`, `"<node>.<resource>.<op>"` -> `"/resources/<node>-<resource>-<op>"`, and `"<resource>.<op>"` -> `"/resources/<entryNode>-<resource>-<op>"` using the basename of `step.entry_path` without `.prompt.md`;
     - HTML tuples on `result` (`htmlPath` defaults to `"/html"`), parsing compact selectors `"tag"`, `"tag#id"`, `"tag.class"`, and `"tag[attr=val]"` into `{ tag, attributes }`:
       - `["html_exists", selector, boolValue?, htmlPath?]` -> `kind: "element"`, `op: "exists"`, `value: boolValue ?? true`;
       - `["html_text", selector, op, value, htmlPath?]` -> `kind: "text"`;
       - `["html_attr", selector, attribute, op, value?, htmlPath?]` -> `kind: "attribute"`, `attribute`;
       - `["html", selector, "labels_include", [label1, ...], htmlPath?]` -> one exact `kind: "element"`, `op: "exists"`, `value: true` check on `selector` plus one `target: "result"`, `path: htmlPath`, `op: "contains"` check per label.

`compileScenarioText(text, { path, storyPath, storySource, space = 2 } = {})` parses `text`, compiles the document, and returns `{ text: outText, doc: jsonSafeDoc, exactDoc, changed, refusal }`.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"dd8fe0e0b70c00b6fdbd2d4c444370ab396d3b4fc72d991e38a5883301f40700","reason":"Pure synchronous BigInt-preserving JSON compiler leaf loaded directly by src/runtime-seam.mjs without external ports."}
```
</details>
