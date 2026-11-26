# Formal-to-Vector Short JSON export

Own `src/core/lint/vector-export.mjs`. Convert deterministic formal test specs (`pdd.formal-vectors.v1` from Hypothesis, seeded PRNG loops, or finite boundary grids) and Quint/Apalache Informal Trace Format (ITF) JSON traces into `pdd lint`-clean PDD Short JSON companion scenarios (`tests/<Story>.<focus>.json`) offline with zero AI calls and zero network calls.

## Domain decisions

- **Dry-run by default:** Never write any file unless `--write` is explicitly supplied. Without `--write`, return or print the generated Short JSON preview and exit `0`.
- **Fail-closed validation:** Refuse non-object inputs, missing or blank `entry_path`, empty or non-array `cases`, unknown keys on specs or cases, duplicate step IDs, invalid RFC 6901 JSON Pointers (must start with `/`), cases with zero checks, and `cases.length > maxSteps` unless `split: true` (`max-steps-exceeded`). On any refusal, return `{ ok: false, refusal }` and write zero files.
- **Exact integer preservation:** Parse and serialize JSON preserving integers outside IEEE-754 safe precision (`BigInt` / `JSON.rawJSON`) and unwrap Quint ITF `{ "#bigint": "<digits>" }` objects directly to exact integer values without floating-point rounding.
- **Idiomatic Short JSON output:** Omit `schema_version` and `criteria` so PDD binds numbered Story acceptance criteria automatically, omit `initial_world` / `simulation` / `seeds` when empty, and never emit `criteria_scope` or `check_exemptions`. Verify every emitted Short JSON document compiles cleanly through the Short scenario compiler before returning or writing.
- **Companion chunking:** When `split: true` and `cases.length > maxSteps`, split cases sequentially in input order into chunks of at most `maxSteps` steps. Given output base `dir/name.json`, chunk paths are `dir/name-01.json`, `dir/name-02.json`, … (zero-padded to at least 2 digits, or wider if `chunks >= 100`). When only 1 chunk is emitted, keep `dir/name.json` unchanged.

## Input formats

| Format | Detection | Conversion rules |
| --- | --- | --- |
| `pdd.formal-vectors.v1` | `schema_version === "pdd.formal-vectors.v1"` or plain object with `Array.isArray(cases)` | Validate top-level keys (`schema_version`, `story_path`, `entry_path`, `default_op`, `default_criterion`, `initial_world`, `simulation`, `seeds`, `cases`). For each case (`id`, `op`, `entry_path`, `criterion`, `input`, `from`, `patch`, `set`, `error`, `expect`, `expect_world`, `checks`), build a Short JSON step with `id` (default `"case-1"`, `"case-2"`, …), `op` (fallback `default_op`), optional per-step `entry_path` (only when differing from top-level `entry_path`), `input` (default `{}` when `from` is omitted), optional `from`/`patch`/`set`, optional `error`, and `checks` keyed by `criterion` (default `default_criterion` or `"1"`). |
| Quint / Apalache ITF trace | Plain object with `Array.isArray(states)` and (`"#meta"` on root or `states[0]["#meta"]`) | Unwrap `#bigint`, `#tup`, `#set`, and string-keyed `#map` recursively across states. Require `states.length >= 2` (state `0` is initial state, `states[1..n]` are transitions). Strip `#meta` from state objects. Derive `initial_world` from state `0` (excluding trace-meta fields `action`/`op`/`input`/`result`/`error` unless caller passes explicit `initial_world`). For each transition `states[i]`, extract operation from `state.action ?? state.op ?? defaultOp`, input from `state.input ?? {}`, optional error from `state.error`, and exact checks from `state.result` (when object, `/k` result checks) or changed non-meta state variables (as `result` checks `/<var> = <value>`). |

## Check construction on each case

For every case in `cases`:
1. If `error` is a nonblank string, set `step.error = error` and add `["error", "=", error]`.
2. For each `[pointer, expected]` of plain-object `expect` (in key order), require pointer starting with `/` (else refuse `invalid-pointer`) and add `["result", pointer, "=", expected]`.
3. For each `[pointer, expected]` of plain-object `expect_world` (in key order), require pointer starting with `/` (else refuse `invalid-pointer`) and add `["world", pointer, "=", expected]`.
4. Append any explicit Short JSON check tuples from `checks` (array of arrays, validating non-empty tuple shape).
5. Require at least `1` check per case; if zero checks exist, refuse with code `missing-checks`.

## Public contract

- `FORMAL_VECTORS_SCHEMA = 'pdd.formal-vectors.v1'`, `FORMAL_EXPORT_RESULT_SCHEMA = 'pdd.formal-vectors-export.v1'`, `DEFAULT_EXPORT_MAX_STEPS = 15`.
- `normalizeItfValue(value)`: pure. Recursively unwrap Quint ITF tagged values (`#bigint`, `#tup`, `#set`, `#map`).
- `convertItfTrace(itfDoc, { storyPath, entryPath, defaultOp, defaultCriterion = '1', initialWorld, simulation } = {})`: pure. Return `{ ok: true, spec }` or `{ ok: false, refusal }`.
- `formatCompanionOutputPaths(basePath, chunkCount)`: pure. Return `[basePath]` when `chunkCount <= 1`, else `[dir/stem-01.json, ...]`.
- `exportFormalVectors(inputDoc, { storyPath, entryPath, defaultOp, defaultCriterion = null, maxSteps = 15, split = false, outputBasePath = 'tests/formal-export.json', storySource = null } = {})`: pure. Option overrides (`entryPath`, `storyPath`, `defaultOp`, `defaultCriterion`) take precedence over spec-level fields (`entry_path`, `story_path`, `default_op`, `default_criterion`, with criterion falling back to `"1"`). Return `{ ok: true, schema_version: FORMAL_EXPORT_RESULT_SCHEMA, files: [{ path, doc, text, step_count, check_count }], warnings }` or `{ ok: false, refusal: { code, section, message, hint } }`.
- `runVectorExport({ cwd, inputPath, outPath, storyPath, entryPath, op, criterion, maxSteps, split, write, json }, ports)`: CLI handler reading `inputPath` (or stdin when `inputPath === '-'` or omitted with piped stdin), validating repository-safe regular output paths (refusing path traversal, null bytes, absolute paths escaping repo, and symlinks) when `write: true`, writing files only when `write: true`, and returning exit code `0` (success), `1` (validation/compile refusal), or `2` (usage/argument/I/O error).

## Dependencies

None.
