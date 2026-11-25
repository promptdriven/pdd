# Test ergonomics decision core

Own `src/core/test-ergonomics.mjs`: pure deterministic option planning, unresolved batch row selection, auto-reconciliation preflight planning, and single-scenario sibling-criteria classification for `pdd test`. Perform zero filesystem, Git, network, or AI I/O; never mutate caller inputs.

## Domain decisions

1. **Batch ID format:** a valid local batch ID matches `/^\d{8}-\d{6}-[a-z0-9]{4}$/`. Reject non-strings, whitespace-padded strings, and malformed values with exit code `2`.
2. **Safe repository-relative scenario paths:** accept only non-empty strings without leading `/`, Windows drive prefix (`^[A-Za-z]:`), `\`, ASCII control characters (`\x00-\x1f`, `\x7f`), or empty / `.` / `..` / `.git` (case-insensitive) segments. Reject unsafe paths into `invalid_paths` and never enqueue them for retry.
3. **Option precedence and compatibility (`planTestErgonomicsOptions`):**
   - Inspect `{ words, options }` where `words` is an array of string operands and `options` is a map of parsed CLI flags to boolean/string/number values.
   - Evaluate in order:

| Condition | Result `mode` | Allowed flags | Failure outcome |
|---|---|---|---|
| `--retry-unresolved` present | `"retry-unresolved"` | `--retry-unresolved`, `--json`, `--details`, `--timeout`, `--batch-timeout`, `--max-calls`, `--max-total-calls`, `--no-restart-replacement`, `--fresh`, `--cache-clear` | Exit `2` on non-matching batch ID, any operand in `words`, or any disallowed option |
| `--affected === true` and `--files === true` | `"affected-files"` | `--affected`, `--files`, `--json`, `--app-map` | Exit `2` on any operand in `words` or any disallowed option |
| `--affected` and `--files` both present (not `undefined`) with either value `!== true` | `"invalid"` | none | Exit `2` |
| All other inputs | `"passthrough"` | caller-owned | `handled: false`, `exit_code: 0` |

   - Reject combining `--retry-unresolved` with `--affected` or `--files` as `"invalid"` (exit `2`).
   - Return fresh `{ handled, mode, exit_code, ai_calls, error, batch_id, forwarded_options }`. For `"affected-files"`, `ai_calls` is `0`; for `"retry-unresolved"`, `batch_id` is the valid batch ID and `forwarded_options` holds all allowed options other than `--retry-unresolved` (normalizing `--json` boolean); for `"invalid"`, `handled: true`, `exit_code: 2`, `ai_calls: 0`, and `error` is a single non-empty diagnostic sentence.

4. **Non-passed scenario selection (`selectUnresolvedBatchTests`):**
   - Inputs: `{ batch_id, rows, receipts_by_id }` where each row has `{ test, state, recovery_state, note_code, request_ids, failed_check_count, refusal_count }` (optional fields default to `null` / `0` / `[]`) and `receipts_by_id` is an optional map from request ID string to terminal receipt state string (`"passed"`, `"failed"`, `"refused"`, `"unknown"`, `"not_run"`, etc.).
   - Resolve each row's effective state:
     - If the row's latest request ID (`request_ids` last element) maps in `receipts_by_id` to a terminal state (`"passed"`, `"failed"`, `"refused"`), that receipt state takes precedence over stale open states (`"sending"`, `"queued"`, `"running"`, `"waiting"`, `"unknown"`, `"partial"`), except when `note_code === "criteria-not-checked"` or `failed_check_count > 0` or `refusal_count > 0`.
     - Otherwise use `recovery_state` when non-empty string, else `state`.
   - A row is **passed** ONLY when its effective state is `"passed"`, `note_code !== "criteria-not-checked"`, `failed_check_count === 0`, and `refusal_count === 0`.
   - Every other row (`"partial"`, `"unknown"`, `"not_run"`, `"not run"`, `"failed"`, `"refused"`, `"sending"`, `"queued"`, `"running"`, `"waiting"`, `"ready"`, or missing/unrecognized state) is **non-passed** and MUST be included in `retry_tests` (in first-seen row order, deduplicated).
   - If the same `test` path appears multiple times in `rows`, any non-passed occurrence wins over an earlier passed occurrence.
   - Return `{ batch_id, retry_tests, passed_tests, skipped_count, all_passed, invalid_paths }` where `skipped_count === passed_tests.length` and `all_passed === (retry_tests.length === 0 && invalid_paths.length === 0)`.

5. **Auto-reconciliation preflight planning (`planAutoReconcile`):**
   - Inputs: `{ options, stale_batches, default_timeout_ms, configured_timeout_ms }` where `stale_batches` is an array of `{ batch_id, expired_count, within_ttl_count }` records for prior unresolved batches of the current repository.
   - Non-dispatch flags: `--files`, `--app-map`, `--explain-bindings`, `--read`, `--retry`, `--retry-unresolved`, `--reconcile`, `--reconcile-stale`, `--request`, `--screen`, `--drawing`, `--look`, `--lint`, `--local`, `--emit-v1`, `--write`, `--bind-criteria`, `--target`.
   - If any non-dispatch flag is present (value not `undefined` and not `false`), return `should_reconcile: false`, `reason: "non-dispatch-mode"`, `stale_batches: []`, `expired_count: 0`, `within_ttl_count: 0`, `timeout_ms: 0`.
   - Filter `stale_batches` to valid batch IDs whose `expired_count + within_ttl_count > 0`; deduplicate by `batch_id` (sorted ASCII-lexicographically). If none remain, return `should_reconcile: false`, `reason: "no-stale-reservations"`, `stale_batches: []`, `expired_count: 0`, `within_ttl_count: 0`, `timeout_ms: 0`.
   - Otherwise compute `timeout_ms`: parse positive finite `configured_timeout_ms` (else `default_timeout_ms`, else `10000`) and clamp to integer `[100, 60000]`. Return `should_reconcile: true`, `reason: "stale-reservations-present"`, `stale_batches` (sorted array of `batch_id` strings), `expired_count` (sum of non-negative integers), `within_ttl_count` (sum of non-negative integers), and `timeout_ms`.

6. **Single-scenario sibling-criteria classification (`classifyTargetedScenarioCriteria`):**
   - Inputs: `{ explicit_scenario_paths, target_test_path, story_criteria_ids, own_checked_ids, sibling_checked_ids }` (all string arrays except `target_test_path` string).
   - `is_targeted_slice`: `true` iff `explicit_scenario_paths` contains `target_test_path`.
   - Deduplicate `story_criteria_ids` preserving order. Let `ownSet` be the subset of `story_criteria_ids` present in `own_checked_ids`, and `siblingSet` be the subset of `story_criteria_ids` present in `sibling_checked_ids`.
   - `sibling_covered_ids`: IDs in `story_criteria_ids` that are NOT in `ownSet` and ARE in `siblingSet`.
   - `uncovered_ids`: IDs in `story_criteria_ids` that are NOT in `ownSet` and NOT in `siblingSet`.
   - `can_pass_as_targeted_slice`: `true` iff `is_targeted_slice === true` AND `story_criteria_ids.length > 0` AND `ownSet.size > 0` AND `uncovered_ids.length === 0`.
   - Return `{ is_targeted_slice, own_checked_count: ownSet.size, sibling_covered_ids, uncovered_ids, can_pass_as_targeted_slice }`.

## Public contract

Export four synchronous pure functions from `src/core/test-ergonomics.mjs` plus constants `AUTO_RECONCILE_DEFAULT_TIMEOUT_MS` (`10000`), `AUTO_RECONCILE_MIN_TIMEOUT_MS` (`100`), `AUTO_RECONCILE_MAX_TIMEOUT_MS` (`60000`), `isValidBatchId(value)`, and `isSafeScenarioPath(value)`:

- `planTestErgonomicsOptions({ words, options })`
- `selectUnresolvedBatchTests({ batch_id, rows, receipts_by_id })`
- `planAutoReconcile({ options, stale_batches, default_timeout_ms, configured_timeout_ms })`
- `classifyTargetedScenarioCriteria({ explicit_scenario_paths, target_test_path, story_criteria_ids, own_checked_ids, sibling_checked_ids })`

All four functions accept missing/undefined optional fields fail-closed without throwing on malformed caller data (normalizing non-arrays to `[]`, non-objects to `{}`), and never mutate their inputs.

## Dependencies

None. All four operations are pure deterministic functions over supplied data.
