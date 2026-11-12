# Recent lint receipt eligibility

Own `src/runtime-lint-receipt.mjs`. New behavior authorized by issue #3208;
existing command semantics and lint verdict policy remain with runtime-client.
Export module function `isRecentLintReceipt({receipt,scope,now,engineSha=null})`
returning a Boolean. This pure hook decides metadata eligibility only; its
caller must validate the actual answer and per-test admission before reuse.

`scope` has exactly root (canonical repository path), origin (normalized Runtime
origin), login, user_id (GitHub numeric identity), source_sha256 (64 lower-case
hex characters, the upload hash), authored_sha256 (64 lower-case hex characters,
the hash of the authored file hashes, so a change that the upload projection
removes is still a change), tests (nonempty sorted unique repository-relative test paths),
version (package version), selected_cap (null or integer 1 through 1000).
All path/name/version strings must be nonblank; user_id is a nonblank string of decimal digits.
A receipt has schema_version `pdd.lint-receipt.v1`, scope in that shape,
received_at (finite epoch milliseconds) and engine_sha (nonblank string other
than case-insensitive `unknown`), plus an answer retained by the caller.

Return true exactly when both scopes are well formed and equal field for field,
the receipt version and engine are valid, and `now - received_at` is between
zero and 600000 milliseconds inclusive. `now` must also be finite. Missing,
null, malformed or future times are false. `engineSha` is the current engine
identity and is required: return true only when it is a known nonblank string
(not `unknown`) equal to receipt.engine_sha. Omitted, null or unknown returns
false, because an unknown current engine cannot prove that no deployment
happened. Extra receipt fields (the answer)
are ignored by this metadata hook; scope keys are exact. Never mutate inputs,
read files, access a clock, authenticate or send requests.

## Dependencies

Use native JavaScript finite-number, string and array comparisons. The caller
supplies all data; there are no external effects. Runtime interface transport
uses JSON strings `receipt_json` and `scope_json` for these canonical objects;
invalid JSON returns false. Native callers use the object signature above.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[{"operation":"isRecentLintReceipt","input_schema":{"type":"object","properties":{"receipt_json":{"type":"string"},"scope_json":{"type":"string"},"now":{"type":"number"},"engineSha":{"oneOf":[{"type":"string"},{"type":"null"}]}},"required":["receipt_json","scope_json","now","engineSha"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"eligible":{"type":"boolean"}},"required":["eligible"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":4},"conventions":[]}
```
</details>
