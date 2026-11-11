# Check scope and interpreter call plan

Own `src/runtime/runtime-check-plan.mjs`. Before a full Check, explain its scope and
bounded work so an owner can distinguish target work from baseline obligations.
Preserve the selected full batch, its exit code and required full-pass gates.
This is local planning, not approval or proof of a baseline defect's age or owner.

Export `buildCheckPlan({root,found,selected,rows,full,base}, ports={})`.
The optional base is the unique workflow run's saved base SHA; otherwise use HEAD.
Read tracked changes against that base and untracked files through `ports.git`
(default a local Git process; NUL-delimited paths). Include staged, unstaged and
committed run changes. On an unavailable comparison, classify all selected
Stories as targets with an explicit conservative reason. A named selection is
always target work. In a full selection with known changes, intersect each
Story's captured upload closure with changed paths. Capture via `ports.capture`
(default the canonical capture owner), grouping every selected test variant.
Changed tests, Stories and transitive dependencies affect that Story. Translate
changed implementation paths to their owning prompts through every Generated-from
header that the shared [header reader](../file-owner.prompt.md#generated-from-header)
finds, and through the binding inventory when declared. For a deleted
implementation, read the same owner headers from the comparison base revision. Apply workspace
exclusions before reading base metadata; excluded paths cannot affect ownership.
If permitted metadata cannot prove a deleted path's owner, retain the selected
Stories as conservative targets, even when another change already establishes a
target. Never classify uncertain deleted ownership as unrelated baseline work.
If no target can be established,
retain all Stories as targets, stating that scope is conservative. Never infer
unrelated status from an unavailable closure.

Return `schema_version:"pdd.check-plan.v1"`, `full` (boolean), `base` (comparison
revision), `changed_paths` (sorted paths or null), `stories` (selection order),
`calls`, and `prerequisites`. Each Story has `story_path`, `tests` (all selected
test paths), `role` (`target` or `baseline`), `reason`, `affected_paths`, and
`dependency_closure` (sorted captured paths). Baseline means unrelated to the
known changes, still required by this batch; it does not claim a pre-change pass.
Each prerequisite is `{code,path,field}`. Deduplicate these in discovery order.

Inspect every executable entry and nested call independently of other preflight
failures. Missing/unreadable interfaces, absent or nonpositive integer
max_model_calls, undefined call max_calls and recursive calls produce named
prerequisites. Native-only entries need no interpreter bound. Any prerequisite
makes `calls.estimated` and `calls.maximum` null. A full Check with any such
prerequisite sends no paid Check, including otherwise ready Stories.

`calls` has `estimated` (entry executions plus declared resource operations and
nested call allowances, capped per test; a conservative estimate before cache
reuse), `maximum` (sum of per-test request caps
including the one permitted restart replacement), `check_requests` (maximum
initial checks plus restart replacements), and `lint_model_calls:0`. Locally
refused tests contribute zero planned initial work. Include provisional cache
fallback work in the ceiling because a changed interpreter identity can require
execution. This is a bound for this invocation, not a new spending authority.

Export `checkPlanResults(plan,rows)` returning null for absent/invalid plans,
otherwise `{target,baseline,guidance}`. Each group has `tests`, `passed`,
`failures`, `unresolved` (test paths) and `state` (`passed`, `failed`, `not_run`,
or `none`). Only all selected rows passing gives passed; omitted rows remain
unresolved. Use canonical public outcome projection. Local prerequisites that block a full batch take priority in guidance: name each code, path and field,
and tell the owner to repair the interface or bound and run a fresh check.
These are known local problems; saved reads and retries cannot repair them.
Without prerequisites, failed target work takes priority in guidance. Target passes with baseline failures name those tests for
owner handoff, retain the failed full batch and forbid retrying unchanged target
checks as a repair. Unresolved work directs reading the saved batch. Never
upgrade a full result or change approval/publication rules.

Export `checkPlanLines(plan)` for one text plan: list Story roles, reasons and
closures, call estimate and ceiling, and named prerequisites. Export
`checkPlanResultLines(result)` for separate target/baseline states and guidance.

The partial Runtime surface below covers `checkPlanResults` for a valid reduced
plan and rows with a test path and state. Scope intake, Git/source capture,
invalid-plan rejection, rich legacy outcome records and text rendering remain
native-test obligations. The partial surface supplies no proof of those effects.

## Dependencies

- [Preflight and capture](runtime-preflight.prompt.md): required for source
  selection, dependency closure and interface reads.
- [Workspace authority](runtime-workspace.prompt.md): required for permitted
  ownership metadata reads, including deleted paths in the comparison base.
- [Result outcome](runtime-outcome.prompt.md): required for public row states.
- [File owner lookup](../file-owner.prompt.md#generated-from-header): required for
  the header rule.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"64079bfd67cc5f2124b4ea5cb731a36dd451f66cf4472a975d5c1ef1ba59432b","kind":"partial","entries":[{"operation":"checkPlanResults","input_schema":{"type":"object","properties":{"plan":{"type":"object","properties":{"schema_version":{"type":"string","enum":["pdd.check-plan.v1"]},"stories":{"type":"array","items":{"type":"object","properties":{"role":{"type":"string","enum":["target","baseline"]},"tests":{"type":"array","items":{"type":"string"}}},"required":["role","tests"],"additionalProperties":false}}},"required":["schema_version","stories"],"additionalProperties":false},"rows":{"type":"array","items":{"type":"object","properties":{"test":{"type":"string"},"state":{"type":"string","enum":["passed","failed","refused","not_run","unknown","running"]}},"required":["test","state"],"additionalProperties":false}}},"required":["plan","rows"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"target":{"type":"object","properties":{"tests":{"type":"array","items":{"type":"string"}},"passed":{"type":"array","items":{"type":"string"}},"failures":{"type":"array","items":{"type":"string"}},"unresolved":{"type":"array","items":{"type":"string"}},"state":{"type":"string","enum":["passed","failed","not_run","none"]}},"required":["tests","passed","failures","unresolved","state"],"additionalProperties":false},"baseline":{"type":"object","properties":{"tests":{"type":"array","items":{"type":"string"}},"passed":{"type":"array","items":{"type":"string"}},"failures":{"type":"array","items":{"type":"string"}},"unresolved":{"type":"array","items":{"type":"string"}},"state":{"type":"string","enum":["passed","failed","not_run","none"]}},"required":["tests","passed","failures","unresolved","state"],"additionalProperties":false},"guidance":{"type":"string"}},"required":["target","baseline","guidance"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```

</details>
