# Check scope and interpreter call plan

Own `src/runtime/runtime-check-plan.mjs`. Before a full Check, explain its scope and
bounded work so an owner can distinguish target work from baseline obligations.
Preserve ordinary full checking, its exit code and required full-pass gates.
This is local planning, not approval or proof of a baseline defect's age or owner.

Export `buildCheckPlan({root,found,selected,rows=[],full,base,affected=false,allowMissingInterfaces=false}, ports={})`.
The optional base is the unique workflow run's saved base SHA; otherwise use HEAD.
Read tracked changes against that base and untracked files through `ports.git`
(default a local Git process; NUL-delimited paths). Include staged, unstaged and
committed run changes. On an unavailable comparison, classify all selected
Stories as targets with an explicit conservative reason. A named selection is
always target work. In a full selection with known changes, intersect each
Story's captured upload closure with changed paths. Capture via `ports.capture`
(default the canonical capture owner, forwarding `allowMissingInterfaces: true` when enabled), grouping every selected test variant.
Changed tests, Stories and transitive dependencies affect that Story. Translate
changed implementation paths to their owning prompts through every Generated-from
header that the shared [header reader](file-owner.prompt.md#generated-from-header)
finds, and through the binding inventory when declared. For a deleted
implementation, read the same owner headers from the comparison base revision. Apply workspace
exclusions before reading base metadata; excluded paths cannot affect ownership.
If permitted metadata cannot prove a deleted path's owner, retain the selected
Stories as conservative targets, even when another change already establishes a
target. Never classify uncertain deleted ownership as unrelated baseline work.
In affected mode classification controls dispatch. Conservatively target all
Stories for changed `pdd-source.json`, `pdd-workspace.json` or binding inventory;
an unresolved changed implementation owner; or an unavailable old/new ownership
or safe-link target relationship. Use permitted old and new owner metadata for
modified implementations. A changed safe link target affects every captured
consumer. A missing association is not proof of independence; fall back without
reading excluded metadata. Retain workspace and fixture exclusions. Renames are
deletion plus addition; removed Stories/tests do not remove remaining full-check
obligations.
If no target can be established,
retain all Stories as targets, stating that scope is conservative. Never infer
unrelated status from an unavailable closure.

Return `schema_version:"pdd.check-plan.v1"`, `full` (boolean), `base` (comparison
revision), `changed_paths` (sorted paths or null), `stories` (selection order),
`calls`, and `prerequisites`. Each Story has `story_path`, `tests` (all selected
test paths), `role` (`target` or `baseline`), `reason`, `affected_paths`, and
`dependency_closure` (sorted captured paths). Baseline means unrelated to the
known changes, still required by full-pass gates; it does not claim a pre-change pass.
Each prerequisite is `{code,path,field}`. Deduplicate these in discovery order.

Inspect every executable entry and nested call independently of other preflight
failures. Missing/unreadable interfaces, absent or nonpositive integer
max_model_calls, undefined call max_calls and recursive calls produce named
prerequisites. When `allowMissingInterfaces` is true, an `interface-missing`
prompt records no `/interface` prerequisite and contributes conservative call
cost `1` plus transitive declared Markdown `.prompt.md` dependency costs
(`promptMarkdownTargets`), ignoring prose-only dependency cycles as
non-recursive while still recording prerequisites on malformed, unbounded or
recursive embedded Runtime interfaces reached from it. Native-only entries need no interpreter bound. Any prerequisite
makes `calls.estimated` and `calls.maximum` null. A full Check with any such
prerequisite sends no paid Check, including otherwise ready Stories.
With affected=true, bound and inspect only rows in `selectCheckTests(plan,
{affected:true}).tests`, while retaining the complete Story classification.
An empty rows input permits classification without dispatch preflight. Revalidate
the locally classified scope before dispatch; if source drift changes its
membership, restart local planning conservatively before any paid call.

Export pure `estimateCheckCalls({prompts=[],rows=[]})` returning `{calls,
has_external_resources,prerequisites}` for supplied prompt summaries (`{path,
kind="full",error,max_model_calls,resource_operations,calls:[{target,max_calls}]}`)
and dispatch rows (`{test,state,max_calls,steps:[{entry_path}]}`). Inspect every
step in `rows` in order even when `row.state !== "ready"`. An executable prompt
(`kind` other than `native-only`) estimates `1 + resource_operations`, plus
`max_calls * (callee_estimate + 1)` for each entry in `calls` with a positive
safe-integer `max_calls` whose target resolves to a non-recursive executable
prompt (`callee_estimate > 0`), counting the caller's continuation turn after
each child call returns. A `native-only` prompt estimates `0`, needs no
`max_model_calls` bound and adds no external-resource presence. Record
`{code:prompt.error ?? "interface-missing",path,field:"/interface"}` for a
missing or unreadable prompt interface, `{code:"undefined-call-bound",path,
field:"/limits/max_model_calls"}` when an executable prompt lacks a positive
safe-integer `max_model_calls`, `{code:"undefined-call-bound",path,
field:"/calls/<index>/max_calls"}` when `call.max_calls` is not a positive safe
integer, and `{code:"recursive-call-bound",path,field:"/calls"}` when `calls`
revisits a prompt on the active call stack (contributing `0`).
`has_external_resources` is `true` iff any reachable non-recursive executable
prompt across inspected steps has `resource_operations > 0`.

`calls` has `estimated` (sum over `state === "ready"` rows of
`Math.min(row.max_calls, step_sum)`; a conservative estimate before cache reuse),
`maximum` (sum over `state === "ready"` rows of `row.max_calls * 2`, including
the one permitted restart replacement), `check_requests` (`2` per `state ===
"ready"` row), and `lint_model_calls:0`. Record `{code:"undefined-call-bound",
path:row.test,field:"/max_calls"}` when a `ready` row lacks a positive
safe-integer `max_calls`. Locally refused or non-ready tests contribute zero
planned initial work (`0` to `estimated`, `maximum` and `check_requests`). Any
prerequisite sets `calls.estimated` and `calls.maximum` to `null` while retaining
`check_requests` and `lint_model_calls:0`. `buildCheckPlan` applies these same
step-cost, prerequisite and `calls` rules to repository interfaces while keeping
the plan's top-level keys unchanged. Include provisional cache fallback work in
the ceiling because a changed interpreter identity can require execution. This is
a bound for this invocation, not a new spending authority.

Export `checkPlanResults(plan,rows)` returning null for absent/invalid plans,
otherwise `{target,baseline,guidance}`. Each group has `tests` (sorted unique
test paths for that role), `passed`, `failures`, `unresolved` (test paths) and
`state` (`passed`, `failed`, `not_run`, or `none`). Only all matching rows
passing gives `passed`; any `failed` row gives `failed`; otherwise a test is
`unresolved` (including `refused`, open or omitted rows), giving group `state`
`not_run` when `tests` is nonempty and `failures` is empty. Use canonical public
outcome projection. Guidance follows this exact precedence:
1. Full-plan local prerequisites (`plan.full && plan.prerequisites?.length`):
   `"Repair local check-plan prerequisites: <code: path field joined by '; '>. Repair the named interface or call bound, then run a fresh pdd test check. No checks were sent; saved reads and retries cannot repair these local prerequisites."`
2. Target failures (`target.failures.length`):
   `"Repair target failures: <target.failures joined by ', '>. Keep baseline results separate."`
3. Unresolved target work (`target.unresolved.length`): when every test in
   `target.unresolved` has at least one matching row in `rows` and every
   matching row's canonical public outcome state is `refused`, return
   `"Inspect refused target checks: <target.unresolved joined by ', '>. Follow each refusal Fix or Next step, then run a fresh pdd test check."`
   Otherwise return `"Read the saved batch for unresolved target checks; do not resend uncertain work."`
4. Target passes with baseline failures or unresolved baseline work: name those
   tests (`[...baseline.failures, ...baseline.unresolved]`) for owner handoff,
   retain the failed or incomplete full batch and forbid retrying unchanged
   target checks as a repair.
5. Otherwise: `"Selected checks passed; required repository gates still apply."`
Never upgrade a full result or change approval/publication rules.

Export `checkPlanLines(plan)` for one text plan: list Story roles, reasons and
closures, call estimate and ceiling, and named prerequisites. Export
`checkPlanResultLines(result)` for separate target/baseline states and guidance.

## Affected selection and saved baseline projection (draft)

Export pure `selectCheckTests(plan, {affected=false}={})`. Return
`{mode,tests,baseline_tests}` with mode `full` or `affected`. Full returns every
plan test and an empty baseline_tests. Affected returns every target Story's
tests and every baseline Story's tests separately. Preserve Story/test discovery
order and deduplicate paths at first occurrence. Include every variant, with no
criterion or budget reduction. If no target exists, return all tests and no
baselines. The client uses this production decision before dispatch preflight,
cache attempts, capture, lint and paid calls; it is not a check-only API.
Keep the complete classification in `check_plan`. For affected dispatch compute
prerequisites and calls from the returned tests only. Report omitted baseline
problems separately; they cannot block target dispatch. A conservative all-test
fallback keeps the ordinary full-check prerequisite stop. The plan's `full`
continues to mean full inventory classification, never proof of full execution.

Export pure `baselineReport({plan,observations,availability,warnings})` for the
client's locally admitted history. Return `{schema_version,availability,tests,
observations,missing_tests,warnings}`, schema_version `pdd.baseline-report.v1`.
The tests are first-occurrence ordered baseline paths. Retain each supplied
observation for those paths, in supplied order, including every older failure
after a later pass or omitted/unsent result. Do not aggregate these into a pass.
missing_tests lists baseline tests with no observation. availability is
`available`, `partial` or `unavailable` for the reader's coverage, not a verdict.
warnings preserves the supplied strings. Empty history never supplies success.

Each observation is `{story_path,test,batch,request_id,evidence_kind,state,reason,
created_at,report_url,source_sha256,currentness,currentness_scope,stage}`. Paths retain
their recorded identity; batch is the original batch ID; request_id is the
original Check ID or null for a local unsent observation. evidence_kind is
`receipt` or `local`; local never attests execution or a pass. state/reason use
the outcome owner's public vocabulary and `{code,message}` or null reason.
created_at is the original batch's ISO timestamp or null if unknown, never the
read time. report_url is its safely validated original link or null;
source_sha256 is its saved source hash or null. currentness is `current`,
`stale` or `unavailable`; currentness_scope is `original-batch`. This compares
the entire original source selection, not the baseline Story alone. Stale batch
source proves no defect age or change to that Story. stage is the admitted
`current`, `pr1` or `before` association, or `unavailable` when not established;
historical stage never attests current-code proof. No owner is inferred.

The partial Runtime surface covers `estimateCheckCalls`, `checkPlanResults`,
`selectCheckTests` and `baselineReport` for valid reduced plans, prompt
summaries and supplied observations. The client must establish their input facts
separately. Scope intake, Git/source capture, invalid-plan rejection, rich
legacy outcome records and text rendering remain native-test obligations. The
partial surface supplies no proof of those effects.

## Dependencies

- [Preflight and capture](runtime-preflight.prompt.md): required for source
  selection, dependency closure and interface reads.
- [Workspace authority](runtime-workspace.prompt.md): required for permitted
  ownership metadata reads, including deleted paths in the comparison base.
- [Result outcome](runtime-outcome.prompt.md): required for public row states.
- [File owner lookup](file-owner.prompt.md#generated-from-header): required for
  the header rule.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"48be7a9a71ca8853e7592736c0d6a8a905141ea87916eb72cc8613a77998e14a","kind":"partial","entries":[{"operation":"estimateCheckCalls","input_schema":{"type":"object","properties":{"prompts":{"type":"array","items":{"type":"object","properties":{"path":{"type":"string"},"kind":{"type":"string","enum":["full","partial","native-only"]},"error":{"type":"string"},"max_model_calls":{"type":"integer"},"resource_operations":{"type":"integer","minimum":0},"calls":{"type":"array","items":{"type":"object","properties":{"target":{"type":"string"},"max_calls":{"type":"integer"}},"required":["target"],"additionalProperties":false}}},"required":["path","resource_operations","calls"],"additionalProperties":false}},"rows":{"type":"array","items":{"type":"object","properties":{"test":{"type":"string"},"state":{"type":"string","enum":["ready","refused"]},"max_calls":{"type":"integer"},"steps":{"type":"array","items":{"type":"object","properties":{"entry_path":{"type":"string"}},"required":["entry_path"],"additionalProperties":false}}},"required":["test","state","steps"],"additionalProperties":false}}},"required":["prompts","rows"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"calls":{"type":"object","properties":{"estimated":{"oneOf":[{"type":"integer"},{"type":"null"}]},"maximum":{"oneOf":[{"type":"integer"},{"type":"null"}]},"check_requests":{"type":"integer","minimum":0},"lint_model_calls":{"type":"integer","enum":[0]}},"required":["estimated","maximum","check_requests","lint_model_calls"],"additionalProperties":false},"has_external_resources":{"type":"boolean"},"prerequisites":{"type":"array","items":{"type":"object","properties":{"code":{"type":"string"},"path":{"type":"string"},"field":{"type":"string"}},"required":["code","path","field"],"additionalProperties":false}}},"required":["calls","has_external_resources","prerequisites"],"additionalProperties":false},"errors":[]},{"operation":"checkPlanResults","input_schema":{"type":"object","properties":{"plan":{"type":"object","properties":{"schema_version":{"type":"string","enum":["pdd.check-plan.v1"]},"stories":{"type":"array","items":{"type":"object","properties":{"role":{"type":"string","enum":["target","baseline"]},"tests":{"type":"array","items":{"type":"string"}}},"required":["role","tests"],"additionalProperties":false}}},"required":["schema_version","stories"],"additionalProperties":false},"rows":{"type":"array","items":{"type":"object","properties":{"test":{"type":"string"},"state":{"type":"string","enum":["passed","failed","refused","not_run","unknown","running"]}},"required":["test","state"],"additionalProperties":false}}},"required":["plan","rows"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"target":{"type":"object","properties":{"tests":{"type":"array","items":{"type":"string"}},"passed":{"type":"array","items":{"type":"string"}},"failures":{"type":"array","items":{"type":"string"}},"unresolved":{"type":"array","items":{"type":"string"}},"state":{"type":"string","enum":["passed","failed","not_run","none"]}},"required":["tests","passed","failures","unresolved","state"],"additionalProperties":false},"baseline":{"type":"object","properties":{"tests":{"type":"array","items":{"type":"string"}},"passed":{"type":"array","items":{"type":"string"}},"failures":{"type":"array","items":{"type":"string"}},"unresolved":{"type":"array","items":{"type":"string"}},"state":{"type":"string","enum":["passed","failed","not_run","none"]}},"required":["tests","passed","failures","unresolved","state"],"additionalProperties":false},"guidance":{"type":"string"}},"required":["target","baseline","guidance"],"additionalProperties":false},"errors":[]},{"operation":"selectCheckTests","input_schema":{"type":"object","properties":{"plan":{"type":"object","properties":{"schema_version":{"type":"string","enum":["pdd.check-plan.v1"]},"stories":{"type":"array","items":{"type":"object","properties":{"role":{"type":"string","enum":["target","baseline"]},"tests":{"type":"array","items":{"type":"string"}}},"required":["role","tests"],"additionalProperties":false}}},"required":["schema_version","stories"],"additionalProperties":false},"affected":{"type":"boolean"}},"required":["plan"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"mode":{"type":"string","enum":["full","affected"]},"tests":{"type":"array","items":{"type":"string"}},"baseline_tests":{"type":"array","items":{"type":"string"}}},"required":["mode","tests","baseline_tests"],"additionalProperties":false},"errors":[]},{"operation":"baselineReport","input_schema":{"type":"object","properties":{"plan":{"type":"object","properties":{"schema_version":{"type":"string","enum":["pdd.check-plan.v1"]},"stories":{"type":"array","items":{"type":"object","properties":{"role":{"type":"string","enum":["target","baseline"]},"tests":{"type":"array","items":{"type":"string"}}},"required":["role","tests"],"additionalProperties":false}}},"required":["schema_version","stories"],"additionalProperties":false},"observations":{"type":"array","items":{"type":"object","properties":{"story_path":{"type":"string"},"test":{"type":"string"},"batch":{"type":"string"},"request_id":{"oneOf":[{"type":"string"},{"type":"null"}]},"evidence_kind":{"type":"string","enum":["receipt","local"]},"state":{"type":"string","enum":["waiting","sent","passed","failed","refused","partial","not run"]},"reason":{"oneOf":[{"type":"object","properties":{"code":{"type":"string"},"message":{"type":"string"}},"required":["code","message"],"additionalProperties":false},{"type":"null"}]},"created_at":{"oneOf":[{"type":"string"},{"type":"null"}]},"report_url":{"oneOf":[{"type":"string"},{"type":"null"}]},"source_sha256":{"oneOf":[{"type":"string"},{"type":"null"}]},"currentness":{"type":"string","enum":["current","stale","unavailable"]},"currentness_scope":{"type":"string","enum":["original-batch"]},"stage":{"type":"string","enum":["current","pr1","before","unavailable"]}},"required":["story_path","test","batch","request_id","evidence_kind","state","reason","created_at","report_url","source_sha256","currentness","currentness_scope","stage"],"additionalProperties":false}},"availability":{"type":"string","enum":["available","partial","unavailable"]},"warnings":{"type":"array","items":{"type":"string"}}},"required":["plan","observations","availability","warnings"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"schema_version":{"type":"string","enum":["pdd.baseline-report.v1"]},"availability":{"type":"string","enum":["available","partial","unavailable"]},"tests":{"type":"array","items":{"type":"string"}},"observations":{"type":"array","items":{"type":"object","properties":{"story_path":{"type":"string"},"test":{"type":"string"},"batch":{"type":"string"},"request_id":{"oneOf":[{"type":"string"},{"type":"null"}]},"evidence_kind":{"type":"string","enum":["receipt","local"]},"state":{"type":"string","enum":["waiting","sent","passed","failed","refused","partial","not run"]},"reason":{"oneOf":[{"type":"object","properties":{"code":{"type":"string"},"message":{"type":"string"}},"required":["code","message"],"additionalProperties":false},{"type":"null"}]},"created_at":{"oneOf":[{"type":"string"},{"type":"null"}]},"report_url":{"oneOf":[{"type":"string"},{"type":"null"}]},"source_sha256":{"oneOf":[{"type":"string"},{"type":"null"}]},"currentness":{"type":"string","enum":["current","stale","unavailable"]},"currentness_scope":{"type":"string","enum":["original-batch"]},"stage":{"type":"string","enum":["current","pr1","before","unavailable"]}},"required":["story_path","test","batch","request_id","evidence_kind","state","reason","created_at","report_url","source_sha256","currentness","currentness_scope","stage"],"additionalProperties":false}},"missing_tests":{"type":"array","items":{"type":"string"}},"warnings":{"type":"array","items":{"type":"string"}}},"required":["schema_version","availability","tests","observations","missing_tests","warnings"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```

</details>
