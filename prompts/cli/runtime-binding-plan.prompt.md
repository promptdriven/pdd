# Local runtime binding plan

Own `src/runtime-binding-plan.mjs`. Explain resource selection before service
admission without evaluating the program or claiming compatibility. #3135
authorizes additive public exports and Story boundary syntax. Preserve existing
fixtures and expectations; fixtures win by exact `resource.operation` key after
per-step overrides, never by fuzzy matching or a different module's entry name.

Export `runtimeBoundary(storyPath,text)`: return null without a declaration,
otherwise a sorted unique nonempty list of repository-relative `.prompt.md`
paths from Markdown links in the Story's `## Runtime boundary` section. Resolve
relative links from the Story, remove fragments, reject outside paths, URLs,
backslashes, duplicate sections and empty declarations with an Error whose code
is `binding-boundary-invalid`. Only this explicit declaration establishes a
boundary; ordinary English cannot silently exclude an executable dependency.

Export `buildBindingPlan({test,storyText,prompts})`, where test is the selected
{path,storyPath,doc}, and prompts is a Map of safely read path to parsed Runtime
interface. Do no I/O. For each step in order follow its entry and transitive
Runtime calls, once per path. Never treat a Markdown context link as a call.
Require entries and call targets to be in a declared boundary. Return exactly
schema_version (`pdd.binding-plan.v1`), test (path), story (path), boundary (paths
or null), steps, edges and problems. steps contains {step_id,closure} with sorted
executable paths. problems contains {step_id,prompt_path,code} for
out-of-boundary or unavailable interfaces. Do not claim complete closure on a
problem. Resource edges are in step, path and declaration order, each with
{step_id,prompt_path,resource,operation,key,state,candidates,repair}. state is
bound, internal or missing. Built-in key-value/collection/blob/sql/compute
resources need no scenario fixture. An exact simulation binding selects bound;
an invalid/empty fixture.lookup cases array selects missing. Other bindings are
selected but not certified: service admission owns action/schema validity.
Candidates are {kind,name,cause}; list every effective simulation key and every
prompt entry with an operation of the same name. Causes are selected, wrong-name,
wrong-operation, invalid-fixture, out-of-boundary or not-in-dependency-closure.
Prompt entries are explanatory candidates only, not implicit resource bindings.
Never print fixture arguments, world data, results or secrets. Include a missing
candidate list when none exists. Repair is a finite instruction to fix a matching
fixture name/operation, add the exact binding, or declare/check the boundary;
a valid supplied fixture must never get an invented mismatch.

Export `bindingPlanLines(plan)` rendering one line per edge with step, prompt,
key, state, candidate names and causes, plus the repair when missing and all
closure problems. No truncation that hides missing edges.

Export `bindingRefusals(plan,compatibility)`: for every reported missing resource
edge return {step_id,prompt_path,key,cause,candidates,repair}. Use the exact local
edge when present. A selected local fixture gives server-binding-disagreement;
an excluded prompt gives out-of-boundary; an unreached one gives
not-in-dependency-closure. Otherwise retain the candidate mismatch or
binding-missing. A disagreement asks the compatibility owner to inspect fixture
selection; no false pass, invented rejection cause or automatic retry. This is
client evidence, separate from the server verdict.

## Dependencies

None. Callers supply authored Story text and safely parsed interfaces. Use only
standard path arithmetic; all filesystem, Git and service access belongs to callers.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
