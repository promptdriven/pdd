# Local runtime binding plan

Own `src/runtime-binding-plan.mjs`. Explain resource selection before service
admission without evaluating the program or claiming compatibility. #3135
authorizes additive public exports and Story boundary syntax. Preserve existing
fixtures and expectations; fixtures win by exact `resource.operation` key after
per-step overrides, never by fuzzy matching or a different module's entry name.
When `step.simulation_overrides` is a list of override rows, overlay each object
row that has a nonblank string `operation` as `row.operation -> row.binding` in
order without exposing array indices as candidate names; retain plain-object
`step.simulation_overrides` compatibility for existing local fixtures.

Export `runtimeBoundary(storyPath,text,{notes=[]}={})`: return a sorted unique
nonempty list of repository-relative `.prompt.md` paths only from one dedicated
block. The opening line is exactly three backticks followed by `pdd-boundary`;
the closing line is exactly three backticks. Require blank lines or document
ends beside the block. Each content line is a literal repository-relative POSIX
prompt path; no blank lines, links, titles, fragments, whitespace, absolute paths,
backslashes, URL escapes, empty/dot/parent components or other syntax. Only
letters, digits, underscores, hyphens, dots and slashes are accepted in paths.
Narrowing requires LF or CRLF line ends throughout the authored Story. Before
block admission, any bare CR, vertical tab (U+000B), form feed (U+000C), file/group/
record separator (U+001C–U+001E), NEL (U+0085), line separator (U+2028) or paragraph
separator (U+2029) cancels narrowing. Return null with reason
`unsupported-line-ends` and message `boundary not applied: unsupported line ends;
full dependency closure is required`. Never normalize these characters into
narrowing authority. A valid top-level block with CRLF may narrow.
The block must be at top level, outside every other fence, list and HTML block;
container-prefixed or indented blocks cannot narrow. Fail closed if HTML markup
makes its context uncertain, or any additional/unsupported boundary fence is
present. Tag-like, comment, declaration and processing-instruction openers make
context uncertain even without matched closers. Do not use Markdown links, headings or reference definitions as scope
authority. Heading spellings, closing ATX markers, titled links and raw HTML
reference examples cannot remove an edge.

On zero blocks, duplicate blocks, malformed/ambiguous syntax or invalid paths,
return null and append one named note {code,reason,message}. code is
`boundary-not-applied`; reason identifies missing-block, legacy-syntax,
duplicate-blocks, unsupported-syntax, unsupported-line-ends or invalid-path. Legacy Runtime boundary
headings are advisory only: message is `boundary not applied: use the
pdd-boundary block`. If a valid block coexists with a legacy heading, apply only
the block and emit the legacy note; the heading cannot alter membership. Other messages name the reason and say full dependency
closure is required. No partial declaration can narrow. Caller-side safe reading
must validate every member before applying any boundary; an unreadable, unsafe
or outside-resolving member cancels narrowing and adds the same named note with
reason unreadable-path. Keep ordinary required-source failures authoritative.

Export `buildBindingPlan({test,storyText,prompts,dependencyPaths,boundaryState})`,
where test is {path,storyPath,doc}, prompts is a Map of safely read path to parsed
Runtime interface, dependencyPaths is the selected test's full prompt dependency
closure, and optional boundaryState is the caller-validated {boundary,notes}.
Without boundaryState parse the Story locally. Do no I/O. Without an applied
boundary seed every prompt in dependencyPaths as well as each step entry; full
required context remains executable, including its resources. With a boundary
seed all declared members. For each step in order follow transitive Runtime
calls once per path. Never interpret an ordinary Markdown link as an actual call.
Require entries and call targets to be in a declared boundary. Return exactly
schema_version (`pdd.binding-plan.v1`), test (path), story (path), boundary (paths
or null), notes (the named boundary notes), steps, edges and problems. steps contains {step_id,closure} with sorted
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
closure problems and boundary notes. Label an unscoped plan as full dependency
closure. Repairs name the pdd-boundary block. No truncation that hides missing edges.

For the selected step entry, respect its explicit `resource_operations` list
when the whole interface has valid entry scopes: every entry has a distinct-name
list of declared qualified operations, and their union covers all declared
resource operations. An empty list means that entry uses no resources. This
narrows only the selected entry's resource advice, never source closure, boundary
membership, approval or uploaded declarations. Keep the existing conservative
resource advice for other required context modules. Missing, malformed or incomplete
scope declarations, an ambiguous selected entry, or a call in the closure to a
different operation of the same entry module retain the existing all-resource
advice. Runtime remains the admission authority. Do not invent a missing binding
for an unselected entry merely because it shares the selected module (#817).

Export `bindingRefusals(plan,compatibility)`: for every reported missing resource
edge return {step_id,prompt_path,key,cause,candidates,repair}. Use the exact local
edge when present. A selected local fixture gives server-binding-disagreement;
an excluded prompt gives out-of-boundary; an unreached one gives
not-in-dependency-closure. Otherwise retain the candidate mismatch or
binding-missing. A disagreement asks the compatibility owner to inspect fixture
selection; no false pass, invented rejection cause or automatic retry. This is
client evidence, separate from the server verdict.

Callers supply authored Story text and safely parsed interfaces. Use standard
path arithmetic; all filesystem, Git and service access belongs to callers.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"7b4871c63a049ad24f969ec7ff3daeed1cc0e6a6ad8c65114386c8369154342b","entries":[],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
