# Compatibility and lint display

Own `src/lint-compatibility-display.mjs`; export pure module functions
`describeCompatibility({ label, compatibility, clientAdvice = null, details = false })`
and `describeLintDiagnostics({ problems, localOnly = false })`, each returning a
fresh `{ text }`. This module formats the PDD interpreter's compatibility report
and lint diagnostics for terminal text while keeping JSON payloads and admission
decisions untouched. Preserve all supplied objects and arrays without mutation.
Neither function performs I/O, adds terminal styling, or reclassifies verdicts.

## Compatibility formatting (`describeCompatibility`)

`label` names the cleaned display scope (for example `tests/place-order.json` in
`pdd test` or `place-order / tests/place-order.json` in `pdd lint`).
`compatibility` carries `reported` (an object or `null`), `state`, `association`
and `issue` (a string or `null`). Optional `clientAdvice` is `{ owner, next_step }`
or `null` (default `null`). Optional `details` is a Boolean (default `false`).

Return `{ text }` with newline-separated lines and no trailing newline:

- **Detailed mode (`details` is `true`):**
  1. ``Compatibility (${label}): ${JSON.stringify(compatibility, null, 2)}``
     (preserving each object's supplied key order with 2-space indentation).
  2. Only when `clientAdvice` is non-null:
     ``  Client advice: ${JSON.stringify(clientAdvice)}`` (compact JSON, preserving
     supplied key order).

- **Default plain-text summary (`details` is `false`):**
  1. Always emit exactly one single `Compatibility (${label}): …` line, never
     multiline JSON:
     - **Structured report (`compatibility.reported` is an object with arrays
       `operations` and `edges`):**
       Let `items = [...compatibility.reported.operations, ...compatibility.reported.edges]`.
       - `stepCount`: count of distinct `item.selection.step_id` values across
         `items`, formatted as `1 step` when 1, else `${stepCount} steps`.
       - `opCount`: `compatibility.reported.operations.length`, formatted as
         `1 operation` when 1, else `${opCount} operations`.
       - `edgeCount`: `compatibility.reported.edges.length`, formatted as
         `1 edge` when 1, else `${edgeCount} edges`.
       - `execModes`: distinct `item.execution_mode` values across `items` in
         first-seen order joined by `, `, or `none` when `items` is empty.
       - `resModes`: distinct `item.resource_mode` values across `items` in
         first-seen order joined by `, `, or `none` when `items` is empty.
       - `engine`: `unknown` when `compatibility.reported.engine_build === 'unknown'`,
         else `compatibility.reported.engine_build.slice(0, 12)`.
       - Start with:
         `Compatibility (${label}): ${compatibility.state} (association ${compatibility.association}); ${stepCount} (${opCount}, ${edgeCount}); execution ${execModes}; resources ${resModes}; complete ${compatibility.reported.complete}; engine ${engine}`
       - If `compatibility.issue` is a nonblank string, append
         `; issue ${compatibility.issue}`.
       - Let `nonSupported` be the distinct `item.reason_code` values across
         `items` where `item.verdict !== 'supported'`, in first-seen order; if
         nonempty, append `; non-supported: ${nonSupported.join(', ')}`.
       - End the line with `.`.
     - **Absent, malformed or conflicting report (`compatibility.reported` is
       `null` or lacks `operations`/`edges` arrays):**
       - Start with:
         `Compatibility (${label}): ${compatibility.state} (association ${compatibility.association})`
       - If `typeof compatibility.reported?.complete === 'boolean'`, append
         `; complete ${compatibility.reported.complete}`.
       - If `typeof compatibility.reported?.engine_build === 'string' && compatibility.reported.engine_build.length > 0`,
         append `; engine ${compatibility.reported.engine_build === 'unknown' ? 'unknown' : compatibility.reported.engine_build.slice(0, 12)}`.
       - If `compatibility.issue` is a nonblank string, append
         `; issue ${compatibility.issue}`.
       - End the line with `.`.
  2. Only when `clientAdvice` is non-null:
     `  Client advice (${clientAdvice.owner}): ${clientAdvice.next_step}`

## Lint diagnostic formatting (`describeLintDiagnostics`)

`problems` is an ordered array of lint diagnostic objects; optional `localOnly`
is a Boolean (default `false`). When `problems` is empty, return `{ text: "" }`.

Partition `problems` while preserving relative input order within each group:

1. `blocking`: every item where `item.severity !== 'warning'` (including items
   whose `severity` is `"error"`, `null` or omitted).
2. `advisories`: every item where `item.severity === 'warning'`.

Emit each nonempty group in order (`blocking` first, `advisories` second):

- Heading for `blocking`:
  `Local lint problems:` when `localOnly` is `true`, else
  `Lint problems (from the PDD interpreter):`.
- Heading for `advisories`:
  `Local lint advisories:` when `localOnly` is `true`, else
  `Lint advisories (from the PDD interpreter):`.
- Under its heading, for each item in the group emit
  ``  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}``,
  followed on the next line by ``    ${item.hint}`` when `item.hint` is a
  nonblank string.

Join all emitted lines with `\n` and no trailing newline.

## Dependencies

None. This pure formatter uses only its explicit arguments and standard string
and JSON formatting.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"296af6a05e54afc9b5bc1554d97f2b00e7b02256bcb3df5bc46608254066ecd3","entries":[{"operation":"describeCompatibility","input_schema":{"type":"object","properties":{"label":{"type":"string"},"compatibility":{"type":"object","properties":{"state":{"type":"string"},"association":{"type":"string"},"issue":{"oneOf":[{"type":"string"},{"type":"null"}]},"reported":{"oneOf":[{"type":"object","properties":{"schema_version":{"type":"string"},"capability_version":{"type":"string"},"engine_build":{"type":"string"},"complete":{"type":"boolean"},"verdict":{"type":"string"},"provider_calls":{"type":"integer","minimum":0},"resource_calls":{"type":"integer","minimum":0},"source":{"oneOf":[{"type":"object","properties":{"scenario_sha256":{"type":"string"},"closure_sha256":{"type":"string"},"files":{"type":"array","items":{"type":"object","properties":{"path":{"type":"string"},"sha256":{"type":"string"}},"required":["path","sha256"],"additionalProperties":false}}},"required":["scenario_sha256","closure_sha256","files"],"additionalProperties":false},{"type":"null"}]},"diagnostics":{"type":"array","items":{"type":"object","properties":{"code":{"type":"string"},"path":{"oneOf":[{"type":"string"},{"type":"null"}]},"section":{"type":"string"}},"required":["code","path","section"],"additionalProperties":false}},"operations":{"type":"array","items":{"type":"object","properties":{"selection":{"type":"object","properties":{"step_id":{"type":"string"},"node_id":{"type":"string"},"prompt_path":{"type":"string"},"operation":{"type":"string"}},"required":["step_id","node_id","prompt_path","operation"],"additionalProperties":false},"feature":{"type":"string"},"binding_kind":{"type":"string"},"resource_mode":{"type":"string"},"evaluator_mode":{"type":"string"},"execution_mode":{"type":"string"},"verdict":{"type":"string"},"reason_code":{"type":"string"},"client_advice":{"type":"object","properties":{"owner":{"type":"string"},"next_step":{"type":"string"}},"required":["owner","next_step"],"additionalProperties":false}},"required":["selection","execution_mode","resource_mode","verdict","reason_code"],"additionalProperties":false}},"edges":{"type":"array","items":{"type":"object","properties":{"selection":{"type":"object","properties":{"step_id":{"type":"string"},"node_id":{"type":"string"},"prompt_path":{"type":"string"},"operation":{"type":"string"},"edge":{"type":"object","properties":{"edge_id":{"type":"string"},"kind":{"type":"string"},"call_operation":{"type":"string"},"target_node_id":{"type":"string"},"target_path":{"type":"string"},"target_operation":{"type":"string"},"resource_operation":{"type":"string"}},"required":["edge_id","kind","call_operation","target_node_id","target_path","target_operation","resource_operation"],"additionalProperties":false}},"required":["step_id","node_id","prompt_path","operation","edge"],"additionalProperties":false},"feature":{"type":"string"},"binding_kind":{"type":"string"},"resource_mode":{"type":"string"},"evaluator_mode":{"type":"string"},"execution_mode":{"type":"string"},"verdict":{"type":"string"},"reason_code":{"type":"string"},"client_advice":{"type":"object","properties":{"owner":{"type":"string"},"next_step":{"type":"string"}},"required":["owner","next_step"],"additionalProperties":false}},"required":["selection","execution_mode","resource_mode","verdict","reason_code"],"additionalProperties":false}}},"required":[],"additionalProperties":false},{"type":"null"}]}},"required":["reported","state","association","issue"],"additionalProperties":false},"clientAdvice":{"oneOf":[{"type":"object","properties":{"owner":{"type":"string"},"next_step":{"type":"string"}},"required":["owner","next_step"],"additionalProperties":false},{"type":"null"}]},"details":{"type":"boolean"}},"required":["label","compatibility"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"errors":[]},{"operation":"describeLintDiagnostics","input_schema":{"type":"object","properties":{"problems":{"type":"array","items":{"type":"object","properties":{"code":{"oneOf":[{"type":"string"},{"type":"null"}]},"path":{"oneOf":[{"type":"string"},{"type":"null"}]},"section":{"oneOf":[{"type":"string"},{"type":"null"}]},"message":{"oneOf":[{"type":"string"},{"type":"null"}]},"hint":{"oneOf":[{"type":"string"},{"type":"null"}]},"severity":{"oneOf":[{"type":"string"},{"type":"null"}]},"pointer":{"oneOf":[{"type":"string"},{"type":"null"}]},"source":{"oneOf":[{"type":"string"},{"type":"null"}]},"rule":{"oneOf":[{"type":"string"},{"type":"null"}]},"local_findings":{"type":"array","items":{"type":"object","properties":{"code":{"type":"string"},"section":{"type":"string"},"message":{"type":"string"}},"required":["code","message"],"additionalProperties":false}}},"required":["code"],"additionalProperties":false}},"localOnly":{"type":"boolean"}},"required":["problems"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":4},"conventions":[]}
```
</details>
