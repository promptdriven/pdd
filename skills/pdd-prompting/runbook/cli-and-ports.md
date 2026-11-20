# Runbook: Saved Data, CLI Programs, Prompt Calls, and Fakes

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 5. Saved data

Persist state through injected `<port>.<op>` ports—never hidden globals or prose counters. In scenarios, bind key-value ports under top-level `"simulation"`:
- `key-value.get`: `{"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": null}, "result_value_pointer": "/value"}`
- `key-value.put`: `{"action": "key-value.put", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": "/value", "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": []}, "result_value_pointer": "/value"}`
- Other collection/port actions: `collection.get`, `collection.get-or-null`, `collection.merge` (when the world state is a list of records), `port.write`, `blob.read`, `blob.write`, `blob.stat`, `sql.execute`, `fixture.lookup`, and `compute`.

## 6. Command-line programs (`cli`)

- A CLI has **one** program prompt (`# <cmd>`, avoiding `pdd`, `node`, `gh`, `git`) exposing operation `main`:
  - Input: `{"argv": string[]}` (optional `"stdin": string`)
  - Result: `{"exit_code": integer, "stdout": string, "stderr": string}` (never exit `125`; every written line ends with `\n`)
- Execute CLI Story scenarios directly against real code with 0 AI calls: `pdd test --target code <story>`.

## 7. A prompt that calls another prompt

Link peer `.prompt.md` files under `## Dependencies` with relative Markdown links (`[pricing](pricing.prompt.md)`). The interpreter resolves peer operations automatically; assert peer call counts with `["calls", "internal:<peer>", "=", 1]`.

## 21. Fake the outside world

Pass non-deterministic inputs (clock, RNG, IDs) as operation inputs or injected `<port>.<op>` bindings—never link `kind: native-only` adapters under `## Dependencies` of a checkable prompt.

| Outside resource | Simulation binding `action` | Key config fields |
|---|---|---|
| Key-value store | `key-value.get` / `key-value.put` | `world_pointer`, `key_argument_pointer`, `value_argument_pointer`, `result_template`, `result_value_pointer` |
| Record list | `collection.get` / `collection.get-or-null` / `collection.merge` | `world_pointer`, `key_argument_pointer`, `value_argument_pointer`, `item_key_pointer`, `item_value_pointer`, `result_template`, `result_value_pointer` |
| SQL / table store | `sql.execute` | `world_pointer`, `statement`, `result_mode` (`"rows"`), `result_template`, `result_value_pointer` |
| Blob / UTF-8 files | `blob.read` / `blob.write` / `blob.stat` | `world_pointer`, `path_argument_pointer`, `content_argument_pointer`, `result_template`, `result_value_pointer` |
| Deterministic SHA-256 | `compute` (ports `compute.hash_utf8`, `compute.hash_json`) | `result_template: {"value": null}`, `result_value_pointer: "/value"` |
| Fixed / varying service | `fixture.lookup` | `world_pointer`, `cases: [{args, call_index, result}]`, `result_template: null`, `result_value_pointer: ""` |
| Write-only / error fake | `port.write` | `world_pointer`, `result_template` |

### Return a different port reply on each call

Each case has exactly `args`, `call_index` (unique 1-based integer matching call order across steps), and `result`. Empty `result_value_pointer` replaces `result_template` with the literal `result`.

`prompts/varying-port.prompt.md`:

````markdown
# Varying port

Own `varying-port.mjs`, exporting module function `lookup(service, id)` for string `id`. Call injected port `service.lookup({ id })` once (where `id` is a string and `service.lookup` returns `{ label: string }`) and return `{ label }` unchanged. The service owns outside access.

## Dependencies

None.
````

`user_stories/varying-port.md`:

```markdown
# Varying port

I can look up the same item twice and see each supplied reply.

## Acceptance criteria

1. The first lookup of book-7 returns Available and the second returns Reserved.
```

`test/runtime/varying-port.json`:

```json
{
  "schema_version": "prompt-runtime.program-scenario.v1",
  "story_path": "user_stories/varying-port.md",
  "criteria": [{"id": "AC1", "text": "The first lookup of book-7 returns Available and the second returns Reserved."}],
  "initial_world": {"fixture_counters": {"lookup": 0}},
  "simulation": {
    "service.lookup": {
      "action": "fixture.lookup",
      "world_pointer": "/fixture_counters/lookup",
      "cases": [
        {"args": {"id": "book-7"}, "call_index": 1, "result": {"label": "Available"}},
        {"args": {"id": "book-7"}, "call_index": 2, "result": {"label": "Reserved"}}
      ],
      "result_template": null,
      "result_value_pointer": ""
    }
  },
  "context": [],
  "steps": [
    {"step_id": "first", "entry_path": "prompts/varying-port.prompt.md", "operation": "lookup", "input": {"id": "book-7"}, "checks": [{"criterion_id": "AC1", "target": "result", "path": "/label", "op": "equals", "value": "Available"}], "model": "gpt-6.1-sol"},
    {"step_id": "second", "entry_path": "prompts/varying-port.prompt.md", "operation": "lookup", "input": {"id": "book-7"}, "checks": [{"criterion_id": "AC1", "target": "result", "path": "/label", "op": "equals", "value": "Reserved"}], "model": "gpt-6.1-sol"}
  ]
}
```

### Verify a record id

Do not rely on opaque runtime-generated IDs or ask the model to compute a digest; pass deterministic IDs or bind `compute.hash_json` / `compute.hash_utf8` (`{"action": "compute", "result_template": {"value": null}, "result_value_pointer": "/value"}`) or `fixture.lookup`, and verify persisted records via `world` pointers. Keep non-SHA-256 digests (such as HMAC) in native tests.

### Override an in-program peer for a failure step

Set optional step `simulation_overrides` (never `simulation` on a step) to `[{"operation": "peer.op", "criterion_id": "AC1", "failure_quote": "<non-negated phrase from criterion>", "reason": "...", "binding": {"action": "port.write"|"fixture.lookup", ...}}]` to simulate a peer failure on one step while other steps call the real peer prompt.

### Try tools over `pdd mcp`

The person's own agent can use the stdio server `pdd mcp` in the current repository. On the person's intent, use `try_open` to open or reuse the Story's simulation, `try_state` to inspect it, `try_run` to run an input, `try_check` to check the run against the Story, and `try_save_case` to save a case (only when the person asks). Follow each tool's returned input schema and errors, and inspect remaining session calls before more work.
