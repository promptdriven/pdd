# External ports, fakes, and CLI programs

Inject outside-world boundaries (databases, filesystem, HTTP, clocks, randomness, generated IDs, child processes) via explicit inputs or `<port>.<op>` operations so `pdd test` fakes them deterministically without hidden globals or prose counters.

## 1. 3-Port Adoption Rule and ambient telemetry carve-out

- **3-Port Adoption Rule:** Adopt an existing legacy module in place with a `.prompt.md` only when it has **`<= 3` external ports** and no direct ORM/SDK singletons. If it has more than 3 ports or tangled SDK state, extract the pure decision core into a small clean PDD module (*Functional Core, Imperative Shell*) and leave the outer wiring as a thin adapter.
- **Ambient telemetry carve-out:** Non-behavioral `logger`, `metrics`, and `tracing` calls do **not** need port mocking unless observability output *is* part of the user contract.
- **Dependency direction:** Never list a `kind: native-only` adapter under `## Dependencies` of a checkable prompt. Invert the dependency so the adapter imports/links the checkable domain prompt.

## 2. Simulation port bindings (`"simulation"` in scenario JSON)

| Outside resource | Binding `action` | Key config fields |
|---|---|---|
| Key-value store | `key-value.get` / `key-value.put` | `world_pointer`, `key_argument_pointer`, `value_argument_pointer`, `result_template`, `result_value_pointer` |
| Record list | `collection.get` / `collection.get-or-null` / `collection.merge` | `world_pointer`, `key_argument_pointer`, `value_argument_pointer`, `item_key_pointer`, `item_value_pointer`, `result_template`, `result_value_pointer` |
| SQL / table store | `sql.execute` | `world_pointer`, `statement`, `result_mode` (`"rows"`), `result_template`, `result_value_pointer` |
| Blob / UTF-8 files | `blob.read` / `blob.write` / `blob.stat` | `world_pointer`, `path_argument_pointer`, `content_argument_pointer`, `result_template`, `result_value_pointer` |
| Deterministic SHA-256 | `compute` (`compute.hash_utf8`, `compute.hash_json`) | `result_template: {"value": null}`, `result_value_pointer: "/value"` |
| Fixed / varying service | `fixture.lookup` | `world_pointer`, `cases: [{args, call_index, result}]`, `result_template: null`, `result_value_pointer: ""` |
| Write-only / error fake | `port.write` | `world_pointer`, `result_template` |

- **One family per `<port>.*` prefix:** never mix e.g. `key-value.get` and `port.write` under the same prefix (`archive.read` + `archive.write`). Keep one family per prefix or split prefixes (`archive_store.read` + `archive_sink.write`). A single `store.load` (`key-value.get`) + `store.save` (`key-value.put`) pair storing one document/list per key is standard for CLI persistence.
- **Entry scope:** bind only `<port>.<op>` operations declared for the entry invoked by that test; unused sibling-entry bindings fail with `unknown-simulation-operation`.
- **Deterministic digests & IDs:** pass deterministic IDs or bind `compute.hash_json` / `compute.hash_utf8` for SHA-256; keep keyed crypto (HMAC, signatures) in native tests.

### Varying replies per call (`fixture.lookup`)

```json
{
  "entry_path": "prompts/varying-port.prompt.md",
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
  "steps": [
    {"id": "first", "op": "lookup", "input": {"id": "book-7"}, "checks": {"1": [["result", "/label", "=", "Available"]]}},
    {"id": "second", "op": "lookup", "input": {"id": "book-7"}, "checks": {"1": [["result", "/label", "=", "Reserved"]]}}
  ]
}
```

### Peer calls and per-step failure overrides

- Link peer `.prompt.md` files under `## Dependencies` with relative Markdown links; assert peer call counts with `["calls", "internal:<peer>", "=", 1]`.
- To inject a failure on one step while other steps call the real peer prompt, use step-level `"simulation_overrides"` (`[{"operation": "peer.op", "criterion_id": "1", "failure_quote": "<un-negated phrase from criterion>", "reason": "...", "binding": {"action": "port.write"|"fixture.lookup", ...}}]`).

## 3. CLI programs and `pdd mcp` Simulator tools

- A CLI program has one program prompt (`# <cmd>`, avoiding `pdd`, `node`, `gh`, `git`) exposing `main({ argv, stdin? }) -> { exit_code, stdout, stderr }` (never exit `125`; end output lines with `\n`).
- Use `pdd sim [STORY] --cli [--shell]` to test a simulated CLI in a terminal, `pdd sim [STORY] --serve [PORT]` for local HTTP routes (`curl`/`fetch`), and `pdd sim --save-last` to append the last observed run for review.
- With `pdd setup`, your coding agent can drive simulations directly through `pdd mcp` (`try_open`, `try_state`, `try_run`, `try_check`, and `try_save_case` only when the person asks).
