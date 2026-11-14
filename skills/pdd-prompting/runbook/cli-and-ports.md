# Runbook: Saved Data, CLI Programs, Prompt Calls, and Fakes

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 5. Saved data

The AI cannot compute a hash. Declare a compute resource with hash_json or hash_utf8, or keep this criterion in native tests. This applies when the program must build or verify a SHA-256 hash: both operations return a lowercase SHA-256. Keep any other digest, for example an HMAC, in native tests. See the [record-id fragment in §21](#verify-a-record-id).

Name each outside port and its argument/result shape clearly in the prompt prose so the PDD interpreter synthesizes and caches the matching resource contract automatically (do not write `<details><summary>Runtime interface</summary>` blocks in `.prompt.md` files). For `todo-cli`, the prose states:
- Read tasks once with key-value port `store.load({ key: "todos" })` returning `{ value }` (`null` when no tasks exist yet, or an array of `{ id: positive integer, text: string, done: boolean }` task records).
- Write updated tasks with `store.save({ key: "todos", value })` returning `{ value }`.
- Shared record schemas may live in a linked contract file (`contracts/*.md`) referenced by `$contract` in scenarios (JSON Schema `$ref` is not allowed).

In the test, `initial_world` is the saved data before step 1. `simulation` connects each operation to the world:
```json
"initial_world": {"kv": {"todos": [{"id": 3, "text": "Buy milk", "done": true}]}},
"simulation": {"store.load": {"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key",
  "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null,
  "result_template": {"value": null}, "result_value_pointer": "/value"}, "store.save": {...}}
```
- `store.save` is the same, with `"action": "key-value.put"`, `"value_argument_pointer": "/value"` and `"result_template": {"value": []}`.
- Say in the prose what `null` means ("no tasks yet"). Keys must be non-empty strings.
- **World paths.** A `world` check reads the world after the step. It starts as `initial_world`. A key-value entry is
  at `<world_pointer>/<key>`: `/kv/todos/1/done` (todo), `/stamps/sam` (Harbor). `port.write` adds its arguments at the
  end of the list at `world_pointer`: `/savedOrders/0/total` (Harbor). For the length of a list: `/kv/books` `count` 4.
- Check "saves nothing" with a `calls` count of 0 (section 8).
- Other actions: `collection.get`, `collection.get-or-null`, `collection.merge` (the world is a list of records),
  `port.write`, `blob.read`, `blob.write`, `blob.stat`, `sql.execute`, `fixture.lookup` and `compute`.
- `port.write` returns its fixed `result_template`. In Harbor, every saved order got the ID 101. Do not check such IDs.

## 6. Command-line programs (`cli`)

Name the program in the prompt’s first heading, for example `# tipjar` (a single safe command name; `pdd`, `node`, `gh` and `git` are reserved).
State the CLI operation's input and output shape clearly in the prompt prose so the interpreter synthesizes its `cli` contract: `{ "argv": string[] }` goes in (plus optional string `"stdin"` when the command reads piped UTF-8 text), and `{ "exit_code": integer, "stdout": string, "stderr": string }` comes out:
- Input: one item for each word, as a shell splits them. `todo add Walk the dog` is `{"argv": ["add", "Walk", "the", "dog"]}`.
- Program exit code 125 is reserved for `pdd simulate` wrapper failures; use another code for program errors.
- Write the rule "Every line written to `stdout` or `stderr` ends with one newline." in the prose.
  Expected text includes the last newline: `"Added #4: Walk the dog\n"`. An empty stream is `""`.

When a legacy or explicit CLI binding declares `"implementation": {"kind": "cli", "command": "node bin/tip.mjs"}` on a tested CLI entry, run `pdd test --target code STORY` to execute the same Story cases locally with 0 AI calls. Use `--json` for structured results.
Each Story result records the current commit. An unsupported step says
`not run` with its reason and cannot make the Story pass. Entries with ports
that cannot be faithfully supplied by this runner are not run; do not replace
their world or call checks with a pass. HTTP and call entries require native
replay tests.

## 7. A prompt that calls another prompt

`checkout` asks `pricing` for a quote. Write the child call directly in plain Markdown so the interpreter synthesizes the prompt-to-prompt call edge:
- Link the child prompt in `## Dependencies`: ``- [Pricing](pricing.prompt.md), runtime use for operation `quote`.``
- Say in the prose how many times to call it: "Call `pricing` operation `quote` at most once."
  Calling a child more times than allowed refuses the check (`graph-result-failure`).
- To pass an error back, name the exact error code in the prose:
  "If `pricing` returns the error `unknown-coupon`, return the error `unknown-coupon`."
- Check the count: `/internal/pricing` equals 1. For an unknown product, it equals 0 (section 8).

## 21. Fake the outside world

Anything outside the code (databases, files, network, clock, randomness and other programs) goes behind an injected port; never call it directly from the decision logic. Name the actual dependency's operations and argument/result fields clearly in the prompt prose so the interpreter synthesizes the resource contract, and supply their replies in the test's `simulation` block. SQL, blob and compute are specialized resource bindings. Preserve existing public functions, factories and methods; do not invent a check-only API.

The examples below specify small JavaScript modules with matching prompt contracts; native execution is reported separately. Their scenarios are synthetic, with exact expected results chosen before execution. The commands run in a clone of pdd (`git clone -b alpha https://github.com/promptdriven/pdd`), from its root; in your own repository, copy the linked files with their paths first. Each command first runs zero-call server lint, then a live prompt check with a hard ceiling; every step requests `gpt-6.1-sol`. A ceiling is not a charge. Native tests establish code behavior separately.

```sh
pdd test fake-database --max-calls 9
# Substitute fake-files, fake-hash, fake-service, fake-decision or fake-factory.
```

Each linked prompt specifies its behavior and port contracts; each scenario includes its starting world, bindings and checks. Copy the complete pair and its Story, then replace the module-owned behavior and expectations from your requirement. Never pass the test or Story as program context.

### Seed a SQL connection

[Module](https://github.com/promptdriven/pdd/blob/main/examples/fakes/database.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/main/examples/fakes/database.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/main/user_stories/fake-database.md) · [Scenario](https://github.com/promptdriven/pdd/blob/main/test/runtime/fake-database.json)

Bind one logical connection to one `world_pointer` for all reads, writes and transactions. Starting rows live under `rows`; SQL executes in real in-memory SQLite. Named scalar argument `id` binds `:id`. Inspect `/database/rows/books`, not SQLite snapshot internals. For dynamic nullable parameters use `statement_argument_pointer` plus JSON-text `parameters_argument_pointer`; never interpolate values into SQL.

```json
{
  "initial_world": {
    "database": {
      "schema": [
        "CREATE TABLE books (id INTEGER PRIMARY KEY, title TEXT NOT NULL)"
      ],
      "rows": {
        "books": [
          {
            "id": 1,
            "title": "Dune"
          }
        ]
      }
    }
  },
  "simulation": {
    "db.find": {
      "action": "sql.execute",
      "world_pointer": "/database",
      "statement": "SELECT title FROM books WHERE id = :id",
      "result_mode": "rows",
      "result_template": {
        "rows": []
      },
      "result_value_pointer": "/rows"
    }
  }
}
```

Passing prompt check (DRAFT): [2/2 checks · 2 AI calls](https://runtime.promptdriven.ai/r/13e8c6dc-532a-4f0c-bb0b-1d1b3671d2a8).

### Read UTF-8 files

[Module](https://github.com/promptdriven/pdd/blob/main/examples/fakes/files.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/main/examples/fakes/files.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/main/user_stories/fake-files.md) · [Scenario](https://github.com/promptdriven/pdd/blob/main/test/runtime/fake-files.json)

Files are keyed by exact POSIX path, each with UTF-8 `content` and `is_symlink`. `blob.write` additionally selects a content argument; `blob.stat` supports exists/is_symlink/size. These fakes never open a host path. Ownership, permissions, races, fsync and atomic rename require explicit ports and native tests.

```json
{
  "initial_world": {
    "files": {
      "/notes/hello.txt": {
        "content": "Hello\n",
        "is_symlink": false
      }
    }
  },
  "simulation": {
    "files.read": {
      "action": "blob.read",
      "world_pointer": "/files",
      "path_argument_pointer": "/path",
      "content_argument_pointer": null,
      "result_template": {
        "content": ""
      },
      "result_value_pointer": "/content"
    }
  }
}
```

Passing prompt check (DRAFT): [1/1 checks · 2 AI calls](https://runtime.promptdriven.ai/r/91df0610-5ecd-4b3b-833f-58a5162d2690).

### Hash exact bytes

[Module](https://github.com/promptdriven/pdd/blob/main/examples/fakes/hash.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/main/examples/fakes/hash.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/main/user_stories/fake-hash.md) · [Scenario](https://github.com/promptdriven/pdd/blob/main/test/runtime/fake-hash.json)

The prompt calls `compute.hash_utf8` with `{text}` and returns `{value}`. The deterministic compute action hashes exact bytes; do not ask the model to calculate a digest. `hash_json` hashes the interpreter's canonical JSON representation and is not interchangeable with an application-specific canonical serializer.

```json
{
  "initial_world": {},
  "simulation": {
    "compute.hash_utf8": {
      "action": "compute",
      "result_template": {
        "value": null
      },
      "result_value_pointer": "/value"
    }
  }
}
```

Passing prompt check (DRAFT): [1/1 checks · 2 AI calls](https://runtime.promptdriven.ai/r/5b26a5ee-1b45-4a79-beb6-ae1dd4c891a3).

### Verify a record id

This is a fragment, not a runnable example. It shows only the two parts that hashing adds. To run it, you also need a Story, a plain Markdown prompt specifying the operation and its `compute.hash_json` port, a scenario with steps and checks, and the native module. "Hash exact bytes" above is a complete example.

`verify(record)` takes `{ "text": string, "id": string }` and returns `{"valid": boolean}`. The prompt prose states that `verify` removes `id`, calls compute port `compute.hash_json` with `{"value": {"text": record.text}}` returning `{"value": string}` (lowercase SHA-256), and compares that digest with `id`.

The `simulation` entry of the scenario:

```json
{"simulation":{"compute.hash_json":{"action":"compute","result_template":{"value":null},"result_value_pointer":"/value"}}}
```

`hash_json` hashes the interpreter's canonical JSON: keys sorted by UTF-16 code units, no spaces, and the interpreter's own spelling of numbers (a subset of RFC 8785). An application's own serializer can give other bytes, for example for floats or non-ASCII keys. To hash exact bytes that the application made, use `hash_utf8`. Native tests must prove that the hash and the serializer match.

Lint accepts this declaration also when the native code hashes inside (for example with Python `hashlib`) and takes no `compute` argument. Keep the native signature. [Module binding coverage](https://github.com/promptdriven/pdd/blob/main/docs/runtime-bindings.md) checks that the prompt can reach its operations. It does not run native hashing. Native tests own that, and a lint pass is not a behavior pass.

### Inject a fixed-answer callback

[Module](https://github.com/promptdriven/pdd/blob/main/examples/fakes/service.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/main/examples/fakes/service.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/main/user_stories/fake-service.md) · [Scenario](https://github.com/promptdriven/pdd/blob/main/test/runtime/fake-service.json)

The native `lookup(service, id)` uses the supplied callback; resource `service.lookup` binds that same boundary. `port.write` appends actual argument objects at `/requests` and returns the fixed `result_template`. Assert both the reply and exact request list. The fixed answer does not prove authentication, transport, timeout handling or any live service effect. Never include credentials in fixtures.

```json
{
  "initial_world": {
    "requests": []
  },
  "simulation": {
    "service.lookup": {
      "action": "port.write",
      "world_pointer": "/requests",
      "result_template": {
        "label": "Available"
      }
    }
  }
}
```

Passing prompt check (DRAFT): [2/2 checks · 2 AI calls](https://runtime.promptdriven.ai/r/53737185-9685-408f-83ca-be9e13c6ae79).

### Return a different port reply on each call

This synthetic example uses one counter for `service.lookup`, starting at zero. Each case has exactly `args`, `call_index`, and `result`: `args` is the literal complete argument object, and `call_index` is a unique positive one-based integer. Other case properties, including `world_result_bindings`, are refused. The counter progresses per operation across steps, so indices must follow that operation's actual call order. The empty result pointer replaces the whole result template with the selected literal result. This binding does not supply a request log or arbitrary world mutations; use an appropriate separate boundary and native tests for effects.

Copy these three files into a repository and use `pdd lint varying-port` for zero-AI fixture/schema admission. Lint does not prove execution behavior or a live service effect.

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

### Override an in-program peer for a failure step

When another prompt in the repository implements a declared port or HTTP operation, the interpreter binds calls to that peer prompt automatically. For an outside port whose reply varies across calls or steps, use top-level `fixture.lookup` with `call_index` above. To simulate a peer failure on one step while other steps still call the real peer prompt, set optional `simulation_overrides` on that step (never `simulation` on a step) to a list of override rows. Each row has exact keys `operation`, `criterion_id`, `failure_quote`, `reason` and `binding`: `criterion_id` must be checked in that step, `failure_quote` must quote an explicit non-negated failure phrase from that criterion's text (such as `"peer is unavailable"`, `"timeout"`, `"offline"` or `"failed"`), and `binding` uses `port.write` or `fixture.lookup` validated against `initial_world`.

```json
{
  "step_id": "peer-down",
  "entry_path": "prompts/service.prompt.md",
  "operation": "resolveItem",
  "input": {"id": "item-7"},
  "simulation_overrides": [
    {
      "operation": "peer.lookup",
      "criterion_id": "AC1",
      "failure_quote": "peer is unavailable",
      "reason": "Simulate unavailable peer catalog returning ok: false.",
      "binding": {
        "action": "port.write",
        "world_pointer": "/peer_requests",
        "result_template": {"ok": false, "label": ""}
      }
    }
  ],
  "checks": [
    {"criterion_id": "AC1", "target": "result", "path": "/label", "op": "equals", "value": "Fallback"}
  ]
}
```

### Separate decide from do

[Module](https://github.com/promptdriven/pdd/blob/main/examples/fakes/decision.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/main/examples/fakes/decision.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/main/user_stories/fake-decision.md) · [Scenario](https://github.com/promptdriven/pdd/blob/main/test/runtime/fake-decision.json)

`decideReply` is a pure public decision over supplied facts; `doLookup` obtains those facts through the injected callback and applies the same rule. The first step proves an unavailable decision without I/O; the second proves the exact effect request and available result. Split only when the native design benefits: SQL and callbacks do not require a split merely to bind them.

```json
{
  "initial_world": {
    "requests": []
  },
  "simulation": {
    "service.lookup": {
      "action": "port.write",
      "world_pointer": "/requests",
      "result_template": {
        "available": true
      }
    }
  }
}
```

Passing prompt check (DRAFT): [4/4 checks · 3 AI calls](https://runtime.promptdriven.ai/r/7cd3364c-d048-46a0-b7a3-41194739405c).

### Keep factory instances with handles

[Module](https://github.com/promptdriven/pdd/blob/main/examples/fakes/factory.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/main/examples/fakes/factory.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/main/user_stories/fake-factory.md) · [Scenario](https://github.com/promptdriven/pdd/blob/main/test/runtime/fake-factory.json)

State the factory operation (returning `{ handle }` for instance type `Greeter`) and instance-method operation (taking `{ handle, ... }`) backed by collection port `instances` (`instances.store({ handle, config })` and `instances.load({ handle })`) in the prompt prose. Store captured state under the executor-issued `handle`; never fabricate a handle or expose closure configuration as a new native method argument. The next scenario step passes `{"$step_result":{"step_id":"create","path":"/handle"}}`. Native callers still receive an object with a method; the handle is its JSON transport identity.

```json
{
  "initial_world": {
    "instances": []
  },
  "simulation": {
    "instances.store": {
      "action": "collection.merge",
      "world_pointer": "/instances",
      "key_argument_pointer": "/handle",
      "value_argument_pointer": "/config",
      "item_key_pointer": "/handle",
      "item_value_pointer": "/config",
      "result_template": {
        "config": null
      },
      "result_value_pointer": "/config"
    },
    "instances.load": {
      "action": "collection.get",
      "world_pointer": "/instances",
      "key_argument_pointer": "/handle",
      "value_argument_pointer": null,
      "item_key_pointer": "/handle",
      "item_value_pointer": "/config",
      "result_template": {
        "config": null
      },
      "result_value_pointer": "/config"
    }
  }
}
```

Passing prompt check (DRAFT): [2/2 checks · 4 AI calls](https://runtime.promptdriven.ai/r/eaa3c792-986a-498c-8970-5d67181d179e).

A prompt pass proves these synthetic cases against the declared fake world. It does not execute the JavaScript module, establish every input/error, approve the prompt, or prove a live effect. If a criterion remains unbound, state the exact missing contract or unsupported effect and the native test needed; never report it as passed.
## Use the Try tools when they are available

The person's own agent can use the stdio server, `pdd mcp`, in the current repository. On the person's intent (for example, "try adding a bookmark with tag news"), use `try_open` to open or reuse the Story's simulation, `try_state` to inspect it, fill the input in `try_run`, `try_check` to check the run against the Story, and `try_save_case` to save a case. Follow the tools' returned input schemas and errors. Each run counts against the simulation's call budget and appears in the Simulator's history; inspect remaining calls before more work.

Saved cases go to a separate `tests/<story>.try-<run-id>.json` with the run's exact starting data; the original scenario stays intact. A recorded case that covers only part of the Story must be completed before `pdd test`, which requires every criterion. Saved cases contain observed results. Review them against the Story with the person before treating them as expected values. Saving or checking a case never approves its expectations or a prompt. If the tools are unavailable, offer `pdd simulate STORY`.
