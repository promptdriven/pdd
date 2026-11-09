# Offline review and interpreter boundaries

`pdd lint` uploads the selected files to the PDD interpreter with your gh login. It uses
zero AI calls, but needs a network connection and server capacity. A task that permits only
offline work does not permit this command.

| Offline work | What it establishes |
|---|---|
| `pdd test --files [STORY...]` | The selected upload paths, byte sizes and capture safety checks; nothing is sent. |
| `pdd test --fill-hash` | The hashes of draft interfaces; nothing is sent. |
| Read the prompt, Story and test together | Check declared schemas, exact criterion text, dependencies and expected-value ownership. This is an authoring review. |
| Run the repository's ordinary tests | The native behavior those tests exercise. |

Record the actual checks you performed. Offline review is not a server lint pass or an interpreter
behavior verdict. If server access is outside the task's permission, leave those results
unverified. When server access is allowed, `pdd lint` requests complete diagnostics and prints the problems the server reports;
correct them and check again before submitting a behavior check.

The AI cannot compute a hash. Declare a compute resource with hash_json or hash_utf8, or keep this criterion in native tests. This applies when the program must build or verify a SHA-256 hash: both operations return a lowercase SHA-256. Keep any other digest, for example an HMAC, in native tests. See the [RUNBOOK §21 record-id fragment](../RUNBOOK.md#verify-a-record-id) for the resource and simulation entries and the native binding limits.

## Native factories and JSON operations

Factories, constructors and objects of methods can bind through Runtime interface v2:
set `schema_version` to `prompt-runtime.interface.v2`. Declare `instance_types` rows with
`name` and `resource`, where the resource is a declared write-access `collection`.
A factory or method entry declares `instance` with `kind` (`factory` or `method`), `type`
and `path`. The factory path selects its result handle; the method path selects its input
handle. The interpreter issues opaque string handles and keeps the instance state in the
bound collection. Preserve the public factory and method contracts when declaring these
transports. A `copy_out` list of `path` and `post_schema` rows declares observable updates
to selected logical input values when the contract requires them.

Put injected I/O and callbacks behind declared `port` operations. A `port.write` simulation
records arguments in the scenario world and returns the scenario-declared result. Bind
these operations to the actual dependency contract and keep expected values owned by the
Story and test. See [RUNBOOK §5](../RUNBOOK.md#5-saved-data) for saved data and resources.

| Declared simulation | What it covers |
|---|---|
| `sql.execute` | Bounded SQL in a real in-memory SQLite connection, including transactions, commit and rollback. It does not open the application's disk database. |
| `blob.read`, `blob.write`, `blob.stat` | File contents and metadata in a path-keyed scenario world; no host file is opened. |
| `compute.hash_json`, `compute.hash_utf8` | SHA-256 of canonical JSON (`value`) or exact UTF-8 bytes (`text`). These are deterministic compute operations. |
| HTTP fixtures | Exact argument/result cases for declared HTTP operations, without a live network request. |

Keyed cryptography and signatures, process and socket lifecycle, Git effects, DOM typing
and paste, and live effects remain native test obligations. Report those criteria as unbound
by the interpreter simulation; a simulated result does not establish a live effect.

Never invent a fake API only for a check. Use the module's public operations and available
dependency contracts, declare the supported instance and resource bindings, and name any
missing contract or unbound criterion. Report what the prompt tests cover and what the
native tests cover. Neither a passing check nor a simulation approves a workflow gate.

## Read call usage as evidence

A check that pdd never posts has zero check AI calls, including one held behind unfinished lint.
The lint result can remain unknown while that check was not run. `pdd test --read BATCH` reads existing work; only guarded saved-lint continuation or a confirmed one-time service-restarted replacement can send a check. UUID call reads remain GET-only.

For a submitted run, keep the server's accounting result. If it reports unknown usage or
incomplete accounting, a raw `provider_calls: 0` does not prove zero cost. Keep the run's call
ceiling reserved until complete evidence resolves it; do not resubmit the same run to obtain a
number. Share its report with the PDD team.

The runtime-slots snapshot interface binds the actual files.listRecords port. Supplied records can establish listing order and preserved fields. Local exclusive-create races, process death, crash cleanup, private file permissions and CLI dispatch require native tests; no snapshot replay establishes those effects. See the [shared admission plan](../user_stories/PLAN.md#shared-runtime-admission-2631).
