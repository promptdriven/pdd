# Autopilot machine storage

Own `src/autopilot-store.mjs`. Keep one local storage interface for control,
queue, runs, leases, budgets, costs, events, cache and alerts. These are machine
observations and work, never authority for a shared issue claim or dependency
review. GitHub remains that authority. Preserve caller values, ordering, limits,
identities, guards and best-effort failure policies. The authorized change is
storage representation, atomic local updates and import of existing state.

`openAutopilotStore({root}, ports={})` returns `{transaction, close}`. The native
backend is `ROOT/machine.sqlite`, using Node's built-in `node:sqlite` on Node
22.16 or newer, without a package dependency. Load SQLite only when opening native storage.
If it is unavailable, use the dependency-free snapshot backend. Atomically
select the format with a private `machine-backend` marker before opening either
backend. Concurrent first opens must choose one format even across runtimes.
The `sqlite` dependency port can supply `{DatabaseSync}` or null for native
capability tests; omission loads the built-in module. Keep an existing
fallback snapshot on that backend to avoid splitting state across runtimes.
If a SQLite database already exists but this runtime cannot open SQLite, refuse
instead of switching formats. `ports.openStore({root})` can
replace the backend. Callers use this interface, never SQL or a database handle.
A future team backend implements the same domain operations and must preserve
transaction semantics; it does not add distributed authority through local data.
No Postgres implementation is part of this module.

`transaction(callback)` gives a scoped synchronous transaction with:

- `get(bucket,key)` returns a detached JSON value, or undefined when absent.
- `put(bucket,key,value)` stores a JSON value, replacing that key.
- `remove(bucket,key)` removes that key.
- `list(bucket)` returns `{key,value}` rows ordered by key.
- `append(bucket,scope,value)` adds an independent ordered journal row and
  returns its positive integer sequence. Repeated values remain distinct.
- `entries(bucket,scope?)` returns `{sequence,scope,value}` rows in sequence order.
- `removeEntry(bucket,scope,sequence)` deletes exactly one matching journal row.
- `prune(bucket,scope,before)` deletes journal rows through the inclusive sequence.
- `migrate(identity,read,apply)` runs `read()` only if that identity is not yet
  imported. Undefined means no source yet; otherwise `apply(value)` and the
  import marker commit together. A failed read or apply leaves no marker.

Buckets are the names in the first paragraph. Keys, scopes and migration
identities are strings. Missing keys or append scopes are refused with TypeError
before storage changes; only `entries` permits an omitted scope. Stored values use JSON serialization; undefined top-level
values are refused. Exceptions, failed commits and process death roll back the
whole transaction. A callback cannot return a promise, nest transactions or use
a transaction after its callback ends. `close` releases native resources.
Native writes use SQLite WAL, FULL synchronous durability and a bounded busy
wait. Concurrent SQLite-capable first openers must all be able to initialize
the same unused root and retain their committed operations. Retry transient
SQLite initialization contention within the same five-second wait budget;
other initialization failures propagate without retry. Schema creation is
transactional and versioned; refuse a newer schema
without altering it. Private state folders and database files use 0700 and 0600.
Database errors propagate to the owning caller's existing error policy. A failed
database open must never silently return to stale JSON after import.

`machineJson({root,bucket,key,file},ports={})` returns `read(fallback=null)`,
`write(value)`, `update(callback)`, `clear()` and `exists()`. Each operation
imports that legacy JSON file once, on demand, in the same transaction as its
operation; absent files return the fallback and remain eligible for import.
An imported file is retained unchanged for recovery and is never read again.
Clear retains a tombstone/import marker so retained files cannot resurrect work.
An update receives the current value or null and atomically stores its result.
An optional `invalidLegacy` value allows cache owners to retain their existing
malformed-cache recovery policy. Otherwise malformed JSON fails before import and leaves the file untouched. Directory
scans ignore unrelated files. File I/O uses `ports.fs` with native defaults.

`readAutopilotState(file,fallback=null,ports={})` and
`saveAutopilotState(file,value,ports={})` bind the launcher's stable logical
`H.json` path to the control bucket key `H.json` under its parent root.
`autopilotStateFiles(root,ports={})` returns sorted unique logical filenames
matching twenty lowercase hex digits plus `.json`, from the database and retained
legacy files. Timer arguments, locks and artifact paths still use that logical
path; the launcher payload is read and written through storage. Per-repository
workflow status and durable metrics evidence stay under their existing Git
common directory owners during this incremental migration.

## Dependencies

Node 22.16 or newer supplies `node:sqlite`, filesystem and path facilities.
Native-only: no complete executable Runtime interface or interpreter claims.
