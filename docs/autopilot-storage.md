# Autopilot machine storage

Autopilot stores machine state in `~/.local/state/pdd/autopilot/machine.sqlite`.
Supported LTS versions from Node 22.16 supply SQLite. Early Node 23 builds
that require a SQLite flag use the dependency-free snapshot backend at
`machine-state.json`. It uses private owner tokens and recovers a killed writer
when the same host can prove its PID is dead. Unknown owners hold the store
until the operator can verify and remove that token. An existing snapshot keeps that backend selected across
runtime upgrades, so processes share one format. It has whole-snapshot write
cost. A runtime without SQLite cannot open an existing SQLite installation;
use a runtime with SQLite for that installation. There is no dependency installation step.
The database and its folder are private. A private `machine-backend` marker
selects one format atomically when several processes first open the store. Each write uses a SQLite transaction,
WAL journaling, FULL synchronous durability and a five-second busy wait.

The store has record buckets for control, queue, runs, leases, budgets, costs,
events, cache and alerts. Journal rows retain independent events and cost rows,
including repeated values. Queue updates, local lease observations, budget
updates and journal appends can commit together through one transaction.
The current GitHub call ledger uses the events journal. Cost producers can use
the costs journal; the store does not infer model use or spending.

The launcher, native dependency commands, worker completion and alert machine
identity all read the same control records. Dependency snapshots and ETags use
cache records. Kept dependency completions use queue records. The machine run
index uses run records and retains its existing 200-entry bound. Full workflow
status and metrics evidence stay in the Git common state directory. Alert
incident files and destination configuration keep their existing locations.

Each old JSON or JSONL record is imported on first use. Its import marker and
records commit together. The old file stays unchanged as a recovery copy.
A restart does not import it again. Clearing a kept completion retains an import
marker, so an old file cannot restore completed work. An interrupted transaction
leaves the prior committed state available. Malformed launcher JSON is reported;
cache owners retain their normal empty-cache recovery policy. An unreadable
database never switches back to old state files.

Use one storage version for the processes that share a state folder. A binary
that reads only the retained JSON files cannot see later database writes. Stop
those processes before using a different storage version. To back up a running
database, use a SQLite-aware backup tool. A stopped database can be copied after
all connections close. Keep recovery copies until the imported state is checked.

GitHub remains the shared authority for claims and dependency reviews. Local
lease observations do not grant ownership on another machine. Local transactions
do not make a GitHub write atomic with a machine-state write; existing intents,
readbacks, guards and reconciliation still handle that boundary.

`src/autopilot-store.mjs` owns SQL. Consumers use `transaction(callback)` and its
record, journal and migration operations. Native adapters accept a `store` port;
the factory accepts an `openStore` port. These ports are the backend seam for
controlled tests and a team service. The present callbacks are synchronous and
must contain local storage work only. A Postgres service will need an asynchronous
transport adapter at this boundary; no Postgres driver or service is included.
Snapshots remain versioned payloads in this stage. Moving their members into
individual records can use the same transaction interface.

Run the bounded native checks from the repository root:

```sh
node --test test/autopilot-store.test.mjs test/autopilot-store-regression.test.mjs
node --test test/github-calls.test.mjs test/github-dependency-snapshot.test.mjs test/github-dependency-snapshot-repair.test.mjs
```

The tests use temporary state, the repository's fake GitHub and fake Herdr,
and controlled child processes. They make no model or live service calls.
