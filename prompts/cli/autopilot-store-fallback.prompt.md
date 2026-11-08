# Machine storage without built-in SQLite

Own `src/autopilot-store-fallback.mjs`. Implement `openFallbackStore({root},ports)`
as the same synchronous transaction port as [machine storage](autopilot-store.prompt.md).
This backend exists for Node builds where `node:sqlite` is unavailable, including
early Node 23 builds that require an experimental flag. It uses no dependency.
Use `ROOT/machine-state.json`, a private versioned snapshot of records, journal,
sequence and import identities. An existing fallback snapshot keeps this backend
selected across restarts and runtime upgrades, so processes cannot split local
state across formats. If a SQLite database already exists and SQLite is
unavailable, fail without switching to a stale fallback or legacy files.

Serialize transactions with a permanent private ownership directory and unique
immutable owner leaves containing PID, host and token. Recover only leaves whose
same-host PID is proved dead. Never remove or replace the namespace directory.
Publish a token atomically, then enter only when it is the sole owner. A live,
unknown or malformed owner waits at most five seconds and then refuses. Nested
transactions in one process refuse. Release only the caller's token. A killed
writer leaves a dead token which the next writer can recover.

Read the snapshot after acquiring ownership. Missing means empty version 1;
malformed data or a newer version refuses. Apply the callback in memory, then
write a private unique temporary file, fsync it, rename it atomically and fsync
the parent directory before success. Failure or death before rename retains the
prior snapshot. Records, journal and import markers commit together. Preserve
JSON serialization, detached reads, key order and journal sequence from the
shared port. No mutation is visible until commit. Async, nested and escaped
transactions refuse. The native default remains SQLite when available and no
fallback snapshot exists. This backend has whole-snapshot write cost; make no
SQLite performance claim for it.

## Dependencies

[Machine storage](autopilot-store.prompt.md) is the required interface authority
for generation and native verification. Native Node filesystem, process, crypto,
path and OS facilities supply the local I/O and ownership boundary.
