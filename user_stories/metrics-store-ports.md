# Compact metrics ledger ports

I can read, append, export, and import compact metrics ledger records and validate selector snapshots while deduplicating identical events, keeping conflicting payloads visible, and rejecting malformed records before any write.

```pdd-boundary
prompts/cli/metrics-store.prompt.md
```

## Acceptance criteria

1. `readEvents` reads retained events, sources, and snapshots from `ledger.read`, and raises `invalid-ledger` when the root path is blank.
2. `appendEvents` deduplicates identical events by `source` and `id`, retains conflicting payloads with the same `source` and `id`, persists the updated ledger via `ledger.write`, and raises `invalid-metrics-event` without writing when an event contains a query-string or localhost URL.
3. `exportMetrics` builds a `pdd.metrics.export.v1` bundle with `scope: "all-retained-repo-events"` and installation metadata from `installation.read`, and raises `invalid-export-metadata` without reading the ledger when `repo` or `timezone` is invalid.
4. `importMetrics` unions compatible bundle events, sources, and snapshots into the ledger and raises `invalid-metrics-bundle` before any write when a bundle has an unsupported scope.
5. `validateSnapshot(snapshot, repository)` returns undefined for a canonical snapshot and throws a plain `Error` when its repository or unique issue membership is invalid.
