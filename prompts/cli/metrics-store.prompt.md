# Compact metrics ledger

`src/metrics-store.mjs` exports module functions `appendEvents({root, events})`, `readEvents({root})`, `exportMetrics({root, metadata})`, and `importMetrics({root, bundle})`. The ledger retains compact event facts beneath the repository git common PDD state independently of the disposable 200-run index and overwritten workflow status. New records are durable, and backfill records only facts actually evidenced. Preserve these interfaces and effects; storage representation is free.

The [calculator event contract](metrics-model.prompt.md) owns event identity and facts. Identical events imported repeatedly do not inflate the ledger. Conflicting payloads with the same source/id remain visible, rather than choosing a successful result. Validate an entire import and its definition/schema compatibility before writing; reject malformed or incompatible bundles without a partial import. Concurrent append/import must not lose events. An export carries schema and metric-definition versions, repository, export time, timezone, pseudonymous installation/source identity and coverage bounds. A missing machine is a coverage gap, not an empty contributor. Explicit export contains no credentials, prompts, raw chats, raw issue bodies or local paths.

The optional second `ports` argument can supply `ledger.read({root})` and `ledger.write({root, events})`; the first returns `{events}` with optional `sources` and `snapshots`, and the second atomically persists the supplied records. `readEvents`, `appendEvents`, and `importMetrics` return `{events, sources, snapshots}` for native storage; a supplied ledger may initially return `{events}`. `exportMetrics` returns the bundle. Metadata supplies `repo` and `timezone`, and may supply `exportedAt`, `cliVersion`, and coverage bounds; the installation supplies source and capture start. Failures propagate without claiming success. This module is native-only for now: its filesystem, identity, clock and atomic write boundaries have no complete executable Runtime interface. Native tests own those boundaries, including concurrency, permissions and crash behavior.

## Dependencies

[Metrics calculator](metrics-model.prompt.md): required for event identity and facts in authoring, generation and native testing.


Bundles may include `sources`, an array of participating source metadata with source, capture start, coverage, version, definition, export time and timezone. Preserve these records over repeated imports and exports, validating them before any write; older bundles without the array remain readable. The top-level bundle source and each nested source use the same identifier contract before any write. Reject arbitrary prose and local paths in identifiers and facts. Evidence links may have public GitHub comment fragments but no credentials or query strings.

Checker family and checker mode are retained as bounded categorical facts for cross-source agreement. Identifiers and categorical facts use bounded token syntax; selection reasons use bounded category tokens or the fixed unavailable-selector message. A reviewer may use the documented public-comment identity description. Reject URLs targeting localhost or private IP addresses and never accept query strings.

Allow public GitHub check-run references and safe CI check names as reason values. Do not retain raw comment text or private names.

Bundles retain complete selector snapshot headers and member selection events, including empty snapshots, so imports preserve observed membership and its time. Validate repository, identity and event consistency before writing.

Every new export declares `scope: "all-retained-repo-events"`: its events and snapshots are the retained records for the exported repository, without a report date or snapshot filter. Preserve the scope of each imported source through later exports. A v1 bundle or nested source without scope remains readable and its scope remains unknown; do not infer it from a later export. When present, scope must be this supported value. Validate top-level and nested scope before any import write.

Module function `validateSnapshot(snapshot, repository)` is the existing canonical selector-snapshot validator exposed for read-only consumers. With a canonical repository name it validates the complete header, permitted event envelope/data fields and values, timestamp/source bindings, selection type/snapshot/repository consistency and unique issue membership using the same validation as bundle import/export. It returns undefined on success and throws on invalid data, without I/O, mutation, storage, process or network effects. Consumers must not substitute a partial second classifier.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "draft",
  "prose_sha256": "03aca210fe90b23cb346cf52579f1680e654ddb745733a0e560396f4c9ee28b8",
  "reason": "Prompt explicitly says native-only for now; identity, concurrency, permissions and crash behavior remain native. Native evidence owners: test/metrics-store.test.mjs."
}
```
</details>
