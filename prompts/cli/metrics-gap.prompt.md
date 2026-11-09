# Metrics capture gap fallback

`src/metrics-gap.mjs` records an incomplete coverage observation for a repository issue when ordinary metrics identity or delivery fails. Store only the repository, issue, observation time and generated event identity; do not store paths, text, credentials or conversation. Write a new private file, sync its bytes, atomically publish it and sync the directory. Return failure to the caller if storage is unavailable; callers warn and continue their ordinary operation. The metrics command replays valid saved gaps. This fallback is evidence of missing coverage, never a workflow gate.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "draft",
  "prose_sha256": "b3cc89519a3a85eb877a0476ae6a02d6dbe73c8caa3b9109f83e27ada09696cd",
  "reason": "Private durable publish with fsync and atomic rename requires native evidence. Native evidence owners: test/metrics-workflow-storage.integration.test.mjs, test/metrics-selector.integration.test.mjs."
}
```
</details>
