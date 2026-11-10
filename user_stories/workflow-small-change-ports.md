# Verify small-change request checklists through Runtime ports

I can read `small-change-checklist.json` under `runDir`, verify its `run_id` and Git-content fingerprint, and review checklist rows against an independent issue request inventory.

```pdd-boundary
prompts/cli/workflow-small-change.prompt.md
```

## Acceptance criteria

1. Reading a valid `small-change-checklist.json` under `runDir` whose `run_id` and `source.sha256` match the run and current `replay.sourceFingerprint` returns `status: "recorded"`, preserves item order, and reports `missing-evidence` for a `done` row with blank evidence.
2. Reading a checklist whose `source.sha256` differs from `replay.sourceFingerprint` returns `status: "stale"` with `stale-checklist`, and passing an empty `runDir` fails with `invalid_checklist_run`.
3. Reviewing a checklist against an independent request inventory matches rows by `source`, `request` and `quote`, reports `missing-request` for an omitted request and `unsupported-exclusion` when an excluded item's quote differs from the independent `exclusion_quote`, and rejects an empty `requests` array with `invalid_request_inventory`.
