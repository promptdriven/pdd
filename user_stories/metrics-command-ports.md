# Metrics report command ports

I can run `pdd metrics` to report queue calculations, export and import ledger bundles, reject historical cutoffs that omit `--snapshot` or `--date`, and refuse unavailable storage.

```pdd-boundary
prompts/cli/metrics-command.prompt.md
```

## Acceptance criteria

1. `runMetrics` with `export FILE` resolves the repository and observation time, calls `store.createBundle`, writes the serialized bundle to `FILE`, and returns `{exitCode: 0}`.
2. `runMetrics` with `--json` collects repository, ledger, selector, and GitHub observations, records live observations through `store.saveEvents`, delegates calculation to `calculate.buildReport`, and writes the JSON report to `output.stdout`.
3. `runMetrics` with a historical `--at` cutoff and neither `--snapshot` nor `--date` returns `{exitCode: 1}` and writes an explanatory diagnostic to `output.stderr` without querying live selector or GitHub ports.
4. `runMetrics` raises `storage-unavailable` when `cwd` is blank.
