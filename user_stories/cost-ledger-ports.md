# Local issue cost ledger ports

I can check `prompts/cli/cost-ledger.prompt.md` with declared blob, directory, process, clock and compute ports.

```pdd-boundary
prompts/cli/cost-ledger.prompt.md
```

## Acceptance criteria

1. `recordCostGithub` appends a timestamped JSONL entry to `github-cost.jsonl` in the run directory via `files.read` and `files.write`, and throws `Error` when `runDir` or `entry.at` is invalid.
2. `captureClosedCi` reserves `cost-ci-N.json` via `files.stat` and `files.write`, queries `gh api` via `exec.execFile` for closed or merged PR workflow runs, writes `{attempted: true, minutes, complete}`, and throws `Error` when the run input is invalid.
3. `captureCosts` reads Claude or Codex session transcripts, audit directories via `fs.readdir`, `github-cost.jsonl`, and `cost-ci-N.json`, hashes account and session identities via `compute.hash_utf8`, computes person waiting minutes and outcome, and throws `Error` when `run` is invalid.
4. `applyCostMeasurement` records suite minutes, active person minutes, and explicit outcomes once per measurement id, ignores identical retries, and throws `Error` on invalid input or measurement id conflicts.
5. `costReport` and `costStatusLines` aggregate 1-day and 7-day totals, coverage, and merged-issue P50/P90 percentiles and format the status summary text, throwing `Error` on invalid inputs.
