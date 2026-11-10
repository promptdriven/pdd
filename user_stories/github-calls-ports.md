# Count, budget and cache GitHub calls through Runtime ports

I can classify `gh` calls, maintain repository ledgers, ETag caches and floor guards, and compute usage, budget and status lines through declared ports and blobs.

```pdd-boundary
prompts/cli/github-calls.prompt.md
```

## Acceptance criteria

1. `githubCall`, `githubPurpose`, `githubRepository`, `githubReply`, `githubEntry`, `githubStateRoot` and `githubFullLastPage` classify normal inputs and return their fallback values for non-matching inputs.
2. `githubLedger` (`record`, `read`, `compact`) and `githubMachineEntries` record, read and compact repository ledger entries and skip invalid lines or missing directories.
3. `countGithubCalls` and `nativeGithubCounter` forward successful calls and record ledger and cost entries, and raise `exec-failed` when the underlying command exits nonzero.
4. `githubUsage`, `githubBudgetSettings`, `githubBudget` and `githubStatusLine` compute hourly counts, budget states (`normal`, `low`, `reserve`) and status lines, falling back to defaults for invalid settings.
5. `githubEtagCache` (`get`, `set`, `save`) and `githubFloorGuard` (`observe`, `blocked`) manage cached ETags and rate-limit floor blocking across normal and missing/unblocked cases.
