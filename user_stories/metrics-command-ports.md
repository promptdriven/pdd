# Metrics command ports

The metrics command reads repository identity and saved evidence, uses the shared metrics store and model owners, and writes the report.

```pdd-boundary
prompts/cli/metrics-command.prompt.md
prompts/cli/metrics-store.prompt.md
prompts/cli/metrics-model.prompt.md
```

## Acceptance criteria

1. runMetrics with a daily JSON report reads the saved start event, calls the shared metrics model to calculate activity, and writes the resulting report to stdout.
2. runMetrics rejects --at without --date or --snapshot with exit code 1 and a diagnostic before it reads Git, the ledger, or live sources.
