# Codex account limit ports

I can check `prompts/cli/codex-limits.prompt.md` with a declared subprocess port.

```pdd-boundary
prompts/cli/codex-limits.prompt.md
```

## Acceptance criteria

1. `parseCodexLimits` classifies healthy and limited `codex` rate-limit buckets, converts reached reset seconds to epoch milliseconds using the latest reached window, and returns `unknown` with `null` metrics for malformed windows.
2. `readCodexLimits` spawns `app-server --listen stdio://`, validates the `id: 1` and `id: 2` protocol frames to normalize rate limits, and returns `unknown` with `null` metrics on subprocess or protocol failure.
