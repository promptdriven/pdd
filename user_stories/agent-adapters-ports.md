# Own-agent adapters ports

I can parse agent authentication status, discover installed local agent states through cheap status commands, ask a selected agent for a structured Try reply or log scrubbed failure diagnostics, and run direct agent subprocesses.

```pdd-boundary
prompts/cli/agent-adapters.prompt.md
```

## Acceptance criteria

1. `parseAgentAuthStatus` classifies Codex `Logged in` or `API key configured` on exit 0 as `ready`, Claude `{"loggedIn":false}` on exit 0 or 1 as `signed_out`, and raises `invalid-auth-probe` when `agent` is blank.
2. `discoverAgents` loads launcher definitions, runs help and status probes via `process.run`, maps missing executables to `not_installed`, and raises `invalid-discovery-cwd` when `cwd` is blank.
3. `askAgent` parses a strict JSON reply from `process.run`, preserves `run: true` only when `supportsRun`, `supportsApply`, `apply: true`, and a valid `fill` are present, writes scrubbed failure stderr to `log.append` when a CLI invocation fails, and raises `invalid-agent-request` for an unknown agent.
4. `runAgentProcess` returns `{code, stdout, stderr}` from `process.run` and raises `executable-missing` when `executableMissing` is true.
