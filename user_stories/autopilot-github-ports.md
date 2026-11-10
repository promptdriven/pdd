# Autopilot GitHub settings ports

I can check `prompts/cli/autopilot-github.prompt.md` with declared blob, Git process, GitHub API and short-ID ports.

```pdd-boundary
prompts/cli/autopilot-github.prompt.md
```

## Acceptance criteria

1. `publishAutopilotSettings` reads the default-branch `pdd.json` and open settings PRs through `github.request`, writes the updated `pdd.json` on `main` when direct PUT succeeds (`written`), and returns `not-updated` with the retry command when GitHub refuses with HTTP 500.
2. `checkAutopilotSettings` compares the local `pdd.json` against the default-branch copy on GitHub, returning `different` with the warning and repair command when they differ and `unknown` when the local `pdd.json` is invalid JSON.
