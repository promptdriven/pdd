# Automatic run base ports

I can check `prompts/cli/autopilot-base.prompt.md` with declared configuration and Git/GitHub process ports.

```pdd-boundary
prompts/cli/autopilot-base.prompt.md
```

## Acceptance criteria

1. `selectAutopilotBase` reads `autopilot.base` via `config.readConfig`, validates `refs/heads/BRANCH` via `program.execFile`, and raises `invalid-base-branch` for disallowed branch names such as `HEAD`.
2. `checkAutopilotBase` verifies the PR target, default branch and newest non-draft release ancestry via `program.execFile`, returning exit 0 when `release/next` contains `main` and `v1.2.0` and exit 1 when `release/next` is 2 commits behind `v1.2.0`.
