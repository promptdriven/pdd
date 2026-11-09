As a repository owner, I want one read-only Autopilot readiness command, so that I can fix setup before I start automatic work.

## Acceptance criteria

1. `pdd autopilot doctor` reports each prerequisite on one line with a command and makes no GitHub write or AI call.
2. A stale pdd earlier on PATH and a missing agent sign-in both appear as failures; start shows the same diagnostics and creates no state, timer, pane or claim.
3. Required tool, account, repository, setup, interpreter and user scheduler failures refuse start; draft prompts, unknown usage and logout or sleep advice remain visible warnings.
4. Codex and Claude accounts and Linux and macOS receive their own read-only checks and commands.
5. README gives one ordered start path and agrees with USAGE about Node 22.20 or newer and delegated approval limits.
