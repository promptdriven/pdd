As a repository owner, I want one read-only Autopilot readiness command, so that I can fix setup before I start automatic work.

## Acceptance criteria

1. `pdd autopilot doctor` reports each prerequisite on one line with a command and makes no GitHub write or AI call.
2. A missing or signed-out agent sign-in refuses start before state, timers, panes or claims. A different pdd on PATH warns with a fix command.
3. Every other doctor finding warns with a fix command and does not add a start refusal in observe or auto mode. This includes read-only repository permission, disabled merge methods, tools, gh sign-in, setup, interpreter and user scheduler findings. Native start keeps its own guards.
4. Codex and Claude accounts and Linux and macOS receive their own read-only checks and commands.
5. README gives one ordered start path and agrees with USAGE about Node 22.20 or newer and delegated approval limits.
