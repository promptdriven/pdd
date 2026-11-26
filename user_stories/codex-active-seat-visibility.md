# Surface active PDD Cloud seat for pdd-codex

As a developer launching Codex from a PDD Cloud account pool, I want to see which pool seat and rotation mode are active when starting `pdd-codex` and when checking `pdd accounts status`, so that I know whether I am using an owned seat or a shared teammate seat without inspecting temporary files.

## Acceptance criteria

1. Launching `pdd-codex` in an interactive terminal with a leased owned seat "cx4" prints `pdd-codex: using PDD Cloud seat "cx4" (owner, auto-rotate on)` on stderr, and launching with a shared seat "team-cx" owned by "alice" prints `pdd-codex: using PDD Cloud seat "team-cx" (shared by alice, auto-rotate on)` on stderr.
2. Launching `pdd-codex --account cx4` in an interactive terminal prints `pdd-codex: pinned to "cx4" (owner, auto-rotate off)` on stderr, or `pdd-codex: pinned to "cx4" (auto-rotate off)` when access metadata is absent.
3. Launching `pdd-codex` in non-interactive or machine-output modes (`exec`, `exec --json`, `app-server`, `--json`, or without a terminal) prints no startup notice.
4. Running `pdd accounts status` while 2 `pdd-codex` sessions share the seat "team-cx" owned by "alice" and a pinned session uses owned seat "cx4" displays a `Running pdd-codex` section with aligned rows showing `team-cx`, `shared (alice)`, `auto-rotate: on`, `2 live sessions` and `cx4`, `owner`, `auto-rotate: off`, `1 live session`, `[pinned]`.
5. When no `pdd-codex` process is running, `pdd accounts status` omits the `Running pdd-codex` section and reports 0 live sessions.

## What must not change

- Personal `~/.codex/auth.json` stays untouched and zero gateway tokens or credentials appear in notices or status output.
- Non-interactive `pdd-codex exec --json` stdout and stderr omit any startup notice.

## Rules to check

- The startup notice must always be a single line free of control characters and never print for non-interactive launches or machine-output flags. Forbidden: exposing credentials in notices or status output, showing a stale `pdd-codex` lease after all live processes exit, or misclassifying a value flag argument like `-C exec` as a non-interactive subcommand.
