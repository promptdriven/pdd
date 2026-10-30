# Versioned workflow status JSON

I can consume `pdd workflow status --all --json` as a versioned description of every visible workflow run.

## Acceptance criteria

1. The output is an object with `version` equal to `1` and a `runs` array; each run identifies `owner/repo#N`, repository folder, issue number/title/URL, workflow, agent (`codex` or `claude`), current area and step.
2. Each run reports `waits_for` as `null`, `gate`, `question`, `chat_stopped`, or `startup_failed`; a gate includes its gate id, a question includes its text, and a run with no wait has neither.
3. A stopped chat reports `stopped_reason` as `usage_limit`, `exited`, or `unknown`; an unclear stop is `unknown`, and non-stopped runs report `null`.
4. Each run reports pull request number, URL, draft status and CI state, and reports Stories as passed and total counts or `null` when the count is unknown.
5. Each run reports the current chat's Herdr session, tab and pane, plus `last_change` as the saved millisecond timestamp or `null`.
6. The JSON contains no Try URL or Try link, and an incompatible future contract uses a version other than `1` instead of silently changing the meaning of version `1`.
