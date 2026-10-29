# Run records

Own `src/workflow-runs.mjs`. A run is one workflow for one issue. Its record is `status.json` in the run folder `<git common dir>/pdd/runs/<issue number>/`. The record remains the internal run state and C3 status shape (`v:1`). This module also owns the read-only JSON returned by `pdd workflow status --all --json`; that public shape is versioned independently as `version: 1`.

## Public status JSON

`pdd workflow status --all --json` returns `{ "version": 1, "runs": [...] }`. It keeps the same filtering and ordering as plain `status --all`: cancelled runs are omitted unless `--cancelled` is supplied; runs are grouped waiting, working, PR open, done and cancelled, then newest first within a group. Reading status may refresh saved PR state as it already does; it never approves, resumes or mutates workflow decisions.

Each run has these fields:

- `identity`: `{ "ref": "owner/repo#N", "repository": "owner/repo", "issue": { "number": N, "title": "...", "url": "https://..." }, "folder": "..." }`.
- `workflow`, `agent` (`codex` or `claude`), `area`, and `step`. `step` is the current step name, or `null` when no step remains.
- `waits_for`: `null`, `"gate"`, `"question"`, `"chat_stopped"` or `"startup_failed"`. For `gate`, `gate_id` identifies the gate. For `question`, `question` contains the person's question. Other wait values have those fields as `null`.
- `stopped_reason`: `"usage_limit"`, `"exited"`, `"unknown"`, or `null`. It is set only when `waits_for` is `"chat_stopped"`; an unclear stop is `"unknown"`.
- `pull_requests`: an array of `{ "number": N, "url": "https://...", "draft": true|false, "ci": "..." }`, preserving the existing PR and CI state. An absent CI state is `null`.
- `stories`: `{ "passed": N, "total": M }`, or `null` when no report can establish a count.
- `chat`: `{ "session": "...", "tab": "...", "pane": "..." }`, with `null` for an unavailable part.
- `last_change`: the saved `updatedAt` time in milliseconds since the Unix epoch, or `null` when absent.

The public JSON contains no Try URL or Try link. Future incompatible field or meaning changes increment the top-level `version`; readers must reject an unknown version rather than guessing. Existing plain-text output, internal `statusView.v:1`, run identity, area and step names, PR semantics, Story counting, Herdr lookup and timestamps remain unchanged.

## Record

Saved fields: `runId`, `workflow`, `repo`, `issue {number,title,url}`, `number`, `root` (worktree), `branch`, `baseBranch`, `sourceRoot`, `commonDir`, `runDir`, `agent`, `configDir`, `startedAt`, `state` (running, waiting, completed, cancelled), `areas`, `area` (index), `done` (step → `{at, summary, area}`), `gate` (`{area, at, kind}` or null; kind `approve`, `approve-pr` (Try before PR 1) or `ask-code`), `question` (`{text, at, area}` or null, from `pdd workflow ask`), `chats` (one per area chat: `{area, tabId, paneId, workspaceId, label, startedAt, session, configDir}`), `decisions`, `changes`, `approvalRecord`, `pr` (one entry per PR: `{stage, number, url, branch, base, state, ci}`), `prBase`, `doneAt`, `prState`, `cancelled`, `warnings`, optional `chatFailure {area, phase, code, message, at}`. The runner owns failure/recovery policy; chat records may retain `startUnconfirmed: true` for an uncertain pane launch.

`writeRun(record, ports)` adds the C3 view, increments `journalSeq`, sets `updatedAt`, and writes the file atomically (temporary file, then rename). It also updates the index of known runs in `<stateDir>/runs.json` (default `~/.local/state/pdd`). An index failure is ignored. `readRun(runDir)` returns the record or null.

An active current-area `chatFailure` takes precedence in `waitingFor`: no approval decisions, a finite reason with the error code, and `pdd workflow open N`. It does not create or clear a gate. Cancelled/completed records ignore stale failure data; normal waiting views return after the runner clears the failure.

C3 view: `stage` (current step, or `approve` at a gate, or `merge` after the last PR), `steps` (each step with area, state done/current/next, times, agent, session and summary), `waitingFor` (`{decisions:['changes'], what: QUESTION}` while a question waits; `{decisions:['approve','changes'], what}` at a gate, with what "Make the code PR now, or stop here and merge PR 1" at the code-or-stop gate, also after PR 1 merged, `{decisions:[], what:'Review and merge the PR on GitHub'}` after the PR, else `{decisions:[], what:null}`), `resumeDecisions`, `waitingDecision`, `herdr`, `stageAgent`, `links:[]`, `controller:null`, `message`.

## Dependencies

- [Workflow runner](../../src/workflow-runner.mjs), runtime use for `status` and `listStatus` behavior and existing plain-text grouping, refresh and filtering.
- [CLI reference](../../docs/cli.md), authoring and verification use for the `workflow status` command and public field definitions.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[{"operation":"main","input_schema":{"type":"object","properties":{"argv":{"type":"array","items":{"type":"string"}}},"required":["argv"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"exit_code":{"type":"integer"},"stdout":{"type":"string"},"stderr":{"type":"string"}},"required":["exit_code","stdout","stderr"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":3},"conventions":[{"path":"/entries/0/input_schema","convention":"cli"},{"path":"/entries/0/result_schema","convention":"cli"}]}
```

</details>
