# Run records

Own `src/workflow-runs.mjs`. A run is one workflow for one issue. Its record is `status.json` in the run folder `<git common dir>/pdd/runs/<issue number>/`. The record is the run state and also the status shape that phone clients read (C3, `v:1`).

## Record

Saved fields: `runId`, `workflow`, `repo`, `issue {number,title,url}`, `number`, `root` (worktree), `branch`, `baseBranch`, `sourceRoot`, `commonDir`, `runDir`, `agent`, `configDir`, `startedAt`, `state` (running, waiting, completed, cancelled), `areas`, `area` (index), `done` (step → `{at, summary, area}`), `gate` (`{area, at, kind}` or null; kind `approve`, `approve-pr` (Try before PR 1) or `ask-code`), `question` (`{text, at, area}` or null, from `pdd workflow ask`), `chats` (one per area chat: `{area, tabId, paneId, workspaceId, label, startedAt, session, configDir}`), `decisions`, `changes`, `approvalRecord`, `pr` (one entry per PR: `{stage, number, url, branch, base, state, ci}`), `prBase`, `doneAt`, `prState`, `cancelled`, `warnings`, optional `productMarker` (string), optional `chatFailure {area, phase, code, message, at}`. The runner owns failure/recovery policy; chat records may retain `startUnconfirmed: true` for an uncertain pane launch.

`writeRun(record, ports)` adds the C3 view, increments `journalSeq`, sets `updatedAt`, and writes the file atomically (temporary file, then rename). It also updates the index of known runs in `<stateDir>/runs.json` (default `~/.local/state/pdd`). An index failure is ignored. `readRun(runDir)` returns the record or null.

## Concurrent record updates

Module function `updateRun(runDir, update, ports = {})` synchronously returns the
committed record. `update` is a synchronous callback receiving the latest durable
record and returning the record to save. Reading that record, applying the
callback and publishing its result form one indivisible update for this run,
including across processes. Successful updates of unrelated fields retain both
writers' effects. The callback owns its intended changes; storage does not infer
them from an arbitrary old snapshot.
Keep the ownership algorithm and private representation free.

The callback may mutate its supplied record, but must preserve its run identity
and perform only local state changes. A missing or unreadable existing record,
callback failure or failed publication fails finitely without claiming a commit;
never create an existing run from a stale fallback. Before publication, retain the
previous durable bytes on failure. Always release only this invocation's ownership.
Ownership covers no external Git, GitHub, Herdr or model effects, readiness waits,
journal claim acquisition or nested ordinary save. Storage/ownership effects have
injectable native boundaries with production defaults. Do not reclaim an owner
merely because its record is old.

`writeRun(record, ports)` retains its synchronous signature, supplied-object
mutation and returned record, and its explicit whole-record save capability. Its
publication participates in the same ownership boundary; it cannot interrupt an
`updateRun` between read and commit. It does not infer an untracked caller's intent.
`updateRun` uses the same C3 derivation, sequence, timestamp and best-effort index
semantics as `writeRun`, applied to the record being committed. An index failure
does not undo or misreport that commit.
Neither function reads or writes the delivery journal. The callback binding and
native filesystem concurrency are unbound to the Interpreter; no JSON callback
adapter is part of this API.

Preserve optional `productMarker` when the runner supplies it. Its capture and
PR propagation belong to [the workflow runner](workflow-runner.prompt.md#product-run-association).
An older record without the field stays valid; this module does not infer one.

An active current-area `chatFailure` takes precedence in `waitingFor`: no approval decisions, a finite reason with the error code, and `pdd workflow open N`. It does not create or clear a gate. Cancelled/completed records ignore stale failure data; normal waiting views return after the runner clears the failure.

C3 view: `stage` (current step, or `approve` at a gate, or `merge` after the last PR), `steps` (each step with area, state done/current/next, times, agent, session and summary), `waitingFor` (`{decisions:['changes'], what: QUESTION}` while a question waits; `{decisions:['approve','changes'], what}` at a gate, with what "Make the code PR now, or stop here and merge PR 1" at the code-or-stop gate, also after PR 1 merged, `{decisions:[], what:'Review and merge the PR on GitHub'}` after the PR, else `{decisions:[], what:null}`), `resumeDecisions`, `waitingDecision`, `herdr`, `stageAgent`, `links:[]`, `controller:null`, `message`.

## Selection

- `gitContext(cwd, ports)` returns `{toplevel, commonDir}` (real paths) or null.
- `runForWorktree(cwd, ports)` returns the run whose `root` is the current worktree.
- `resolveRun(ref, {cwd}, ports)` returns `{run}` or `{error}`. `N` looks in the current repository, worktrees included. Outside a repository it uses the index; when several repositories have issue N, it asks for `owner/repo#N`. `owner/repo#N` and issue URLs pick that repository. Without ref: the run of the current worktree, else the only run of this repository that waits for a person, else the only active run; otherwise list the choices.
- `listRuns({cwd}, ports)` returns the runs of the current repository, or all indexed runs outside a repository.
- `allRuns({cancelled}, ports)` returns every run on this machine. It finds the repositories from the run index (`<stateDir>/runs.json`) and the Herdr layout registry (`<stateDir>/herdr-layout/registry.json`, its `repositories[].commonDir`), then reads each `<commonDir>/pdd/runs/<N>/status.json`. With `cancelled` it also reads the renamed `<N>-cancelled-<id>` folders. A repository or file that is gone or unreadable is skipped without an error.
