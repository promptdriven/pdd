# Run records

Own `src/workflow-runs.mjs`. A run is one workflow for one issue. Its record is `status.json` in the run folder `<git common dir>/pdd/runs/<issue number>/`. The record is the run state and also the status shape that phone clients read (C3, `v:1`).

## Owner and projections

The run record is the sole durable workflow/chat owner. The run index, stageAgent, phone view, process lock and assignments are lookup, observation or exclusion views; none can override its chat custody. Persist run-level `layout` custody with repository/run workspace IDs and their initial root tab/pane/terminal IDs, alongside chat IDs; its IDs are live-checked lookup hints and cleanup custody, never authority over contradictory live Herdr identity. Preserve the [runner lifecycle](workflow-runner.prompt.md#chat-lifecycle) fields and positive evidence on every write, deriving index and stageAgent consistently. Missing state on legacy chats is unknown unless explicit saved launch custody derives starting; absence never creates ended evidence. Index repair never changes runId, commonDir, root, native session or workflow progress.

## Record

Saved fields: `runId`, `workflow`, `repo`, `issue {number,title,url}`, `number`, `root` (worktree), `branch`, `baseBranch`, `sourceRoot`, `commonDir`, `runDir`, `agent`, `configDir`, `startedAt`, `state` (running, waiting, completed, cancelled), `areas`, `area` (index), `done` (step → `{at, summary, area}`), `gate` (`{area, at, kind, id, promptSnapshot?}` or null; kind `approve`, `approve-pr` (Try before PR 1) or `ask-code`), `question` (`{text, at, area}` or null, from `pdd workflow ask`), `chats` (one per area chat: `{area, tabId, paneId, workspaceId, label, startedAt, session, configDir, state, evidence?, code?}`), `decisions`, `changes`, `approvalRecord`, `pr` (one entry per PR: `{stage, number, url, branch, base, state, ci}`), `prBase`, `doneAt`, `prState`, `cancelled`, `warnings`, optional `productMarker` (string), optional `replayAdoption` (immutable declaration copy/digest and origin provenance, owned by the [runner](workflow-runner.prompt.md#adopt-an-existing-approved-corpus)), optional `chatFailure {area, phase, code, message, at}`. The runner owns failure/recovery policy; chat records may retain `startUnconfirmed: true` for an uncertain pane launch.

`writeRun(record, ports)` adds the C3 view, increments `journalSeq`, sets `updatedAt`, and writes the file atomically (temporary file, then rename). It also updates the index of known runs in `<stateDir>/runs.json` (default `~/.local/state/pdd`). An index failure is ignored. `readRun(runDir)` returns the record or null.

Preserve optional `home`, a nonempty absolute machine-home path for Codex runs,
through writes, reads and projections. Its selection and legacy fallback belong
to the [runner](workflow-runner.prompt.md#current-codex-login-and-saved-home).
An older record without it remains valid; storage does not infer a home or login.

## Concurrent record updates

Module function `updateRun(runDir, update, ports = {})` synchronously returns the
committed record. `update` is a synchronous callback receiving the latest durable
record and returning the record to save. Reading that record, applying the
callback and publishing its result form one indivisible update for this run,
including across processes. Successful updates of unrelated fields retain both
writers' effects. The callback owns its intended changes; storage does not infer
them from an arbitrary old snapshot.
Ordinary ownership uses `<run folder>/.ordinary-owner` and publishes complete owner
PID, hostname and a unique token atomically. Reclaim only a confirmed dead owner
on the same host. Live, foreign-host, malformed and unverifiable ownership,
including permission-check failures, stays protected; age alone proves nothing.
Release or reclaim only the observed token, so an older owner cannot remove its
replacement. A dead owner's leftover ownership must not prevent cancellation.
Keep the private ownership algorithm free.

Module function `readRunOwnership(runDir, ports = {})` returns `null` when ordinary
ownership is absent, otherwise a snapshot `{path, pid, hostname, token, warning}`.
`path` names `.ordinary-owner`; unavailable PID, hostname or token fields are
`null`. A complete readable owner has `warning: null`; unreadable or malformed
ownership has a finite diagnostic string in `warning`, retaining available facts.
This public read performs no acquisition, recovery, release or durable write.
Its native filesystem binding remains unbound to the Interpreter.

The callback may mutate its supplied record, but must preserve its run identity
and perform only local state changes. A missing or unreadable existing record,
callback failure or failed publication fails finitely without claiming a commit;
never create an existing run from a stale fallback. Before publication, retain the
previous durable bytes on failure. Always release only this invocation's ownership.
Ownership covers no external Git, GitHub, Herdr or model effects, readiness waits,
journal claim acquisition or nested ordinary save. Storage/ownership effects have
injectable native boundaries with production defaults. Contention fails with a
finite diagnostic naming the ownership path and available owner details, with one retry instruction. Ordinary acquisition while a delivery
journal claim is held must wait less than its 250 ms claim budget, never block the
main thread there for five seconds. Retain journal-before-ordinary ordering.

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

## Approval history

Keep legacy decisions and approvalRecord readable. New gates have a nonempty string `id`, stable through save/reload and publication retry and distinct for each new or changed/reopened gate independently of clock, area or kind. Legacy gates without id remain readable. Preserve optional `gate.promptSnapshot` as an ordered array of `{path,proseSha256,reviewSha256?}` rows, including an empty array. Absence means unbound, not an empty selection. The runner owns capture, invalidation and comparison; storage must preserve these distinctions through reload and projection. Each new approval decision and approvalRecord adds nonempty string `gateId` identifying its gate. Each new approval decision retains `gateAt` (the approved gate's original at value) and adds `evidence` with the exact shared [evidence shape](approval-policy.prompt.md#actor-and-evidence), alongside existing stage/decision/via/at/text fields; `approvalRecord` retains its legacy fields and the same evidence. Decisions are the complete gate history, not only the latest approvalRecord. The runner supplies the facts; this storage module never invents actors, words or approval. Preserve every record through atomic write/read and C3 projection; old records lacking evidence stay valid and must not gain invented provenance. The shared prompt journal remains separate from status.json.

## Dependencies

- [Approval policy and journal](approval-policy.prompt.md): required authoring/generation/native-production/verification/testing context for the evidence value schema; no reverse dependency on runner.

## Selection

- `gitContext(cwd, ports)` returns `{toplevel, commonDir}` (real paths) or null.
- `runForWorktree(cwd, ports)` returns the run whose `root` is the current worktree.
- `resolveRun(ref, {cwd}, ports)` returns `{run}` or `{error}`. `N` looks in the current repository, worktrees included. Outside a repository it uses the index; when several repositories have issue N, it asks for `owner/repo#N`. `owner/repo#N` and issue URLs pick that repository. Without ref: the run of the current worktree, else the only run of this repository that waits for a person, else the only active run; otherwise list the choices.
- `listRuns({cwd}, ports)` returns the runs of the current repository, or all indexed runs outside a repository.
- `allRuns({cancelled}, ports)` returns every run on this machine. It finds the repositories only from the run index (`<stateDir>/runs.json`), never from a Herdr layout registry, then reads each `<commonDir>/pdd/runs/<N>/status.json`. With `cancelled` it also reads the renamed `<N>-cancelled-<id>` folders. A repository or file that is gone or unreadable is skipped without an error.
