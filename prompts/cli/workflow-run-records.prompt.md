# Local workflow status for clients

`src/workflow-run-records.mjs` owns a bounded, atomic `status.json` projection
of a local run. Phone and area-chat clients can display progress without reading
private journal snapshots. The journal remains the only authority for decisions
and effects. Preserve the fleet v1 field meanings below; no controller, keeper,
installer, session discovery or background service is introduced.

Module functions `runStatusFromState(state, extras = {})`,
`normalizeRunLinks(links, stageId = null)`, async
`writeRunStatus(runDir, status, ports = {})` and async
`readRunStatus(runDir, ports = {})` are the shared interface. Projection never
mutates its input or throws. Writers return `{ok:true}` or `{ok:false,code}`;
readers return `{value,warnings}` and never grant approval.

## Status projection

`extras` has `phase` (`record`, `exit`, or default `journal`), `now`, optional
`outcome` and `controller`. Record phase reports running unless all definitions
are complete; journal-only phase cannot prove liveness and reports unknown
unless complete. Exit phase uses outcome.state (completed, waiting, failed or
recovery_required), with unrecognized states becoming unknown. Invalid stage
layout yields no current stage or steps.

The object includes `v:1`, `runId`, `workflow` from name, `repo`, `issue`, `root`,
`agent`, `number` (issue.number, or area number), `startedAt`, `journalSeq` (safe nonnegative integer, otherwise zero),
`updatedAt`, `state`, and `stage:{id,kind,index,total}` or null. Absent identity
fields are null. `controller` is extras.controller or null; never invented.

| Field | Observation |
|---|---|
| steps | Definition order; each has id, kind, optional, state, startedAt, endedAt, agent, session. Completed entries are done or skipped; current is current (failed on failure); later entries are next, other entries unknown. Times are durable intent/completion epoch milliseconds, or null. Session is `{agent,id}` only from that step's own backend.nativeSession of kind id and supported agent; never borrow another step's session. |
| waitingFor | While waiting: saved waitingPerson or waitingDecision decisions/what first; explicit outcome.decisions/what next; otherwise undecided optional offers approve/skip, human stage offers approve, next-advance proposal without acceptance offers approve, merge offers no decisions and asks for GitHub merge. Other waits are null. Running or terminal states yield `{decisions:[],what:null}`; unknown yields null. Bound what text to 200 characters. |
| resumeDecisions | Saved waitingPerson choices when present, otherwise the same optional/human/next-advance choices. Only approve, skip, changes are exposed. Merge is never a decision. |
| pr | Completed PRs with number and URL, as `{stage,number,url}`. |
| links | At most the newest 20 valid `{stage,kind,url,verdict}` entries. Kind check/try/replay; HTTPS URL without credentials, max 2048 code points; verdict passed/failed/unknown/null, with try requiring null. Optional stageId filters to that stage. |
| cancelled | null when absent; otherwise saved `{state,at}`. No cancellation is invented. |
| herdr | Optional actual `{session,workspaceId,label}` from state.herdr or current/latest recorded backend; absent when no workspace identity is known. Unknown label is null. |
| decisions | Last five valid decisions, newest last: `{stage,decision,via,at,text?,phoneId?}`. Decision approve/changes/skip, via terminal/chat/phone. Accept normalized area records or runner records with binding decision/expectStage/text and approvalRecord kind/userMessage/phoneId. Preserve the admission time; omit missing optional fields. Never infer who approved from the active process. |
| changes | Latest five `{stage,round,text,at}` entries, text limited to 4000 code points. |
| waitingDecision | Clone the saved gate stage, seq, at and decisions, or null. Status never creates a gate. |
| approvalRecord | Clone the journal's person approval evidence, or null; status never verifies, generates or changes that evidence. |
| stageAgent | Current agent/cleanup pending backend's actual `{kind,nativeSessionId,herdrSession,paneId}`, or null. |
| message | Exit outcome message cut to 300 characters, otherwise null. |

Unknown sessions and times remain null, including old runs without these fields.
Stage start is recorded before launch; completion records retain that start and
the actual completion time. A snapshot does not certify native success.

## Atomic file and failure rules

Write UTF-8 JSON plus newline to `<runDir>/status.json`, at most 256 KiB.
Use an exclusively created mode-0600 temporary file in the canonical ordinary
run directory, complete write, file sync, atomic rename, and best-effort directory
sync. Reject aliases of the run directory. A pre-rename failure leaves the old
status whole; clean up only this writer's temporary file. A failure is a side
output failure only: do not alter the journal, workflow outcome, output or
progress. `ports.fs` may provide the node:fs/promises interface and
`ports.randomBytes` the temporary suffix. No writes to journal or artifacts.

Read missing/unreadable/oversize/malformed files as null with warnings. Require
v1, matching run-directory basename and nonnegative safe journalSeq; normalize
unknown display states and invalid links. Readers never repair files.

## Runner integration

After every durable record, await its derived write before the next record.
Write the final outcome before releasing the command lock. Only a command that
owns the lock and has validated its own run journal writes status. Missing runs,
contended commands, same-issue conflict reports and attach write nothing. A
failed write cannot fail a successful workflow or add a journal event. Area-chat
runners use these same exports and field semantics.

## Dependencies

- [Workflow runner](workflow-runner.prompt.md): required authoring/runtime input
  owner for saved stage state, actual backend identity and journal ordering.
- Node fs/promises, path and crypto: runtime atomic replacement and read-only
  projection access. No external service is required.
