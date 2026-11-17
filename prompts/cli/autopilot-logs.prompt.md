# Autopilot worker viewer

Own `src/autopilot-logs.mjs`. Let a person see a headless core worker between scheduler ticks, without taking
custody of its processes. This is a local view, not a terminal attach, scheduler, approval or merge operation.

## Domain decisions

- `runAutopilotLogs({root, issue, follow, env}, ports)` reads the repository's current core jobs. `root` is the
  core state directory; `issue` is a positive integer or absent; `follow` is Boolean; `env` supplies the worker
  queue location. Return `{exitCode, message}`. With no issue, list current workers in issue order, or say
  `No current Autopilot workers in this repository.` Select by primary or grouped issue number, preferring a
  direct match. An unknown issue exits 1 and points to `pdd autopilot logs`. Do not follow a future run of an
  absent worker. No GitHub, timer, scheduler, signal delivery, lock, process custody or saved state writes.
- Show the primary issue, grouped issue numbers if any, stage (including build, repair, PR checks or ending),
  PR number if known and last observed activity (UTC time of newest job, process or current check evidence).
  Show saved blockers with reasons: active retry or service hold, Runtime maintenance, waiting for the merge
  lane, or a last error. Report each attached process (build/repair, review, replay, suite and Runtime) with
  the wrapper state from `jobs.inspect(job)` using the saved identity, not a PID alone. An exit record is not
  evidence of a live process. A missing exit record for a dead wrapper is not a successful result.
- Read suite/replay queue progress by check working directory from `queue.read({cwd, since, env})`; ignore
  receipts queued before the wrapper started or for another known head. A waiting ticket gives its queue
  position; an admitted ticket without a child has not started tests. Report running tests only with a current
  running ticket, live wrapper and a live recorded child group (`process.groupAlive(pid)`); unknown ownership,
  a dead group, or a no-longer-live wrapper never displays as running tests. Separate finished receipts from
  current execution, and show unavailability or uncertainty and its reason rather than claiming a pass.
- Show paths to saved wrapper logs, result and exit files, and current check log and receipt when available.
  Only read regular per-worker wrapper logs within the core log directory, never job input or spec contents.
  Metadata and log reads use `fs`, which defaults to local filesystem reads. Files may appear, change or go
  away between reads; a missing optional file does not prevent viewing the rest.
- With an issue, print a snapshot and recent wrapper log lines. With `follow`, `emit(text)` that snapshot
  immediately, then use `clock.sleep(ms)` to re-read about once a second, without waiting for scheduler ticks.
  Stream new lines by process and print state updates when stages, processes or blockers change, not on every
  log write. Follow parallel and replacement phases and drain recent output from a disappearing log before
  switching or exiting. When the selected saved worker goes away or a new run replaces it, exit 0 and say it is
  no longer current; no claim about the outcome follows from its disappearance. Ctrl-C stops only the viewer.
- Limit each log read to the most recent 64 KiB of unread bytes; make omissions visible. Do not repeat old
  bytes on ordinary append; restart the cursor on replacement or truncation. Decode complete lines and flush
  remaining text on a final read. Strip terminal controls from all displayed text, summarize known agent
  event lines in readable text, and bound the length of individual displayed lines. Local output is not
  publication or a promise to redact all secrets from an agent's transcript.

## Process display contract

`describeWorkerProcess(input)` is a pure module function returning one string without a final newline.
Inputs: `role` and `lastActivity` strings (the latter an ISO UTC timestamp or `unknown`), `processState`
(`running`, `exited`, `dead`), `exitCode` (integer or null), `signal` (string or null), `queueState` (one of the
values below), `position` (integer or null), and `log` and `evidence` (path strings or null).

Start `ROLE: wrapper running`, `ROLE: wrapper exited` (append ` (status N)` for a known exit code,
otherwise ` (SIGNAL)` for a known signal), or `ROLE: wrapper not running (no exit record)`. Append the
queue phrase (semicolon and space if present), then `; last activity TIME`. Append `\n  Log: PATH` for a
log and `\n  Evidence: PATH` for an evidence receipt. Strip terminal controls from display values.

| queueState | phrase |
| --- | --- |
| `none` | no phrase |
| `waiting` | `waiting for a check slot` plus ` (position N)` when known |
| `starting` | `tests have not started` |
| `running` | `tests running` |
| `finished` | `test receipt finished` |
| `stale` | `no live test process confirmed (stale or uncertain receipt)` |
| `unavailable` | `test queue evidence unavailable` |

## Dependencies

- [Headless agent jobs](agent-job.prompt.md#public-contract) and [shared suite queue](test-suite-queue.prompt.md),
  native adapters for observing, not changing, current process and queue evidence.
