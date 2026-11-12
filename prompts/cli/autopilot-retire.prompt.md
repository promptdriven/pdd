# Move a machine from the removed full engine to the core engine

Own `src/autopilot-retire.mjs`. Autopilot has one engine, the [core](autopilot-core.prompt.md). The old full engine
(a coordinator chat in the Herdr session `pdd-autopilot`, workflow runs with worker chats, completion workers and its
own claims) is removed. This module moves one saved machine state of one repository to the core engine, once, in
steps, inside a [launcher](autopilot-launcher.prompt.md) tick. It makes no AI call and never changes the timer.

Export:

- `FULL_ENGINE_REMOVED`: `The full Autopilot engine is removed; Autopilot runs only the core engine. Run pdd autopilot
  start without --engine.` The launcher refuses `--engine full` with it.
- `RETIRED_NOTE`: `Autopilot moved this machine to the core engine; this PR is not worked on. A person can merge or
  close it.`
- `MOVE_STEPS` (`pane`, `runs`, `claims`, `notes`, `slots`, `workers`, in this order) and `MAX_DEFERS` (6).
- `engineBefore(state, repoEngine)`: the engine that a state ran before: its saved `engine` when it is core or full,
  else `repoEngine` (`autopilot.engine` of the checkout's `pdd.json`) when it is core, else full.
- `moved(state)`: true when `state.retiredFull.done` is a number.
- `movedState(state, journal)`: the state with `engine: "core"`, `retiredFull: journal` and no full-engine key
  (`acknowledged`, `auditHolds`, `checkCapacity`, `commentCache`, `contextBinding`, `contextPane`, `currentMode`,
  `deliveryIntent`, `dependencyPending`, `fullEngineNoticeAt`, `githubIntake`, `health`, `interpreterPattern`,
  `ownerLaunch`, `paneId`, `parkedNumbers`, `parking`, `parkingAlerts`, `pullCache`, `recipeDelivered`,
  `reconciliationIntent`, `relaunchHeld`, `relaunchPending`, `relaunchTargets`, `retryAt`, `routeQuestions`, `runtime`,
  `seen`, `timeSeen`, `uncertainDeliveryHistory`, `workspaceId`). Every other key stays. When `ownerLaunch.profile`
  exists and no `launchProfile` is saved, it becomes `launchProfile`, so a later start verifies the same agent sign-in.
- `claimRecord(body)`: the claim record of a comment (a JSON object with nonblank `repository`, `coordinatorId`,
  `machine` and `labelEventId`, in a code block or as the whole body), else null.
- `oldProcessOf(args, {runsRoot, stateFile, runDirs})`: `worker` for a command line that runs `workflow-worker-completion.mjs`
  with a JSON identity whose `runDir` is inside `runsRoot` (`COMMON_DIR/pdd/runs/`) and, when recorded run directories
  are supplied, exactly equals one of them; `coordinator-idle` for one that
  runs `autopilot-launcher.mjs --coordinator-idle` with a JSON identity whose `stateFile` is this state file; else
  null. An identity that is a file path, or JSON that does not parse, is not ours. A start follow-up
  (`--start-scan-wait`) is never stopped. A repository path, another run, an active run, a core worktree
  and a manual command are never enough.
- `parseProcesses(text)`: the `ps` rows `{pid, ppid, pgid, rss, uid, start, args}` (rss in KiB). `uid` can be null only
  for a legacy test adapter; a null uid never gets a cwd probe. It returns null when any nonblank row is malformed,
  rather than treating a partial inventory as cleanup evidence.
- `procTable(fs, root = '/proc')`: the same rows as text, read from Linux `/proc` (`cmdline`, `status` uid, and ppid,
  process group, start identity and rss pages from `stat`), for a machine without `ps`; only a PID confirmed gone during reads is skipped. An unreadable live row or a missing uid or start identity makes the inventory unavailable.
- The live workers step reads the global process table while this launcher is running. The table must include this
  launcher process; otherwise it is unavailable and the step stays unfinished. No selected old workers is a valid
  no-op when the launcher row proves the table is complete.
- `moveLine(state, journal)` and `moveToCore({state, stateFile, repoEngine}, ports)`.

## The journal and the steps

`moveToCore` reads the journal `state.retiredFull` (or a new one) and returns `{done, journal, message}`. The journal
keeps `startedAt`, `wasFull` (`engineBefore` is full), `steps` (step name → time done), `counts`, `defers`, `claims`
(the claims that the runs step found), `runIntents` (saved `{runId, issue}` cancellation intents), `cancelledRuns` (run IDs
whose cancellation count is saved), `forced`, `warnings` and `lastError`. A complete journal returns `{done: true,
message: ''}` with no read or write. Each step runs only when it is not done; after it, the move awaits
`ports.save(journal)` before it starts another step or returns. A failed step saves `lastError` (`STEP: one line`) and
returns done false with `Autopilot could not finish the move to the core engine (LAST_ERROR); the next tick goes on
from this step. No new work starts.` A failed journal save returns done false with `Autopilot could not save the move
journal (save: ERROR); the next tick retries. No new work starts.` A failed save returns that result directly and is
not retried in the same tick. It never leaves a save running after it returns.
So a failed step goes on at the next tick, and a done step never runs again.

**Merge hold.** Before the first step of a machine that ran the full engine, the move reads which old work is busy:
a live run of this machine with a merged PR (its post-merge steps may be open), and the old coordinator chat when Herdr
shows its saved pane `working`. While something is busy and `defers` is below 6, add 1 to `defers`, await its save,
and return done false with `Autopilot waits to move this machine to the core engine: WHAT (tick N of 6); no new work starts.` On
the 7th tick the move goes on and saves what was busy in `forced`; the line names it. A read failure here waits for the
next tick in the same way, without a count.

1. **pane**: with a saved `paneId`, read `agent get PANE` from the old coordinator session. Herdr that is missing, not
   running, or has no such agent or pane: nothing to close. When the agent's pane, workspace, folder (`samePath`) and
   agent kind match the saved state, close the pane and read `pane get` to confirm that it is gone (still open: the
   step fails). A pane that belongs to something else is never closed (`keptPanes`). Another Herdr error fails the
   step.
2. **runs**: every run record of this machine (`automaticOrigin.machine` is this machine, same repository, any older
   coordinator of this machine too) that is not cancelled or completed: first add its saved claim identity
   (`commentId`, `labelEventId`) and its `runId` intent to the journal and save the journal. If that save fails, do not
   cancel the run. Then call `ports.cancelRun(run)` (exit 0 needed, else the step fails), then
   `ports.releaseLocal(run)` (not released: a warning). After each cancelled run, add to the journal's cumulative run
   count and warnings, then save before the next run. If that post-cancel save fails, the next tick reads
   `listRuns(true)`: it records only a saved intent whose same `runId` is now cancelled, retries its local release and
   saves the cumulative result. A live intended run is cancelled again; it is not counted. A retry therefore adds its
   remaining runs without dropping or duplicating earlier counts or warnings. The saved claim lets a retry release a
   run's remote claim after its local status was already cancelled.
3. **claims**: release this machine's claims of the full engine. Issues to read: the claims of the runs step; for a
   machine that ran the full engine also the saved intake claims of this machine (`githubIntake.claims`) and every open
   issue with `pdd:working`. Skip an issue that has a core job file (`ports.coreJobs()`). On each issue, this machine's
   claim comments are the ones with a saved claim identity, or with a claim record whose `coordinatorId` and `machine`
   are this state's. The core's own claim records name a hashed machine id, so they never match. Delete those comments
   (404 is fine). Remove `pdd:working` only when the winning label event (the first `pdd:working` label in the
   timeline after its last removal) is named only by this machine's claim comments. Never remove another label:
   `pdd:stuck`, `pdd:needs-decision` and every label of a person stay. Another machine's claim stays untouched.
4. **notes**: for each PR of this machine's runs that are not completed (cancelled runs too), when the PR is open and
   has no comment with the hidden marker `<!-- pdd:autopilot-retired-full -->`, post `RETIRED_NOTE` with the marker.
   So each PR gets the note at most once, also when the step runs again. PRs stay open; branches stay.
5. **slots**: `ports.releaseSlots()` releases this state's check-capacity snapshot.
6. **workers**: from `ports.processes()`, the processes of `oldProcessOf` other than this process and its parent,
   plus descendants that were still linked to those selected processes. The selector receives only exact run directories
   and root paths from this machine's recorded ended old runs (cancelled or completed). It never selects by executable name. For a current-user
   parentless process (PID 1 or a parent missing from the inventory), cwd under one of those exact ended-run roots proves only that it can be a manual command:
   leave that process untouched and the step unfinished unless its command already has a recorded worker or coordinator
   identity. Do not read working directories of other users' processes. If that process exits before its cwd read, it is
   already gone; if it remains with the same PID and start identity, even if its command changed, and cwd is unreadable, leave the step unfinished. Each selected PID is re-read before TERM and KILL and must retain
   its start identity and command. The native `ps` and Linux `/proc` adapters both provide this stable identity. A failed inventory leaves this step unfinished for
   retry; it does not remove any retained run worktree.
   Send each captured process PID `SIGTERM` (captured descendants include `herdr agent wait` children).
   Wait up to 5 seconds, reading the process table every 250 ms; a process whose pid still shows the same command
   line gets `SIGKILL` by PID. Count the stopped processes, the killed ones and their memory.

The move is done after the last step. Its message is the one line `Autopilot moved this machine to the core engine for
REPO: closed N coordinator chat(s), cancelled N old run(s), released N claim(s), left N PR note(s), stopped N old
worker process(es) (M MB)`, plus `; it waited N tick(s) for WHAT` when the merge hold ended by the limit, and a period.
A machine that did not run the full engine and where nothing was found gets an empty message.

## Ports

`now`, `gh(args, options)` (a `gh api --include` reply with the HTTP status), `herdr(args)` (a reply, or an error with
its Herdr code), `listRuns(cancelled)`, `cancelRun(run)`, `releaseLocal(run)`, `releaseSlots()`, `processes()`,
`signal(target, name)`, `sleep(ms)`, `cwdOf(pid)` (the exact local working directory, or null when unavailable),
`uid` (the current numeric user id), `samePath(a, b)`, `commonDir`, `coreJobs()` and `save(journal)`. `save` may be
async and the move awaits it. The launcher supplies the native ones.

## Dependencies

- [Autopilot launcher](autopilot-launcher.prompt.md#the-move-from-the-full-engine): required native generation and verification context for the
  tick that calls the move and for its ports.
- [Workflow runner](workflow-runner.prompt.md#commands): required native generation and verification context for `cancelRun`.
- [GitHub dependency reader](issue-dependencies-github.prompt.md): required verification context for the claim comment
  record and the winning label event.
- [Process lifecycle](process-lifecycle.prompt.md): required native process identity and captured-tree termination
  context for retired workers. This prompt owns which old workers are eligible for cleanup.
