# Run records

Own `src/workflow-runs.mjs`. A run is one workflow for one issue. Its record is `status.json` in the run folder `<git common dir>/pdd/runs/<issue number>/`. The record is the run state and also the status shape that phone clients read (C3, `v:1`).

## Record

Saved fields: `runId`, `workflow`, `repo`, `issue {number,title,url}`, `number`, `root` (worktree), `branch`, `baseBranch`, `sourceRoot`, `commonDir`, `runDir`, `agent`, `configDir`, `startedAt`, `state` (running, waiting, completed, cancelled), `areas`, `area` (index), `done` (step → `{at, summary, area}`), `gate` (`{area, at}` or null), `chats` (one per area chat: `{area, tabId, paneId, workspaceId, label, startedAt, session, configDir}`), `decisions`, `changes`, `approvalRecord`, `pr`, `prState`, `cancelled`, `warnings`.

`writeRun(record, ports)` adds the C3 view, increments `journalSeq`, sets `updatedAt`, and writes the file atomically (temporary file, then rename). It also updates the index of known runs in `<stateDir>/runs.json` (default `~/.local/state/pdd`). An index failure is ignored. `readRun(runDir)` returns the record or null.

C3 view: `stage` (current step, or `approve` at a gate, or `merge` after the PR), `steps` (each step with area, state done/current/next, times, agent, session and summary), `waitingFor` (`{decisions:['approve','changes'], what}` at a gate, `{decisions:[], what:'Review and merge the PR on GitHub'}` after the PR, else `{decisions:[], what:null}`), `resumeDecisions`, `waitingDecision`, `herdr`, `stageAgent`, `links:[]`, `controller:null`, `message`.

## Selection

- `gitContext(cwd, ports)` returns `{toplevel, commonDir}` (real paths) or null.
- `runForWorktree(cwd, ports)` returns the run whose `root` is the current worktree.
- `resolveRun(ref, {cwd}, ports)` returns `{run}` or `{error}`. `N` looks in the current repository, worktrees included. Outside a repository it uses the index; when several repositories have issue N, it asks for `owner/repo#N`. `owner/repo#N` and issue URLs pick that repository. Without ref: the run of the current worktree, else the only run of this repository that waits for a person, else the only active run; otherwise list the choices.
- `listRuns({cwd}, ports)` returns the runs of the current repository, or all indexed runs outside a repository.
