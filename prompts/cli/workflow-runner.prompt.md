# Workflow runner (area chats)

Own `src/workflow-runner.mjs`. It runs a workflow for one GitHub issue as a few area chats. pdd has four jobs: start, gates, PR and status. The agent does the work. pdd does not watch the agent, run tests, wait with a timeout or merge.

## Commands

Each export takes `(input, ports)` and returns `{exitCode, message}`. The CLI prints the message.

- `startRun({name, issue, agent, cwd, packageRoot})`: read the areas from the pdd-NAME skill ([areas](workflow-areas.prompt.md)). Resolve the issue with gh ([GitHub](workflow-github.prompt.md)). Refuse when the issue already has a run that is not cancelled. Fetch the default branch (a failure is only a warning). Make the worktree and branch ([worktree](workflow-worktree.prompt.md)). Make the run folder and write the run record ([runs](workflow-runs.prompt.md)). Start the area 1 chat ([chat](workflow-chat.prompt.md)). Print where the run is, `pdd workflow open N`, `pdd workflow status N` and `pdd workflow approve N`. Then return at once. If the main repository is not trusted by Claude, say that Claude asks to trust the folder first.
- `stepDone({step, summary, cwd})`: only the agent calls this, from the worktree. Find the run from cwd. Record the step with its summary and time. An unknown or out-of-order step prints a warning and is still recorded. Then print one of:
  - the next step of the area and the exact `done` command (an optional step is a question to the person, and "skipped" is a valid summary);
  - at an `approve` gate: show the result, ask the person, stop, never approve for them; how they approve; how to handle changes (revise here, run done again, ask again);
  - after the last step of a `pr` area: "pdd opens the PR now". Commit any uncommitted files (with a warning), push and open the PR. The title is the issue title. The body has "Closes #N", each step summary and `<run folder>/verify.md` (or a note that it is missing). When the PR exists already, push the new commits only. Print the PR URL and "pdd never merges".
  A cancelled or completed run prints that the agent must stop.
- `approveRun({ref, cwd})`: only a person approves. When pdd runs in an agent session (`PDD_AGENT_SESSION`, `CLAUDECODE`, `CODEX_THREAD_ID`) or without a TTY, it needs chat evidence: a user message in the current area chat's native session after the gate ([approval evidence](approval-evidence.prompt.md)). Messages that pdd sent with `changes` do not count. Otherwise ask `y/N` on the terminal; the question names the area, the repository, the issue and its title. Before the gate, the terminal may still approve after a second question; an agent may not. Record the decision with its source and text. Start the NEXT area as a NEW chat. Its first message lists the approved step summaries, the changed files and the run folder. A `pr` area has nothing to approve.
- `changeRun({ref, text, cwd})`: send "The person asks for changes: TEXT …" into the SAME area chat. Record the round. The gate stays open; move the gate time to now.
- `cancelRun({ref, cwd})`: mark the run cancelled and close its Herdr tabs. Keep the worktree and the branch.
- `runStatus({ref, cwd})`: without ref, list the runs of this repository (or all known runs outside a repository). With ref, show the issue, the area, the steps, what pdd waits for, the chat, the PR with its state and CI, the worktree and the run folder. Read the PR with gh. A merged PR completes the run. Write the run record.
- `openRun({ref, cwd})`: focus or attach the current area chat. When its native session ended, resume it in its tab. When the area has no chat yet, start it.

`ref` is an issue number, `owner/repo#N` or an issue URL ([selection](workflow-runs.prompt.md)). Without ref, use the run of the current worktree, or the only run of this repository that waits for a person.

## Rules

- No timeouts, no polling loop, no foreground controller, no test runs, no hashes or snapshots.
- Light checks warn and never break the run. Errors that stop a command say what to do next.
- Never merge. Never push to the default branch. Never touch the person's default Herdr session.
- Messages to the agent are short. The first message of an area chat is about 10 lines: "Use the pdd-NAME skill", the issue number, title and URL, the worktree, the run folder, the area and its steps, the `done` rule and the gate rule. Never paste the guide or the workflow text.
- Commands that pdd prints for the agent use this package's absolute node and `bin/pdd.mjs` paths.

## Dependencies

- [Workflow areas](workflow-areas.prompt.md), [run records](workflow-runs.prompt.md), [area chats](workflow-chat.prompt.md), [approval evidence](approval-evidence.prompt.md), [GitHub](workflow-github.prompt.md) and [worktree](workflow-worktree.prompt.md).
- Ports: `execFile` (git and gh), `herdr`, `env`, `stdin`, `stderr`, `confirm`, `readApprovalEvidence`, `stateDir`, `now`, `pdd` (the command prefix). Defaults are the real ones.
