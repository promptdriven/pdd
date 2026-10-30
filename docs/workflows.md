# Workflows in depth

A PDD workflow is a skill: a folder of plain Markdown and one JSON file. Your agent follows it. pdd itself does only four things: it starts the run, it holds the gates, it opens the PRs and it shows the status.

## The three workflows

| Workflow | Use it for |
|---|---|
| `pdd-feature` | New behavior. |
| `pdd-bug` | The code breaks an accepted expectation. |
| `pdd-small-change` | A small change with a clear effect that is easy to undo. If the impact grows, the agent suggests `bug` or `feature`. |

Each workflow has areas. Each area has steps and ends at a gate. `?` marks an optional step.

| Workflow | Area 1 | Area 2 | Area 3 (only when you ask) |
|---|---|---|---|
| `feature` | story: understand, visual?, prompt-story. Gate **approve** | prompt PR: check, try?. Gate **try it and approve**. pdd opens **PR 1**. Then **code now or stop?** | code: build, verify, formal, review. pdd opens **PR 2** |
| `bug` | story: reproduce, prompt-story. Gate **approve** | prompt PR: check, try?. Gate **try it and approve**. pdd opens **PR 1**. Then **code now or stop?** | code: build, verify, formal, review. pdd opens **PR 2** |
| `small-change` | plan: scope. Gate **approve** | build: change, verify, formal. pdd opens **one PR** | |

PR 1 holds the prompt, the Story and the test cases (`tests/*.json`). Repo tests that fail on today's code go to PR 2, so merging PR 1 never breaks the main branch. PR 2 holds the code. You can stop at PR 1, merge it, and make PR 2 later.

### A big request: a plan and many Stories

In `feature`, the understand step counts the separate behaviors in the issue. One behavior gets one Story and no plan. More behaviors get a plan, `user_stories/PLAN.md`: a numbered list with one line for each Story, in build order.

- Each Story in the plan has its own test file, `tests/<story>.json`.
- At the story gate, the chat gives the paths of the Story files and the plan, and ends with "Reply 'I approve' here or run `pdd workflow approve N`, or tell me what to change." You can say "make it one Story", "split part 5" or "change Story 5: …". A change names one Story: the chat redoes only that Story and its test file.
- The check step prints one `Runtime check (<story>)` line for each Story, then the overall line. If a Story fails, it fixes and checks only the Stories that failed.
- `pdd workflow status` shows the count, for example `Stories: 4 of 5 pass (✗ refunds)`.

What each step does:

| Step | What the subagent does |
|---|---|
| scope | States the result, the files, why the change is small and how to undo it. Writes the expected result and names the test command. For a behavior fix, records `Defect:` and `Not caught because:`. |
| change | Makes only the approved change. If a prompt owns the behavior, it changes the prompt first. Adds a test. |
| reproduce | Finds the smallest safe input that shows the bug. Writes the expected and the actual result. |
| understand | States the wanted result, what must not change and what is out of scope. Counts the behaviors. With more than one, writes `user_stories/PLAN.md`. |
| visual? | For a visible interface, sketches 2 or 3 options, with empty and error states. For a page or a screen, it also writes the app map and its SVG mockups from the chosen design, so the Simulator shows the real screen (the Screen tab). The chat asks you first, and recommends this step for a page or a screen. |
| prompt-story | Reads the full Prompting guide and `RUNBOOK.md` sections 2 to 4, then the sections that fit: a CLI, a prompt that calls another, check paths, money and dates, a page or screen, AI calls and test patterns. A page gets a `render` operation that returns its HTML and an app map, so you can try the page on the Screen, and its tests check what the page shows. Writes or changes the smallest prompt that owns the behavior, each Story in the person's words, and one `tests/<story>.json` for each Story. Takes the expected results from the requirement, not from the code. |
| check | Runs `pdd test` once for all Stories as `RUNBOOK.md` says, when the `pdd-prompting` skill has that file. After a fix, it checks again only the Stories that failed, by name. It never sends the same check on the same files again: it reads a result again with `pdd test --read`. In `bug`, it checks every Story whose prompt changed. Puts one `Runtime check` line and one report link for each Story in its summary. Else it reviews the prompt and the cases by hand with the review rules. |
| try? | Runs `pdd simulate` and makes a Simulator link for each Story that you want to try, as `RUNBOOK.md` says. Else it shows the plan or the bug in a safe local preview or demo. |
| build | Builds only what you approved. Tests through the public interface. |
| verify | Runs the replay test of `RUNBOOK.md` section 17 on the code and on a planted mistake, then the tests and the repo's required checks. Writes the tables first, and the exact commands and their real output last, in a closed `<details>` block. |
| formal | A fresh subagent that did not write the code runs the formal check of `RUNBOOK.md` section 17 for each Story with `## Rules to check`. Adds one result to `verify.md`, after the tables. |
| review | A fresh independent subagent that neither built nor verified gets only the issue, Story, Defect block, diff, Old-code proof and Tests vs base, PR 1 body and supplied step summaries, never builder notes or chat history. It must not open build.md, verify.md or formal.md in the run folder. It answers the six questions in `steps/review.md`, inspects source and tests, exercises a real changed path and writes the actual verdict and findings to the run folder. |

If verify or formal finds a failing case, or review finds must-fixes, the chat returns to a fresh build, then verify, formal and fresh review. There are at most two repair rounds after the initial review. If vectors still fail, PR 2 keeps "✗ N vectors fail" at the top. The PR then opens with the actual `Review: N must-fix` or `Review: no must-fix` verdict and any remaining must-fix list at the top. There is no new human gate. These are agent instructions; metadata orders steps but does not enforce reviewer independence or judgment.

Only prompt-story reads the full Prompting guide. check reads the `pdd-prompting` core rules and review rules. change reads the guide only when it changes a prompt.

## Two ways to use a workflow

| | In your chat | As a run on an issue |
|---|---|---|
| Start | Call `pdd-feature`, `pdd-bug` or `pdd-small-change` in Codex or Claude Code | `pdd workflow start NAME ISSUE` |
| Branch and worktree | No. The agent works in your folder | Yes. A new branch and worktree for the issue |
| Chats | One | One for each area, in Herdr |
| Gates | The agent asks you | pdd holds them. You approve in the chat or with `pdd workflow approve` |
| PRs | At a PR gate, the agent asks you. It opens the PR only if you say yes. It never merges | pdd opens them. It never merges |

## How a run works

```
pdd workflow start feature 42      returns at once
  |
chat 1  story: understand, visual?, prompt-story
  |     gate: approve
chat 2  prompt PR: check, try?
  |     gate: you try it and approve
  |     pdd opens PR 1 (prompt, Story, tests)
  |     "Do you want the code PR now, or stop here and merge PR 1 first?"
chat 3  code (only when you ask): build, verify, formal, review
  |     pdd opens PR 2 (code), stacked on PR 1
you     review and merge on GitHub
```

1. `pdd workflow start` reads the issue, makes the branch, the worktree and the run folder, and opens the first chat in Herdr. It refuses an issue that already has an active run. Then it returns. You can close the terminal.
2. The first message of the chat is short. It names the skill, the issue, the worktree, the run folder and the area with its steps.
3. The main chat coordinates and talks with you. It writes no code and performs no checks.
4. The main chat gives steps to fresh subagents; builders are never reused and never check their own code. Before checking, close finished agents if supported and try fresh startup. Only after startup fails may verify or formal reuse an agent that wrote no code, tests or prompts in this run. Review always needs a fresh agent with no build, verify, formal or prior review of this change and no prior review context, including every repair round. If no fresh reviewer can start, write `Not checked: review (agent limit)`, stop and tell the person. Follow pdd-prompting RUNBOOK §17 for missing-check records, new-session recovery and replacing them after actual checks. Each subagent gets its full brief at once, with file paths, not chat history; the chat waits once with a long time-out and no small follow-ups.
5. Hold review completion while must-fixes remain and fewer than two repair rounds have run: start a fresh build with the must-fix list. Only after the final review (clear or two repairs used), run `pdd workflow done review`; it opens PR 2. For other steps, the agent runs `pdd workflow done STEP --summary "..."`. pdd records the step and tells the agent what comes next: the next step, a gate, or "pdd opens the PR now". An unknown or out-of-order step gives a warning. It does not stop the run.
6. At a gate, the chat shows the result, asks you and stops. There is no time limit. When the chat needs your answer in the middle of a step, the agent runs `pdd workflow ask "<question>"` first, so `status` shows that the run waits for you.
7. If you ask for changes, the same chat revises and asks you again. The gate stays open.
8. If you approve, pdd starts a new chat for the next area. That chat gets the outputs of the approved area: the files, the summaries and the run folder.
9. Completing the last step of an area with a PR gate pushes the branch and opens the PR. For bug and feature, the review-completion hold in point 5 overrides generic completion after each step: keep PR 2 unopened during repairs.
10. You merge the PRs on GitHub. `pdd workflow status` reads the PR state. When the last PR is merged, the run is completed.

A workflow can start from a normal checkout or a linked worktree, including one whose primary repository is bare. All linked checkouts share the same issue claims and allocation records in the common Git directory. New run worktrees live beside the primary repository in `<primary-name>.pdd-worktrees/`; a bare `project.git` uses `project.git.pdd-worktrees/`. pdd verifies the origin and physical Git identity and keeps `core.bare` unchanged. A refusal before saving allocation intent leaves no issue claim or allocation record. If intent was saved but allocation is unconfirmed, preserve it and inspect that exact run before trying recovery.

Herdr uses the verified primary repository workspace as the parent when a run starts from a linked checkout;
the invoking source checkout and the allocated run worktree keep their own identities. This also supports a
verified bare primary. If Herdr confirms `linked_worktree_source` before any native agent starts, run
`pdd workflow open ISSUE` to finish that same allocated run. A saved linked-parent failure can recover through
this command even after an earlier open failed. pdd preserves the old parent shell workspace, records it as
superseded, and opens the verified parent under an unused label. It does not allocate another Git worktree.
An uncertain or lost allocation reply remains blocked for inspection; it never authorizes another native chat.

Review a run without entering its chat with `pdd workflow view ISSUE`; `status` prints this command. The terminal view brings together the saved state and gate, recorded human approvals, pending decisions, PRs, Runtime check/report links and the Simulator link. It links to the full issue and to current Stories (including acceptance criteria), plan, prompts, tests and gate notes. The commit and uncommitted-change indicator identify what you are reading. These are current files; a recorded approval does not certify later edits. Prompt approval and permission to start code work remain separate decisions. Missing artifacts or links are shown as unavailable or not recorded.

The view uses saved local records and local Git/file reads. It works with Herdr and the network offline and changes no state. Use `pdd workflow open ISSUE` when you want to focus or resume the chat.

### Simulate before PR 1

The check comes first, then the simulation. At the story gate, the chat can offer a simulation before the check: `pdd simulate <story>`, or `pdd simulate <story> --new` when visual made an app map.

After the check and try steps, the chat shows one `Runtime check` line for each Story (✓, ✗ or no verdict) with its report link, and the Simulator links. You try it, then approve or ask for changes. pdd opens PR 1 only after you approve.

The PR 1 body is short:

1. For a bug: the verdict line and the `Before ✗ … → after ✓ …` line with its report links.
2. One `Runtime check (<story>)` line for each Story. With more than one Story, pdd adds them up in a `Runtime check (all Stories)` line. Then a `Report (<story>)` link for each Story (report links expire after 7 days).
3. `Part of #N`, and that the code comes in PR 2 only when you ask.
4. `Draft prompts: … Approve them before you merge.`, when a prompt is still `draft`.
5. One short line for each step.

PR 1 has no `verify.md`, no Simulator links and no local paths.

### The code question

Then the chat shows the PR 1 link and asks: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`."

| You choose | What happens |
|---|---|
| Code now: say it in the chat, or run `pdd workflow approve N` | The code area starts in a new chat. It works on top of PR 1. PR 2 is stacked on PR 1's branch. Merge PR 1 first |
| Stop | The run waits. `status` says that PR 1 is open. If PR 1 is merged and you do not go on, the run ends as "done at PR 1" |
| Code later: `pdd workflow approve N` at any time | The code area starts. If PR 1 is merged, PR 2 starts from the merged prompts on the saved base branch (`--base BRANCH`, else the repository default) |

The code area is the PDD compiler: your agent writes the code from the approved prompts, and the same tests run on that code.

PR 2 says `Closes #N` and that it builds on PR 1. Warning-light-only work instead starts with `Not fixed yet: this helps find the cause`, uses `Refs #N` and keeps the issue open. PR-top rendering and old-code proof depend on the runner integration (#2594 and #2570). If PR 1 names draft prompts, approve each one with `pdd approve PROMPT` before you merge. Only a person can do that, at a terminal, or with the Approve button in the PDD Simulator while `pdd simulate` runs in the owner's terminal. An agent never sets `approved`. While PR 1 has a draft prompt, pdd does not offer the code PR. It prints the lines to run instead: `pdd approve PROMPT` in the run's worktree, then `pdd workflow approve N`. It commits your approval, pushes it to PR 1, removes the "Draft prompts" line from PR 1 and starts the code area.

### Who can approve

Only a person approves a gate. The agent never approves for you.

- In a terminal: `pdd workflow approve N` asks y/N. The question shows the repo, the issue and its title. At the PR 1 gate, it asks whether to make the code PR now.
- In the chat: say it in your own words. The agent then runs `pdd workflow approve`. pdd checks that your own message is in the chat after the gate. If it is not there, pdd refuses.

### The run folder

Each run has a run folder: `.git/pdd/runs/N/` in your clone, where N is the issue number. It is in the Git folder of your clone, not in the run's worktree. The first message of each chat names it.

| File | What it holds |
|---|---|
| `status.json` | The area, the step, what the run waits for and the PRs |
| `AREA-start.md` (one for each area) | The start message of that area's chat |
| `STEP.md` (one for each step) | The notes of that step |
| `verify.md` | The exact test commands and their real output |
| `review.md` | The independent verdict, six answers and concrete must-fix findings |

The code that the steps write is committed on the run's branch, in the run's worktree.

## Tests and evidence

pdd does not run tests. The agents do.

- The verify step runs in a fresh subagent that did not write the code.
- It runs the new cases, the regression tests and the repo's required checks. When it can, it shows that a new test fails on the old or wrong code, in a throwaway copy.
- For a small-change behavior fix it writes `Proof (defect fixed):` and `Proof (gap closed):`, and a reason for each removed test or changed assertion.
- It writes the exact commands, the exit codes and the real output to `verify.md`. It names what no test covers.
- The body of PR 2, or of the one `small-change` PR, has the step summaries and `verify.md`. When a check on the PDD interpreter ran, the body starts with its `Runtime check` lines and report links. Report links expire after 7 days.

Bundled feature/bug code areas declare `replay_evidence: "pdd.replay-evidence.v1"`. The agent writes
`replay-evidence.json` in the run folder using the [structured replay contract](replay-evidence.md).
The PR begins with the validated replay status and exact counts, original vector and current source hashes,
public-boundary execution coverage, semantic mutation control, and formal result with scope and reason.
Missing, malformed or stale records appear as blocked/not replayed. Assertion failures remain publishable.
Saved areas and custom workflows without this field retain their behavior. pdd checks structure and identity;
agents execute the tests. A replay status does not independently prove execution or prompt/code equivalence.

Read that output before you merge. Passing tests are useful evidence. They are not proof of all behavior. A test that was only written is not a test that ran.

<a id="make-your-own-workflow"></a>

## Make your own workflow

### Where skills live

| Level | Codex reads | Claude Code reads |
|---|---|---|
| For one project (commit it) | `.agents/skills/` in the repo | `.claude/skills/` in the repo |
| For you, in all projects | `~/.agents/skills/` | `~/.claude/skills/` |

If you set `CLAUDE_CONFIG_DIR`, Claude Code reads `$CLAUDE_CONFIG_DIR/skills/` for you, too.

`pdd workflow start NAME` and `pdd workflow list` look for a folder `pdd-NAME` with a `workflow.json`, in this order. The first one found wins.

1. `.agents/skills/` in the project
2. `.claude/skills/` in the project
3. `~/.agents/skills/`
4. `~/.claude/skills/`
5. `skills/` in the pdd package

The project is the top folder of the Git repo of your current folder. Put your copy where your agent reads it too, or in both folders of a level.

`npx skills add promptdriven/pdd` installs the five PDD skills at the project level, or at the "for you" level with `-g`. `pdd setup` copies them to the "for you" level only when they are missing: `~/.agents/skills/` for Codex, and `~/.claude/skills/` (or `$CLAUDE_CONFIG_DIR/skills/`) for Claude Code. After an update of the pdd command, `pdd setup` replaces an older copy that has its `.pdd-skill.json` marker. It never touches a copy without the marker, or a symlink. Do not edit these installed folders: an update replaces them.

Give your workflow a new name. A project copy with the same name as a PDD skill (for example `pdd-bug`) works only in Codex:

| Project folder | Codex | Claude Code |
|---|---|---|
| New name, for example `pdd-mybug` | Uses it | Uses it |
| Same name as a PDD skill, for example `pdd-bug` | Uses the project copy first | Uses only the user copy. The project copy has no effect |

### Copy and edit

This example makes the workflow `mybug` for one repo. Run it in your repo:

```sh
mkdir -p .agents/skills
cp -RL ~/.agents/skills/pdd-bug .agents/skills/pdd-mybug   # or from .agents/skills/pdd-bug
rm -f .agents/skills/pdd-mybug/.pdd-skill.json
```

Then edit the copy:

1. In `SKILL.md`, set `name: pdd-mybug` and a new `description`. The description tells the agent when to use the skill, for example "Use when the person reports a bug in the billing module."
2. Edit the areas in `SKILL.md` and in `workflow.json`. Keep them the same.
3. Edit, add or remove the step files in `steps/`. Keep each one short.
4. If you use Claude Code, also copy the folder to `.claude/skills/pdd-mybug`.

Then use it:

```sh
pdd workflow list            # pdd-mybug is in the list
pdd workflow start mybug 42  # a run on issue 42
```

In a chat, call `$pdd-mybug` in Codex or `/pdd-mybug` in Claude Code. Commit the folder so that your team gets the same workflow.

`cp -RL` copies the files, also when the installed skill is a symlink. Then your edits do not change the PDD skill.

### The files

```
pdd-mybug/
  SKILL.md          frontmatter (name, description), when to use it, the areas, the rules
  workflow.json     the areas, their steps and their gates
  steps/
    reproduce.md    one short brief for each step
    prompt-story.md
    check.md
    try.md
    build.md
    verify.md
    formal.md
    review.md
```

`workflow.json` lists the areas in order:

```json
{"version":2,"areas":[
{"name":"story","steps":["reproduce","prompt-story"],"optional":[],"gate":"approve"},
{"name":"prompt-pr","steps":["check","try"],"optional":["try"],"gate":"pr","before":"approve","then":"ask-code"},
{"name":"code","steps":["build","verify","formal","review"],"optional":[],"gate":"pr"}]}
```

- Each area has a `name`, its `steps` in order, the `optional` steps and a `gate`.
- `gate` is `approve` (the person approves, then a new chat starts) or `pr` (pdd opens a PR).
- `"before":"approve"` on a `pr` area makes the person try and approve before pdd opens that PR.
- `"then":"ask-code"` on a `pr` area makes it PR 1. pdd then asks the person before the next area, which makes PR 2. Leave it out for a workflow with one PR, like `small-change`.
- Each step has a file `steps/STEP.md`.
- The last area ends with `pr`. It should have a `verify` step, so that the PR body has the test output.

Keep the rules of the PDD workflows in your `SKILL.md`: the main chat does not write code, each step runs in a fresh subagent, verify runs in a subagent that did not write the code, and the agent never approves or merges. Outside a run, the agent opens a PR only if the person says yes; in a run, pdd does.

`pdd workflow open ISSUE [AREA] [--new]` focuses or resumes the current area's saved session by default. AREA opens a recorded current or earlier area's chat without moving the run or changing its gate and approvals; this does not enforce read-only execution. `--new` replaces only the current area's verified owned chat with one fresh session in the same worktree and saved agent configuration. It archives the old chat, native session identity and original first message, and the continuation explains completed work and any pending gate. Run it from another terminal: replacement refuses from an agent session, from the pane it would close and for an earlier area. Eligibility or ownership refusal before replacement intent leaves the saved run unchanged. Once intent is saved, an interruption retains the pending recovery record. Repeat `pdd workflow open ISSUE --new` to inspect and continue the same current-area attempt or roll it back without a duplicate native session. If its area differs from the current area, recovery only restores a verified usable original or safely ends the attempt; it never launches a fresh agent or resumes a stopped historical agent. Both status State and Next lines name the pending phase and this resolving command. If external inspection is temporarily unavailable or ambiguous, retry that command later; cancel remains available, as do the usual progress and approval commands. Plain open, AREA open and `--new` share the same short run lock; status holds no lock during external calls. Replacement keeps completed work, decisions, approvals and PRs and never approves new work.
