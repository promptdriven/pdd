# Workflows in depth

A PDD workflow is a skill: a folder of plain Markdown and one JSON file. Your agent follows it. pdd itself does only four things: it starts the run, it holds the gates, it opens the PR and it shows the status.

## The three workflows

| Workflow | Use it for |
|---|---|
| `pdd-small-change` | A small change with a clear effect that is easy to undo. If the impact grows, the agent suggests `bug` or `feature`. |
| `pdd-bug` | The code breaks an accepted expectation. |
| `pdd-feature` | New behavior. |

Each workflow has areas. Each area has steps and ends at a gate. `?` marks an optional step.

| Workflow | Area 1 | Area 2 | Area 3 |
|---|---|---|---|
| `small-change` | plan: scope, gate **approve** | build: change, verify, gate **PR** | |
| `bug` | solution: reproduce, prompt-story, check, try?, gate **approve** | build: build, verify, gate **PR** | |
| `feature` | solution: understand, visual?, gate **approve** | story: prompt-story, check, try?, gate **approve** | build: build, verify, gate **PR** |

What each step does:

| Step | What the subagent does |
|---|---|
| scope | States the result, the files, why the change is small and how to undo it. Writes the expected result and names the test command. |
| change | Makes only the approved change. If a prompt owns the behavior, it changes the prompt first. Adds a test. |
| reproduce | Finds the smallest safe input that shows the bug. Writes the expected and the actual result. |
| understand | States the wanted result, what must not change and what is out of scope. |
| visual? | For a visible interface, sketches 2 or 3 options, with empty and error states. |
| prompt-story | Reads the full Prompting guide. Writes or changes the prompt, the Story and the test cases. Takes the expected results from the requirement, not from the code. |
| check | Reviews the prompt and the cases with the `pdd-prompting` review rules. Traces cases through the prompt. |
| try? | Shows the plan or the bug in a safe local preview or demo, if the repo has one. |
| build | Builds only what you approved. Tests through the public interface. |
| verify | Runs the tests and the repo's required checks. Writes the exact commands and their real output. |

Only prompt-story reads the full Prompting guide. check reads the `pdd-prompting` core rules and review rules. change reads the guide only when it changes a prompt.

## Two ways to use a workflow

| | In one chat | As a run on an issue |
|---|---|---|
| Start | `pdd workflow NAME [request]`, or ask your agent in any chat | `pdd workflow run NAME ISSUE` |
| Branch and worktree | No. The agent works in your folder | Yes. A new branch and worktree for the issue |
| Chats | One | One for each area, in Herdr |
| Gates | The agent asks you | pdd holds them. You approve in the chat or with `pdd workflow approve` |
| PR | No. Ask the agent if you want one | pdd opens one PR. It never merges |

## How a run works

```
pdd workflow run feature 42        returns at once
  |
chat 1  solution: understand, visual?
  |     gate: approve
chat 2  story: prompt-story, check, try?
  |     gate: approve
chat 3  build: build, verify
  |     pdd pushes the branch and opens the PR
you     review and merge the PR on GitHub
```

1. `pdd workflow run` reads the issue, makes the branch, the worktree and the run folder, and opens the first chat in Herdr. Then it returns. You can close the terminal.
2. The first message of the chat is short. It names the skill, the issue, the worktree, the run folder and the area with its steps.
3. The main chat coordinates and talks with you. It does not write code itself.
4. The main chat gives each step to a fresh subagent and never reuses it. The subagent gets a short brief and file paths, not the chat history.
5. After each step, the agent runs `pdd workflow done STEP --summary "..."`. pdd records the step and tells the agent what comes next: the next step, a gate, or "pdd opens the PR now". An unknown or out-of-order step gives a warning. It does not stop the run.
6. At a gate, the chat shows the result, asks you and stops. There is no time limit.
7. If you ask for changes, the same chat revises and asks you again. The gate stays open.
8. If you approve, pdd starts a new chat for the next area. That chat gets the outputs of the approved area: the files, the summaries and the run folder.
9. After the last build step, pdd pushes the branch and opens the PR.
10. You merge the PR on GitHub. `pdd workflow status` reads the PR state. When the PR is merged, the run is completed.

### Who can approve

Only a person approves a gate. The agent never approves for you.

- In a terminal: `pdd workflow approve N` asks y/N. The question shows the repo, the issue and its title.
- In the chat: say it in your own words. The agent then runs `pdd workflow approve`. pdd checks that your own message is in the chat after the gate. If it is not there, pdd refuses.

### The run folder

Each run has a run folder. The first message of each chat names it.

| File | What it holds |
|---|---|
| `STEP.md` (one for each step) | The notes of that step |
| `verify.md` | The exact test commands and their real output |
| `status.json` | The area, the step, what the run waits for and the PR |

The code that the steps write is committed on the run's branch, in the run's worktree.

## Tests and evidence

pdd does not run tests. The agents do.

- The verify step runs in a fresh subagent that did not write the code.
- It runs the new cases, the regression tests and the repo's required checks. When it can, it shows that a new test fails on the old or wrong code, in a throwaway copy.
- It writes the exact commands, the exit codes and the real output to `verify.md`. It names what no test covers.
- The PR body includes `verify.md`.

Read that output before you merge. Passing tests are useful evidence. They are not proof of all behavior. A test that was only written is not a test that ran.

The [ticket-status example](../examples/ticket-status/README.md) shows a full prompt, Story, test cases, code and tests. Run its tests from the repository root:

```sh
node --test examples/ticket-status/test/status.test.mjs
```

<a id="make-your-own-workflow"></a>

## Make your own workflow

### Where skills live

| Level | Codex | Claude Code |
|---|---|---|
| For you, in all projects | `~/.agents/skills/NAME/` | `~/.claude/skills/NAME/` |
| For one project (commit it) | `.agents/skills/NAME/` in the repo | `.claude/skills/NAME/` in the repo |

pdd installs its four skills at the "for you" level. Each has a `.pdd-skill.json` file. pdd replaces a folder with that file when you update pdd. pdd never changes a folder without that file.

### Copy and edit

```sh
cp -R ~/.agents/skills/pdd-small-change ~/.agents/skills/pdd-docs-fix
rm ~/.agents/skills/pdd-docs-fix/.pdd-skill.json
```

Then edit the copy:

1. In `SKILL.md`, set `name: pdd-docs-fix` and a new `description`. The description tells the agent when to use the skill.
2. Edit the areas in `SKILL.md` and in `workflow.json`. Keep them the same.
3. Edit, add or remove the step files in `steps/`. Keep each one short.
4. Copy the folder to `~/.claude/skills/` too if you use Claude Code.

To use your workflow, ask your agent in a chat, for example: "Use the pdd-docs-fix skill for issue 42."

To change a PDD workflow for all your projects, you can also edit its installed folder and delete its `.pdd-skill.json` file. pdd then keeps your folder and does not update it.

### The files

```
pdd-docs-fix/
  SKILL.md          frontmatter (name, description), when to use it, the areas, the rules
  workflow.json     the areas, their steps and their gates
  steps/
    scope.md        one short brief for each step
    change.md
    verify.md
```

`workflow.json` lists the areas in order:

```json
{"version":2,"areas":[
{"name":"plan","steps":["scope"],"optional":[],"gate":"approve"},
{"name":"build","steps":["change","verify"],"optional":[],"gate":"pr"}]}
```

- Each area has a `name`, its `steps` in order, the `optional` steps and a `gate`.
- `gate` is `approve` (the person approves, then a new chat starts) or `pr` (pdd opens the PR).
- Each step has a file `steps/STEP.md`.
- The last area ends with `pr`. Its last step should be `verify`, so that the PR body has the test output.

Keep the rules of the PDD workflows in your `SKILL.md`: the main chat does not write code, each step runs in a fresh subagent, verify runs in a subagent that did not write the code, and the agent never approves, pushes, opens a PR or merges.
