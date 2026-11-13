# PDD onboarding guide

PDD helps you build software from prompts that state what it must do. You test
the prompts and try the behavior before your coding agent builds the code. This
guide takes you from installation to a first reviewed change. It also shows how
to contribute to PDD itself.

Read the [PDD doctrine](prompt-driven-development-doctrine.md) for the reasons
behind this method. Use the [Prompting guide](prompting-guide.md) for authoring
rules and the [RUNBOOK](../RUNBOOK.md) for file formats and checks.

## Understand the parts

| Part | Its job |
| --- | --- |
| Prompts | State each module's behavior and public contract. |
| Stories and test cases | State what a user can do and the results they must get. |
| PDD skills | Instructions that tell your coding agent how to plan, write, check and review a kind of work. |
| The `pdd` command | Sets up a project, sends prompt checks to the interpreter and launches and manages issue workflow runs. |
| The PDD interpreter | Uses AI to act as the prompt program. It fakes declared outside resources. |
| Your coding agent | Writes the prompts, Stories, test cases and implementation. It runs the implementation's checks. |

Prompt tests check the prompt program. Native tests check the code. A pass in
one does not establish a pass in the other.

A skill is instructions for the agent, not a terminal command. For example,
`pdd-feature` gives the agent its method for new behavior, and `pdd-bug` gives
it the method for a defect. The workflow name is shorter: `feature` uses the
`pdd-feature` skill, and `bug` uses the `pdd-bug` skill. You can ask an agent
to use either skill in a normal chat, or start a managed GitHub issue run from
the terminal. The run launches agent chats that follow the same skill while
`pdd` manages the worktree, gates, PRs and status.

## Install PDD and its skills

Use Node.js 22.16.0 or newer, Git, the GitHub CLI and a supported coding agent.
Install and sign in to your agent with your own account. PDD is tested on macOS
and Linux. Sign in to the GitHub CLI with your own account:

```sh
gh auth login
npm install -g github:promptdriven/pdd
npx skills add promptdriven/pdd -g
pdd --version
```

Install the command and the skills from the same source. To update, repeat both
install commands and start a new agent chat. Use the GitHub package shown above.
The npm registry package named `pdd` is a different product.

If you have the Python `pdd-cli` installed, follow the
[installation guidance](USAGE.md) to resolve the shared command name.

Prompt tests, `pdd lint` for interpreter Stories and simulations use the hosted
interpreter. For interpreter Stories, `pdd lint` checks the format and makes
zero AI calls, but needs network access, GitHub sign-in and interpreter access.
Sign up at
[promptdriven.ai/login](https://promptdriven.ai/login) with the same GitHub
account that `gh` uses. Your account needs interpreter access. You can read the
guide and draft files before you have that access. For interpreter Stories,
`pdd lint --local` gives offline, warning-only SVG layout advice. The
`pdd test --files` command is also offline.

## Set up your project

From your project's Git repository, run:

```sh
cd your-project
pdd setup
```

PDD adds a short instruction block to `CLAUDE.md`, or to `AGENTS.md` when there
is no `CLAUDE.md`. It also ignores its local `.pdd/` cache. Review any proposed
agent configuration changes when setup asks.

Open your coding agent in that project. Keep the repo's own instructions
available. Before the agent writes a prompt or Story, it must read the full
[Prompting guide](prompting-guide.md) in that conversation.

## Make your first change

Choose one small behavior that you can check by hand. Ask your agent to use the
appropriate skill:

| You want to | Ask for |
| --- | --- |
| Add behavior | `pdd-feature` |
| Fix a wrong result or error | `pdd-bug` |
| Make a small change that is easy to undo | `pdd-small-change` |
| Plan a whole product | `pdd-product` |
| Write or review prompts | `pdd-prompting` |

The next steps describe feature and bug work. For a small change, use
`pdd-small-change` to agree the scope, build and verify a contained change. In a
direct chat, the agent opens a PR when you ask. Use `pdd-product` for product
planning. Use `pdd-prompting` to author or review prompts.

The agent prepares the owning prompt, a Story and its test file. A file set can
use this language-qualified naming convention:

```text
prompts/orders_JavaScript.prompt.md
user_stories/my-story.md
tests/my-story.json
```

`orders_JavaScript.prompt.md` is an example of
`prompts/NAME_LANGUAGE.prompt.md`: the name before the underscore identifies
the module, and the language suffix can tell people which language it targets.
The language suffix is a naming convention, not a requirement. PDD requires
the `.prompt.md` extension; existing prompt names can omit a language suffix,
such as `prompts/cli/command-catalog.prompt.md`. `my-story` is a placeholder.
Read the actual files. Check the expected results against what you asked for.
Correct the intended behavior before the agent implements it.

Inspect the selected files and run the checks:

```sh
pdd test --files
pdd lint                      # hosted format check; 0 AI calls
pdd test my-story
```

`--files` shows what a check will send without making a network call. For
interpreter Stories, `pdd lint` checks prompt, Story and test format through the
hosted interpreter; `pdd lint --local` gives offline, warning-only SVG layout
advice. It does not check prompt, Story or test format or replace hosted lint.
`pdd test` uses the interpreter and its AI-call budget. Read each `Prompt tests`
result and its report. A draft pass still needs approval.

You can try the prompt program before code exists:

```sh
pdd simulate my-story
```

Use `--cli` for a command line or `--serve PORT` for a local HTTP interface.
See [simulation](USAGE.md) for the full procedure. Keep Simulator links private:
a person with the link can use its AI-call budget.

If a result is wrong, return to the requirement and prompt. The agent can propose
a new expected value; a person decides it. When the behavior is right, approve
the reviewed prompts in chat or with `pdd approve PATH`.

Then ask for the code. The agent implements the approved behavior and runs the
same cases against the code's public interface. It also runs the project's native
checks. Review the actual results and any remaining failures.

## Use a skill in chat or run a GitHub issue

You can use a skill in a normal chat or ask `pdd` to manage an issue run. For a
normal chat, open Codex or Claude Code in your project and type the request in
the agent chat. For example:

```text
Use pdd-feature to add a shipping estimate to the order summary.
Use pdd-bug to fix the wrong total shown for a discounted order.
```

You can also invoke the skills as `$pdd-feature` in Codex or `/pdd-feature` in
Claude Code, and likewise `$pdd-bug` or `/pdd-bug`. In a normal chat, the agent
works in the current checkout. The skill does not create a workflow worktree
or open a PR on its own; ask the agent if you want it to open a PR.

For a managed workflow run, install [Herdr](https://herdr.dev). From a terminal
in your project, run the command for the issue:

```sh
pdd workflow run feature 42
pdd workflow run bug 43
```

Here `feature` maps to `pdd-feature`, and `bug` maps to `pdd-bug`. Replace the
numbers with GitHub issue numbers. The command creates a branch and worktree,
then opens agent chats in Herdr. The agent follows the mapped skill. PDD manages
the run and its PR steps; a direct chat does not start this managed issue run.
Workflow agents run with full access as your user. To inspect a run, use these
terminal commands:

```sh
pdd workflow status 42
pdd workflow view 42
```

For a normal feature or bug run, read the Story card. Approve the behavior and
choose whether to stop after PR 1 or continue to code. With a full prompt check
pass, PDD opens PR 1 for the prompts, Stories and tests. If you chose code, it
then prepares PR 2 for the implementation. A changed Story or expected result
needs another decision. Strict mode retains its approval steps. Autopilot has
its own delegated route. A small change uses one PR.

The [workflow guide](workflows.md#how-a-run-works) owns the exact steps and
approval rules. `pdd-small-change` fits a contained change, `pdd-product` plans
a whole product, and `pdd-prompting` helps author or review prompts. A first
manual change does not require Autopilot.

## Contribute to PDD itself

Use the [contribution guide](../CONTRIBUTING.md) for the development branch and
review route. Read the checkout's `AGENTS.md`. Work on a topic branch and keep
other people's work intact.

For a fast first check from a PDD source checkout, run:

```sh
node bin/pdd.mjs --help
node --test test/cli.test.mjs
```

Run focused tests for the change, then follow the repository's full-suite route.
A prompt test through the interpreter is a separate check.

A useful PR explains the user problem, the prompt and behavior changes, the
actual checks and any remaining limits. Link the issue. State the lines added
and removed. Add a screen image for a visible UI change. Keep logs, reports,
private conversations and credentials outside the source tree.

Follow the repository's review, test and merge rules. An open PR, a merged PR
and a deployed release are separate results.

## Get help

For command forms, use the [CLI reference](cli.md). For an interpreter refusal
or a wrong result, use [troubleshooting](USAGE.md) and the [issue guide](ISSUES.md).
Include the PDD version, the command, the expected result and the actual result.
Remove secrets and private Simulator links.
