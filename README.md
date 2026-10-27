# PDD

**Prompt-driven development for Codex and Claude Code.**

In PDD, prompts are the source of your software. Your agent writes the prompt, the Story and the test cases first, then the code. You review the prompts and stay in control.

> Looking for the Python `pdd-cli`? It is on the [`main` branch](https://github.com/promptdriven/pdd/tree/main).

## Quick start

Add the PDD skills to your agent:

```sh
npx skills add promptdriven/pdd
```

Then open Codex or Claude Code in your project, as usual. Run `/pdd-setup` once, then call a skill:

```
/pdd-setup
/pdd-feature Add a CSV export button to the orders page.
```

`/pdd-setup` adds a short PDD note to your `CLAUDE.md` or `AGENTS.md`, so every chat in the repo knows the project uses PDD. Run it once in each repo.

For runs that open pull requests, and for `pdd check`, also install the `pdd` command:

```sh
npm install -g github:promptdriven/pdd#alpha
```

## Skills

| Skill | Use it to |
|---|---|
| `/pdd-feature` | add new behavior |
| `/pdd-bug` | fix something that is broken |
| `/pdd-small-change` | make a small edit that is easy to undo |
| `/pdd-prompting` | write or review prompts with the [Prompting guide](docs/prompting-guide.md) |
| `/pdd-setup` | set up a repo for PDD |

The skills work in any chat. Only the skill you call is loaded, so your chat stays small. Add `-g` to `npx skills add` to install them for all your projects.

## From a GitHub issue to pull requests

```sh
pdd workflow run feature 42
```

pdd opens the work in [Herdr](https://herdr.dev) and returns at once. You can close the terminal.

```
chat 1  story      the agent writes the prompt, Story and tests  → you approve
chat 2  prompt PR  the agent checks the prompts and gives a Try link → you try it and approve → pdd opens PR 1
                   "Do you want the code PR now, or stop here?"
chat 3  code       only if you ask                                → pdd opens PR 2
```

- Talk to the chat at any time. If you ask for changes, the same chat revises.
- Approve in the chat in your own words, or with `pdd workflow approve 42`.
- PR 2 runs PR 1's test cases on the real code and shows the result in a table, with a formal check line.
- `small-change` makes one PR. `bug` works like `feature`.
- Codex is the default agent. Add `--agent claude` for Claude Code.
- The agents run your tests, and each PR shows the real output. **pdd never merges.**

| Command | What it does |
|---|---|
| `pdd workflow status --all` | every run on this machine, the ones waiting for you first |
| `pdd workflow status 42` | where one run is, and what it waits for |
| `pdd workflow open 42` | open the run's chat |
| `pdd workflow approve 42` | approve the gate, or make the code PR |
| `pdd workflow changes 42 "…"` | ask for changes |
| `pdd workflow cancel 42` | stop the run |

## Check your prompts

```sh
pdd check          # run every Story's tests on the PDD runtime
pdd try            # get a link to use the prompt by hand
```

`pdd check` prints one table with a report link for each Story. Your agent reads [RUNBOOK.md](RUNBOOK.md) to write prompts and tests that the runtime can check.

To approve a prompt, run `pdd approve prompts/NAME.prompt.md` in your terminal (or click **Approve** on the Try page while `pdd try` runs). Only a person can approve.

The runtime is invite-only. If `pdd check` says your GitHub login is not on the invite list, ask the PDD team.

## Requirements

- [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview), signed in
- [Node.js](https://nodejs.org) 22 or newer, for `npx` and the `pdd` command
- For the `pdd` command: [Git](https://git-scm.com), the [GitHub CLI](https://cli.github.com) signed in (`gh auth login`), and [Herdr](https://herdr.dev) for workflow runs

PDD works with the versions of these tools that you have. It is tested on macOS and Linux.

## Good to know

> [!WARNING]
> **Agents run with full access.** In a workflow run, Codex and Claude Code do not stop to ask for approval. They can change files and run commands as your user. Use PDD only where you accept this.

- **Update:** run the `npx skills add` and `npm install` lines again. Do not run `npm install -g pdd`, because that is a different package.
- **Old Python pdd:** if `pdd --version` does not print `0.1.4`, the Python `pdd-cli` comes first on your PATH. Remove it with `uv tool uninstall pdd-cli` (or `pipx` or `pip`).
- **Your own workflow:** copy a skill folder as `pdd-NAME` into `.agents/skills` or `.claude/skills`, then edit it. See [Workflows](docs/workflows.md#make-your-own-workflow).
- **This is an alpha.** Read the [known limits](docs/USAGE.md), and [report problems](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) with **[alpha]** in the title.

## Documentation

- [Usage guide](docs/USAGE.md): install, runs, gates, runtime checks, clean up and troubleshooting
- [Workflows](docs/workflows.md): areas, steps and your own workflows
- [CLI reference](docs/cli.md)
- [Prompting guide](docs/prompting-guide.md)

## License

[MIT](LICENSE). Contributions go to the `alpha` branch. See [CONTRIBUTING.md](CONTRIBUTING.md).
