# PDD

**Prompt-driven development for your coding agent.**

Describe what your software should do in prompts, Stories and test cases. Your coding agent builds it, runs your tests and opens the pull request.

## Install

```sh
npm install -g github:promptdriven/pdd_alpha
```

Requires Node.js 22.16+ and [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview). If you have the older Python `pdd`, uninstall it first: `uv tool uninstall pdd-cli` or `pip uninstall pdd-cli`.

## Quickstart

```sh
cd your-project
pdd session
```

This opens your coding agent with the Prompting guide and the PDD workflows loaded. Plan a feature, draft prompts and Stories, or write code. No setup and no issue needed.

## Run a workflow on a GitHub issue

```sh
pdd workflow run feature 42
```

PDD works on issue #42 in its own branch and worktree. Each step runs in a fresh agent session. You approve the plan, PDD runs your tests and opens the PR, and you merge.

Needs Git, [GitHub CLI](https://cli.github.com) and [Herdr](https://herdr.dev).

## Highlights

- **Prompting guide.** A clear method for prompts, Stories and test cases that agents can build from.
- **Three workflows.** `feature`, `bug` and `small-change`, written in plain Markdown that you can edit.
- **A fresh session for every step.** Each step gets the guide, its instructions and the earlier results.
- **Many issues at once.** Each issue gets its own worktree and branch.
- **Real tests and real PRs.** PDD runs your project's tests before it opens a PR. It never merges.
- **Your tools, your accounts.** Everything runs on your machine with your own agent and GitHub.

## Commands

| Command | What it does |
|---|---|
| `pdd session [--agent codex\|claude]` | Open your coding agent with PDD loaded |
| `pdd workflow run NAME ISSUE` | Run a workflow on a GitHub issue |
| `pdd workflow resume RUN_ID --decision approve` | Approve a step and continue a run |
| `pdd workflow attach RUN_ID` | Watch and talk to the step that is running |
| `pdd workflow list` | List the available workflows |

## Good to know

- PDD starts agents in full-access mode, so they don't stop to ask for approval.
- While a workflow runs, keep its terminal open. If you close it, continue with `pdd workflow resume`.

## Documentation

- [Prompting guide](docs/prompting-guide.md)
- [Sessions](docs/prompt-sessions.md)
- [Workflows](docs/workflows.md)
- [CLI reference](docs/cli.md)
- [Example project](examples/ticket-status/README.md)

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

[MIT](LICENSE)
