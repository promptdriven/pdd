# PDD Alpha

> Looking for the original Python PDD (`pdd-cli` 0.0.x)? It lives on the [`main` branch](https://github.com/promptdriven/pdd/tree/main) and on PyPI: `pip install pdd-cli`.

**Prompt-driven development for your coding agent.**

> **This is the `alpha` branch of `promptdriven/pdd`.** It holds PDD Alpha, a new command-line tool for Node.js. The `main` branch holds the older Python `pdd-cli`. They are different programs, but both install a command named `pdd`. Read [If you have the old Python pdd](#if-you-have-the-old-python-pdd) before you install.

In PDD, prompts are the source of your software. You and your coding agent write down what the software must do: a prompt for each module, a Story and test cases. Then agents build the code from them.

PDD Alpha takes a GitHub issue to a real pull request:

1. Agents work in stages. Each stage is a fresh Codex or Claude Code session that starts with the [Prompting guide](docs/prompting-guide.md).
2. You approve the plan and its test commands before the agents change code.
3. PDD runs the approved tests itself.
4. PDD opens a real PR on GitHub. It never merges. You review and merge.

> [!WARNING]
> **Agents run with full access.** PDD starts Codex and Claude Code in full-access mode, so they do not stop to ask for approval. They can read, change and delete files and run commands as your user. Use PDD only in projects and on machines where you accept this.

The full guide is in [docs/USAGE.md](docs/USAGE.md).

## Requirements

| You need | Check it with | Get it |
|---|---|---|
| Node.js 22.16 or newer | `node -v` | [nodejs.org](https://nodejs.org) |
| Git 2.36 or newer | `git --version` | [git-scm.com](https://git-scm.com) |
| GitHub CLI, signed in | `gh auth status` | [cli.github.com](https://cli.github.com), then `gh auth login` |
| Herdr (for workflow runs) | `herdr --version` | [herdr.dev](https://herdr.dev). Tested with 0.9.1 |
| Codex CLI or Claude Code, signed in | `codex login status` | [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview) |

Codex is the default agent and the most tested one. PDD Alpha is tested on macOS and Linux. Windows is not tested.

## Install

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version   # prints 0.1.1
which -a pdd    # the first line must be in "$(npm prefix -g)/bin"
```

Always install and update with that full `github:` line. Do not run `npm install -g pdd` or `npm update -g`. The npm registry has a different, unrelated package called `pdd`, and npm would replace PDD Alpha with it.

### If you have the old Python pdd

The Python `pdd-cli` (from the `main` branch and PyPI) also installs a `pdd` command. If `pdd --version` does not print `0.1.1`, the old one comes first on your PATH. Remove it with the tool you used to install it:

```sh
uv tool uninstall pdd-cli    # or: pipx uninstall pdd-cli   or: pip uninstall pdd-cli
hash -r                      # zsh users can also run: rehash
which -a pdd
```

If you want to keep the old one, call PDD Alpha by its full path: `"$(npm prefix -g)/bin/pdd"`. The agents that PDD starts always use the full path, so they are not affected.

## Start a session

<a id="open-an-ordinary-native-session"></a>

```sh
cd your-project
pdd session
```

This opens Codex with the Prompting guide, the PDD skill and the three workflows loaded. The agent summarizes the method and asks what you want to work on. You need no issue and no setup. Plan a change, draft prompts, Stories and test cases, or write code.

You can also give the first request, or pick Claude Code:

```sh
pdd session "Help me write a prompt, a Story and test cases for a CSV export button."
pdd session --agent claude
```

## Run a workflow on a GitHub issue

Run this in a clone of a GitHub repository that you can push to. The issue must be in that same repository.

```sh
cd your-clone
git fetch origin
pdd workflow run small-change 42
```

1. PDD reads issue #42 with `gh`. It makes a new branch (`pdd/small-change-42-…`) and a new Git worktree next to your clone. Your own checkout is not changed.
2. Each stage runs a fresh agent in the background in Herdr. The command stays busy and prints nothing while the agents work.
3. At the approval gate the command stops and prints a line like this:
   ```
   waiting: run 6f1c…-… / change. Review the independent proposal and test plan; resume with approve to advance.
   ```
4. Review the plan. Then approve it with the run ID from that line:
   ```sh
   pdd workflow resume RUN_ID --decision approve
   ```
5. The agents make the change. PDD runs the approved tests, pushes the branch and opens the PR. Then it stops with `Waiting for actual merge of <PR URL>`.
6. Review and merge the PR on GitHub. Then run `pdd workflow resume RUN_ID` once more to mark the run completed.

Pick the workflow that fits the issue:

| Workflow | Use it for | Stages (you act at the **bold** ones) |
|---|---|---|
| `small-change` | A small, contained edit | scope, **approve**, change, verify, open PR, **merge** |
| `bug` | Something is broken | reproduce, prompt and Story, check, try (optional), **approve**, prompt PR (optional), build, verify, code PR, **merge** |
| `feature` | New behavior | understand, visual (optional), prompt and Story, check, try (optional), **approve**, prompt PR (optional), build, verify, code PR, **merge** |

At each optional stage the run stops. Choose `--decision approve` to run it or `--decision skip` to leave it out. For your first runs, skip the optional prompt PR. Then the prompts and the code come in one PR.

To watch or talk to the agent of the current stage, run `pdd workflow attach RUN_ID` in a second terminal. Read [docs/USAGE.md](docs/USAGE.md) for the full steps, how to find the run ID early, and what to do when something stops.

## Commands

| Command | What it does |
|---|---|
| `pdd session [--agent codex\|claude] [request]` | Open your coding agent with PDD loaded |
| `pdd workflow run NAME ISSUE [--agent codex\|claude]` | Run a workflow on a GitHub issue (number, `owner/repo#N` or URL) |
| `pdd workflow resume RUN_ID` | Show where a run is. It starts no new work |
| `pdd workflow resume RUN_ID --decision approve` | Approve the current step and continue the run |
| `pdd workflow resume RUN_ID --decision skip` | Skip the current optional step and continue |
| `pdd workflow attach RUN_ID` | Watch and talk to the agent of the current stage |
| `pdd workflow list [--json]` | List the workflows you can run (not the runs) |
| `pdd workflow feature\|bug\|small-change [request]` | Follow one workflow in a single normal session (no stages, no PR) |
| `pdd --skill` | Print the full Prompting guide and the PDD skill |
| `pdd completion bash\|zsh` | Print shell completion |
| `pdd --help`, `pdd --version` | Help and version |

## Make a workflow your own

Workflows are plain Markdown and JSON. Copy one into your project and edit it:

```sh
mkdir -p .pdd/workflows
cp -R "$(npm prefix -g)/lib/node_modules/pdd/.pdd/workflows/small-change" .pdd/workflows/
pdd workflow list   # small-change now shows "project"
```

A project folder replaces the bundled workflow of the same name. You can also add a new one with a new name. See [docs/USAGE.md](docs/USAGE.md#make-a-workflow-your-own).

## Update and uninstall

```sh
npm install -g github:promptdriven/pdd#alpha   # update to the newest alpha
npm uninstall -g pdd                           # remove PDD Alpha
```

## Known limits of this alpha

- **Keep the terminal of a run open.** If you close it, the agent in Herdr can go on, but PDD stops moving the run forward. When that agent is done, run `pdd workflow resume RUN_ID --decision approve` to go on. A fix ("never lose work") is in progress.
- `pdd workflow run` keeps your terminal busy until the run stops at a gate or ends. There is no command to list runs or to stop a run.
- One run per issue in a clone. A second run on the same issue points back to the first one. There is no "reject" decision. If a plan is wrong, open a new, clearer issue.
- A busy or rate-limited model (HTTP 429) can fail a stage, and resume may not recover it.
- If the agent is not signed in, a stage can stop or hang at a sign-in screen. Check `codex login status` before you start.
- The controller waits at most 30 minutes for one stage. Then it stops with `stage_wait_timeout`. Continue as after a closed terminal.
- The PR step can fail when an agent leaves files that are not committed. The PR title is the last commit message, and the body does not link the issue. Edit them before you merge.
- Do not edit files in a run's worktree while it runs. PDD refuses to continue when the saved input changed.
- `small-change` has made real PRs. `bug` has made one real PR. `feature` is not yet tested on real issues. Claude Code inside workflow runs is less tested than Codex.
- Each session and each stage starts with the full guide (about 21,000 tokens). This uses your agent plan's quota.
- PDD does not remove old worktrees or Herdr sessions. See [Clean up](docs/USAGE.md#clean-up-after-a-run).

## Report a problem

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) on `promptdriven/pdd` and put **[alpha]** at the start of the title. Add your OS, the output of `pdd --version`, `node -v` and `herdr --version`, the agent you used, the command you ran, the run ID and the last lines of output. Do not paste tokens or secrets.

## Documentation

- [Usage guide](docs/USAGE.md): install, sessions, workflow runs, approvals, limits and fixes
- [Prompting guide](docs/prompting-guide.md)
- [PDD skill](skills/pdd/SKILL.md)
- [Sessions](docs/prompt-sessions.md)
- [Workflows in depth](docs/workflows.md)
- [CLI reference](docs/cli.md)
- [Example project](examples/ticket-status/README.md)

## Contributing

Contributions are welcome. Open pull requests against the `alpha` branch. See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

[MIT](LICENSE)
