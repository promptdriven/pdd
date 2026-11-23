# pdd-cli

[![PyPI](https://img.shields.io/pypi/v/pdd-cli?color=blue&label=PyPI)](https://pypi.org/project/pdd-cli/)
[![Python](https://img.shields.io/pypi/pyversions/pdd-cli)](https://pypi.org/project/pdd-cli/)
[![License: MIT](https://img.shields.io/pypi/l/pdd-cli)](https://github.com/promptdriven/pdd/blob/main/LICENSE)
[![GitHub](https://img.shields.io/badge/GitHub-promptdriven%2Fpdd-181717?logo=github)](https://github.com/promptdriven/pdd)

[**Website**](https://promptdriven.ai) | [**Docs**](https://github.com/promptdriven/pdd/tree/main/docs) | [**CLI Reference**](https://github.com/promptdriven/pdd/blob/main/docs/cli.md) | [**GitHub**](https://github.com/promptdriven/pdd) | [**Releases**](https://github.com/promptdriven/pdd/releases)

**`pdd-cli`** is the Python package for [**Prompt Driven Development (PDD)**](https://promptdriven.ai) (`@promptdriven/pdd`). Write plain-Markdown prompts and Stories as your source of truth, test and simulate them directly with the PDD interpreter before any code exists, then generate and prove real working code with your coding agent (Claude Code, Codex, Gemini CLI, or Antigravity).

> **Install `pdd-cli`, not `pdd`:** The unrelated `pdd` package on PyPI (and on npm) is a different project. Always install `pdd-cli` via Python or `@promptdriven/pdd` via npm.

## Highlights

- **Prompts as source:** Plain-Markdown `prompts/*.prompt.md` files and readable `user_stories/*.md` Stories stay the source of truth for owned modules.
- **Test before writing code:** Run `pdd lint` offline (`0` AI calls, `0` network calls) and `pdd test` on the PDD interpreter to verify behavior before codegen.
- **Interactive preview:** Try screens, CLIs, and HTTP APIs interactively with `pdd sim` before building implementation code.
- **Real code proof:** Run `pdd prove` to verify offline lint, diff checks, repository tests, and `verify.paths` recipes against your base branch.
- **Works with your coding agent:** `pdd setup` installs one unified `/pdd` skill (`$pdd` in Codex, `/pdd` in Claude Code) and previews Simulator MCP registration across Codex, Claude Code, Gemini CLI, and Antigravity.

## Installation

### Requirements

- [Node.js](https://nodejs.org) `>=22.16.0` on `PATH` (`>=22.20.0` for Autopilot)
- [Git](https://git-scm.com)
- [GitHub CLI](https://cli.github.com) signed in with `gh auth login` for hosted interpreter commands (`pdd test`, `pdd lint --remote`, `pdd sim`, and `pdd mcp`; sign up at [promptdriven.ai/login](https://promptdriven.ai/login))

Local commands (`pdd setup`, `pdd init`, `pdd status`, `pdd lint`, `pdd prove`, `pdd owner`, `pdd files`, and `pdd update`) run 100% locally offline.

### Install `pdd-cli`

Install with `pip`:

```sh
pip install pdd-cli
pdd --version
```

Upgrade an existing `pip` install with `pip install -U pdd-cli`.

Install in an isolated environment with `uv` or `pipx`:

```sh
uv tool install pdd-cli
# or
pipx install pdd-cli
```

Or install directly with npm:

```sh
npm install -g @promptdriven/pdd
```

`pdd-cli` bundles the matching `@promptdriven/pdd` release and provides `pdd` (plus `pdd-codex` and `pdd-claude` for Cloud account sessions).

## Quick Start

```sh
pdd setup        # Install the /pdd skill globally and configure agent MCP tools
cd your-repo
pdd init         # Add the 4-line PDD block to CLAUDE.md or AGENTS.md
```

Open your coding agent in your repository and invoke `/pdd` (Claude Code) or `$pdd` (Codex), or run the core commands directly:

```sh
pdd lint         # Offline structural, SVG, and scenario checks (0 AI calls)
pdd test         # Run Story tests on the PDD interpreter
pdd sim          # Try prompts interactively in the PDD Simulator
pdd prove        # Verify lint, repo tests, and verify.paths against base
```

## Core Commands

| Command | Description |
| --- | --- |
| `pdd setup [--yes]` | Install the global `/pdd` skill and preview Simulator MCP setup for detected agents. |
| `pdd init` | Add the 4-line PDD block to `CLAUDE.md` (else `AGENTS.md`) and detect stack and tests. |
| `pdd status [--changed] [--json]` | Show an offline overview of prompts, Stories, file ownership, and `verify.paths` coverage. |
| `pdd lint [STORY...] [--diff [BASE]]` | Run fast offline structural, SVG, scenario, and diff lint (`0` AI calls, `0` network calls). |
| `pdd test [STORY...]` | Run Story tests on the PDD interpreter (`--files` previews uploads; `--target code` tests local CLI code). |
| `pdd sim [STORY]` | Try prompts or Stories interactively in the PDD Simulator (short for `pdd simulate`; supports `--cli`, `--serve [PORT]`). |
| `pdd approve PROMPT` | Review a prompt diff and record approval (terminal y/N or `--said WORDS`). |
| `pdd prove [--base REF]` | Run offline lint, diff checks, repository tests, and `verify.paths` recipes against `REF`. |
| `pdd mcp` | Serve the current repository's Simulator Try tools over stdio MCP. |

Run `pdd --help` for all commands or `pdd <command> --help` for full options.

## Documentation & License

- **Website:** [promptdriven.ai](https://promptdriven.ai)
- **Guides:** [Documentation](https://github.com/promptdriven/pdd/tree/main/docs), [Usage Guide](https://github.com/promptdriven/pdd/blob/main/docs/USAGE.md), and [CLI Reference](https://github.com/promptdriven/pdd/blob/main/docs/cli.md)
- **Issues:** [github.com/promptdriven/pdd/issues](https://github.com/promptdriven/pdd/issues)
- **License:** [MIT](https://github.com/promptdriven/pdd/blob/main/LICENSE)
