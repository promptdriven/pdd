# pdd-cli

[![PyPI](https://img.shields.io/pypi/v/pdd-cli?color=blue&label=PyPI)](https://pypi.org/project/pdd-cli/)
[![Python](https://img.shields.io/pypi/pyversions/pdd-cli)](https://pypi.org/project/pdd-cli/)
[![License: MIT](https://img.shields.io/pypi/l/pdd-cli)](https://github.com/promptdriven/pdd/blob/main/LICENSE)

[**Website**](https://promptdriven.ai) | [**Docs**](https://github.com/promptdriven/pdd/tree/main/docs) | [**GitHub**](https://github.com/promptdriven/pdd) | [**Releases**](https://github.com/promptdriven/pdd/releases)

**`pdd-cli`** is the Python package for [**Prompt Driven Development (PDD)**](https://promptdriven.ai) (`@promptdriven/pdd`). Write plain-Markdown prompts and Stories as your source of truth, and test and run them directly with the PDD interpreter.

## Highlights

- **Prompts are your source code:** Write plain-English prompts and user Stories describing what your app should do.
- **Test before writing code:** Catch bugs, edge cases, and requirement gaps while you're still in Markdown with `pdd lint` and `pdd test`.
- **Run prompts like real apps:** Launch interactive UIs, CLIs, and APIs straight from your prompts to see and feel the behavior before building it.
- **Prove your code actually works:** Run `pdd prove` to verify every change passes real end-to-end checks before you ship.
- **Works with the agents you already use:** Run `pdd setup` once to connect Claude Code, Codex, Gemini CLI, and Antigravity.

## 1. Install

Requires [Node.js](https://nodejs.org) `>=22.16.0` and [Git](https://git-scm.com) (plus `gh auth login` for hosted interpreter runs).

```sh
pip install pdd-cli
```

> **Note:** Install `pdd-cli` (not `pdd`, which is an unrelated package on PyPI).

Also available via `uv tool install pdd-cli`, `pipx install pdd-cli`, or `npm install -g @promptdriven/pdd`. Upgrade with `pip install -U pdd-cli`.

## 2. Quick Start

```sh
pdd setup          # Install the /pdd skill and agent MCP tools
cd your-repo
pdd init           # Connect your repository to PDD
```

Then open your coding agent and run `/pdd` (Claude Code) or `$pdd` (Codex).

## 3. Core Commands

| Command | What it does |
| --- | --- |
| `pdd status` | View prompts, Stories, and coverage offline |
| `pdd lint` | Check prompts and Stories locally |
| `pdd test` | Run Story tests with the PDD interpreter |
| `pdd prove` | Verify every change passes real checks before you ship |
| `pdd upgrade` | Update `pdd` and installed skills |

Run `pdd --help` for the full command list.

## Links

[promptdriven.ai](https://promptdriven.ai) · [Documentation](https://github.com/promptdriven/pdd/tree/main/docs) · [CLI Reference](https://github.com/promptdriven/pdd/blob/main/docs/cli.md) · [Issues](https://github.com/promptdriven/pdd/issues) · [MIT License](https://github.com/promptdriven/pdd/blob/main/LICENSE)
