# Prompt Driven Development (PDD) Extension

[![▶ Watch the overview video](https://img.youtube.com/vi/5lBxpTSnjqo/maxresdefault.jpg)](https://www.youtube.com/watch?v=5lBxpTSnjqo)

Build software with prompts as the durable source of truth. This extension provides first‑class editing for `.prompt` files—clear syntax highlighting and editor behaviors—so requirements stay human‑readable while code becomes a regenerable artifact.

Why this matters: AI agents can draft code in seconds, but teams often spend hours repairing breakage and drift. Instead of treating prompts as one‑off instructions, PDD formalizes the prompt as the canonical spec. You iterate on the prompt; the system regenerates code deterministically and safely.

## Features

- Syntax highlighting for `.prompt` files
- Language configuration for predictable editing (comments, brackets)
- PDD CLI installation using uv (the modern Python package manager)
- Automatic detection across multiple installation methods (uv tools and common paths)
- Works alongside `pdd` CLI to turn prompts into code

Learn more:

- Whitepaper with Benchmarks: https://github.com/promptdriven/pdd/blob/main/docs/whitepaper_with_benchmarks/whitepaper_w_benchmarks.md
- PDD repository: https://github.com/promptdriven/pdd
- LinkedIn thread (background + discussion): https://www.linkedin.com/posts/gltanaka_ai-softwaredevelopment-devtools-activity-7366248249604648960-ylTA

## Why PDD vs. Spec-Driven and Vibe Coding

- Spec-driven aims for spec → code. PDD inserts an explicit engineering layer: spec → prompts → code. Developers refine the partitioning into a suite of precise, version-controlled prompts (easier to tune than partitioning code), then regenerate artifacts deterministically.
- Vibe coding is ad‑hoc prompting and auto‑accepting of code patches. It is like throwing a grenade in the codebase: you never know what will be changed, deleted or duplicated. In contrast, PDD couples every prompt with automated validation; generated code is accepted only if tests pass. No surprise changes—reviewable diffs and test‑gated merges.
- PDD is built for real projects: modular prompts, few‑shot context reuse, and regeneration that reduces drift. The whitepaper documents measurable benefits and benchmarks on non‑toy codebases.


| Approach     | Source of truth        | Change process                          | Acceptance gate               |
| ------------ | ---------------------- | --------------------------------------- | ----------------------------- |
| Vibe coding  | Traditional code files | Prompts that auto-patch code files      | Human eyeballing              |
| Spec‑driven | Static spec document   | Spec → code (direct synthesis/patches) | Reviews; fragile regeneration |
| PDD          | Versioned prompt suite | Spec → prompts → code (regenerate)    | Automated tests + review      |

## Requirements

- Visual Studio Code 1.96+ or any OpenVSX-compatible IDE
- Compatible with VS Code, Cursor, VSCodium, Gitpod, Kiro, Windsurf, and other OpenVSX-compatible editors

## Installation

### VS Code Marketplace
Install directly from the VS Code marketplace in VS Code or compatible editors.

### OpenVSX Marketplace
For OpenVSX-compatible IDEs (VSCodium, Gitpod, Kiro, Windsurf, etc.), install from the OpenVSX marketplace:
- VSCodium: Search for "Prompt Driven Development" in the Extensions view
- Gitpod: Available through the OpenVSX marketplace integration
- Kiro: Available through the OpenVSX marketplace integration
- Windsurf: Available through the OpenVSX marketplace integration
- Other OpenVSX-compatible editors: Use the OpenVSX marketplace URL

## PDD CLI Installation

### Installation System

New in v0.0.3: The extension now provides an intelligent installation system that detects your environment and offers the best installation method for your setup.

#### Automatic Detection
The extension automatically detects if PDD CLI is installed via:
- uv tools (recommended method)
- Direct PATH installations
- Common installation paths (including base anaconda/miniconda environments)

#### Installation
When PDD CLI is not found, the extension will prompt to install it using uv (the modern Python package manager). If uv isn't installed, the extension will install it first with your permission.

Benefits of uv:
- Latest PDD CLI version with all features
- Faster installation and updates
- Isolated tool environment
- Modern Python package management

#### Available Commands
- `PDD: Install PDD CLI` - Install PDD CLI using uv
- `PDD: Check PDD CLI Installation` - Verify current installation
- `PDD: Run PDD Setup` - Configure API keys and settings
- `PDD: Upgrade PDD to uv Installation` - Ensure using latest uv-based installation

### Manual Installation

For custom setups or manual installation:
- Getting started with PDD CLI: https://github.com/promptdriven/pdd#readme
- uv installation: `uv tool install pdd-cli`

## Get Started

- Create a `.prompt` file that expresses intent and constraints.
- Use this extension to edit and validate the prompt with good ergonomics.
- Use `pdd` tooling to synthesize code from the prompt and keep artifacts in sync.

Extension contributes:

- Custom language support for `.prompt`
- File association and syntax highlighting
- PDD CLI installation using uv
- Cross-platform support (macOS, Linux, Windows)
- Automatic environment detection (uv tools, common paths)
- Command palette integration for PDD operations
- Toast notifications for better user experience
- Optional setup - users can configure when ready

## Release Notes

### 0.0.3

- New Installation System
  - uv-only installation: Removed pip support for simpler, more reliable installation
  - Detection across multiple installation methods (uv tools, common paths)
  - Automatic uv installation with user consent
  - Cross-platform support (macOS, Linux, Windows)
  - Toast notifications instead of modal dialogs for better UX
  - Optional setup - no longer automatically runs after installation
  - New "Upgrade to uv Installation" command to ensure latest installation
  - Comprehensive test suite (31 passing tests)
  - Error handling and fallback options

### 0.0.2

- Extended IDE Compatibility

  - Updated metadata and documentation to support OpenVSX-compatible editors such as VSCodium, Cursor, Gitpod, Kiro, and Windsurf.
  - Improved extension description and keywords for better discoverability across marketplaces (VS Code + OpenVSX).

- Documentation Enhancements

  - Expanded README and quickstart instructions for alternative IDEs.
  - Added installation notes and clarified usage across platforms.

- Build & Metadata Updates

  - Improved Makefile `install` target messaging for editor CLIs.


### 0.0.1

Initial release with syntax highlighting for `.prompt` files.

---

## Contributing

If you'd like to contribute to this extension, please visit our repository and submit a pull request.

---
