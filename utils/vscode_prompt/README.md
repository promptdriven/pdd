# Prompt Driven Development (PDD) Extension

Build software with prompts as the durable source of truth. This extension provides first‑class editing for `.prompt` files—clear syntax highlighting and editor behaviors—so requirements stay human‑readable while code becomes a regenerable artifact.

Why this matters: AI agents can draft code in seconds, but teams often spend hours repairing breakage and drift. Instead of treating prompts as one‑off instructions, PDD formalizes the prompt as the canonical spec. You iterate on the prompt; the system regenerates code deterministically and safely.

## Features

- Syntax highlighting for `.prompt` files
- Language configuration for predictable editing (comments, brackets)
- Works alongside `pdd` CLI to turn prompts into code

Learn more:
- Whitepaper with Benchmarks: https://github.com/promptdriven/pdd/blob/main/docs/whitepaper_with_benchmarks/whitepaper_w_benchmarks.md
- Getting started with PDD (Gemini setup): https://github.com/promptdriven/pdd/blob/main/examples/SETUP_WITH_GEMINI.md
- PDD repository: https://github.com/promptdriven/pdd
- LinkedIn thread (background + discussion): https://www.linkedin.com/posts/gltanaka_ai-softwaredevelopment-devtools-activity-7366248249604648960-ylTA

## Why PDD vs. Spec-Driven and Vibe Coding

- Spec-driven aims for spec → code. PDD inserts an explicit engineering layer: spec → prompts → code. Developers refine the partitioning into a suite of precise, version-controlled prompts (easier to tune than partitioning code), then regenerate artifacts deterministically.
- Vibe coding is ad‑hoc prompting and auto‑accepting. PDD couples every prompt with automated validation; generated code is accepted only if tests pass. No surprise changes—reviewable diffs and test‑gated merges.
- PDD is built for real projects: modular prompts, few‑shot context reuse, and regeneration that reduces drift. The whitepaper documents measurable benefits and benchmarks on non‑toy codebases.

## Further Reading

- Whitepaper with Benchmarks: https://github.com/promptdriven/pdd/blob/main/docs/whitepaper_with_benchmarks/whitepaper_w_benchmarks.md
- Getting started with PDD (Gemini setup): https://github.com/promptdriven/pdd/blob/main/examples/SETUP_WITH_GEMINI.md
- PDD repository: https://github.com/promptdriven/pdd
- LinkedIn thread announcing PDD and community discussion: https://www.linkedin.com/posts/gltanaka_ai-softwaredevelopment-devtools-activity-7366248249604648960-ylTA

| Approach     | Source of truth        | Change process                   | Acceptance gate                 |
|--------------|------------------------|----------------------------------|---------------------------------|
| Vibe coding  | Ad‑hoc prompts         | Manual edits + autofix           | Human eyeballing                |
| Spec‑driven  | Static spec document   | Spec → code (direct synthesis)   | Reviews; fragile regeneration   |
| PDD          | Versioned prompt suite | Spec → prompts → code (regenerate) | Automated tests + review        |

## Requirements

- Visual Studio Code (or Cursor) 1.96+ recommended

## Installation

- Marketplace (recommended): install from the VS Code/Cursor marketplace (search “Prompt Driven Development (PDD)”).
- Local VSIX (for development): see “Package & Local Install (.vsix)” in vsc-extension-quickstart.md.

## Get Started

- Create a `.prompt` file that expresses intent and constraints.
- Use this extension to edit and validate the prompt with good ergonomics.
- Use `pdd` tooling to synthesize code from the prompt and keep artifacts in sync.

Helpful links:
- PDD repo: https://github.com/promptdriven/pdd
- Setup guide (Gemini): https://github.com/promptdriven/pdd/blob/main/examples/SETUP_WITH_GEMINI.md

Extension contributes:
- Custom language support for `.prompt`
- File association and syntax highlighting

## Release Notes

### 0.0.1

Initial release with syntax highlighting for `.prompt` files.

---

## Contributing

If you'd like to contribute to this extension, please visit our repository and submit a pull request.

---
