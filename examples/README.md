# Examples

This directory contains examples that demonstrate comparisons between using Cursor and Prompt-Driven Development (PDD) for various programming tasks. These examples serve as practical illustrations of how PDD can be used to generate and modify code, via the pdd sync command, and how it compares to traditional development approaches.

## Getting Started

### Post-Installation Setup (Required first step after installation)

Before running any examples, make sure you've completed the PDD setup:

```bash
pdd setup
```

This command will guide you through:
- Installing shell tab completion
- Capturing your API keys
- Creating ~/.pdd configuration files
- Writing the starter prompt

After setup, reload your shell:
```bash
source ~/.zshrc  # or source ~/.bashrc / fish equivalent
```

## Available Examples

### Agentic Fallback
The agentic fallback example demonstrates using agentic fallback to resolve cross-file dependencies during automated debugging.  
The example has two files — `src/main.py` and `src/utils.py` — where `main.py` fails without reading `utils.py`.  
With agentic fallback enabled, the CLI agent (Claude/Gemini/Codex/OpenCode) can read `utils.py`, understand the dependency, and fix `main.py`.
Users may intentionally introduce errors in `src/utils.py` to test the agentic fix functionality.

Additional examples demonstrating the use of agentic fallback are provided for Java, TypeScript, and JavaScript.

### Edit File Tool
The edit_file_tool_example walks through generating a complete Python tool using PDD's streamlined `pdd --force sync` workflow. This example shows:
- How to drive end-to-end project generation (code, tests, docs) from component prompts (complete dev units)
- Using the provided Makefile targets to orchestrate setup, prompt creation, and sync runs
- Integrating automation features like command logging and optional cost tracking during sync

### Handpaint
The handpaint example demonstrates how PDD can be used to create and modify a painting application. This example shows:
- How PDD can be used to generate code for a graphical application
- The process of iteratively refining code through PDD
- A comparison between traditional development and PDD-assisted development

### Hello World
The hello_world example demonstrates how PDD can be used to generate code for a simple Python function that prints "hello". This example shows:
- How PDD can be used to generate code for a simple Python function via the sync command

### Hello You
The hello_you example expands on the Hello World flow by rendering a personalized greeting in large ASCII art. This example shows:
- Capturing the current shell username (via `whoami`) and feeding it into the generated program
- Building a reusable ASCII art alphabet map inside the generated Python file to spell arbitrary strings
- Producing a self-contained script that prints a 10-row tall "Hello <username>" banner with no external dependencies

### Pi Calc
The pi_calc example demonstrates how PDD can be used to generate code for a simple Python function that calculates the value of Pi. This example shows:
- How PDD can be used to generate code for a simple Python function using the sync command

### QR Code Sandwich
The qrcode_sandwich example demonstrates how PDD can be used to generate code that produces scannable QR codes embedded within photorealistic images using ControlNet QR conditioning. This example shows:
- Creating a QR code that blends into a realistic image while remaining scannable
- Leveraging ControlNet QR conditioning in a generated Python script
- Iterating with PDD to refine parameters and results

### Coverage contracts demo
[`coverage_contracts_demo/`](coverage_contracts_demo/) — minimal `pdd coverage --contracts`
walkthrough on a small refund prompt with checked / story-only / test-only /
unchecked / waived / failed statuses. Also includes a legacy non-contract prompt
to verify coverage degrades gracefully.

### Prompt lint + contracts workflow
[`prompt_lint_contract_workflow/`](prompt_lint_contract_workflow/) — same `foo_work`
handler as the contract E2E demo, packaged as a **decomposed command playbook**
(per-phase `reports/phase1_*.json` snapshots). A bundled `run_phase1.sh` and
`guidance/` notes are planned follow-on work; see the demo's README for the
manual command sequence.

### Cost tracker strict A/B pipeline (WIP)
[`cost_tracker_strict_ab/`](cost_tracker_strict_ab/) — authoring artifacts for a
planned controlled A/B demo. The deterministic Experiment A driver, golden pytest
harness, and `--live-ab` demo wrapper depend on `pdd evidence` / `pdd gate` /
`pdd contracts drift`, which are not yet on this branch. The directory ships
captured `reports/` snapshots as regression fixtures; see its README.

### Contract commands E2E (cost_tracker)
[`contract_commands_cost_tracker_e2e_demo/`](contract_commands_cost_tracker_e2e_demo/) —
runs the deterministic contract pipeline (`pdd prompt lint`, `pdd contracts
check`, `pdd contracts compile`, `pdd coverage --contracts`) on a baseline vs.
contracts-enriched copy of
[`cost_tracker_utility_Python.prompt`](template_example/prompts/cost_tracker_utility_Python.prompt)
from template_example. CI: `pytest tests/test_contract_commands_cost_tracker_e2e_demo.py`.

### Prompt lint + contracts E2E demo
[`prompt_lint_contract_e2e_demo/`](prompt_lint_contract_e2e_demo/) — companion
end-to-end demo for the `foo_work` handler used by the workflow example above;
wraps everything in a single `demo.sh` and shows the vague -> formalized
contrast in one run.

More examples will be added to this directory as they are developed.

## Purpose
These examples are designed to help developers understand:
1. The capabilities of PDD in different programming contexts
2. How PDD compares to traditional development workflows
3. Best practices for using PDD effectively
4. Real-world applications of PDD in various domains

Each example includes documentation and code that can be used as a reference for your own PDD-based development projects.
