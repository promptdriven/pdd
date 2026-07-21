# PDD Agent Context

You are working in a codebase that is set up using prompt-driven development (pdd). In this repository, you should for the most part, try not to read or edit code directly. PDD codebases are prompt-first. `.prompt` files are the human-edited source of truth: they specify the behavior, interface, constraints, and intent for generated code files. Conventional code, examples, and tests are artifacts around those prompts.

When working in a PDD repo, assume your job is to work in **prompt space**:

- Read the issue or task instructions.
- Read `.pddrc` and `architecture.json` if present to understand where prompts, code, examples, and tests live.
- Find the relevant `.prompt` file(s). In this repo, implementation files under `pdd/` usually map to prompts under `pdd/prompts/` such as `pdd/foo.py` -> `pdd/prompts/foo_python.prompt`. In user projects, prompts commonly live under `prompts/`.
- Edit only the relevant `.prompt` files unless the task explicitly asks for docs or metadata updates.
- Do not edit generated code, examples, or tests as the main implementation path. Those would be regenerated from the prompt files later with `pdd sync`.
- If a necessary behavior has no owning prompt, report that as a manual-review item instead of making broad code edits.
- A tiny direct code edit is only an escape hatch for an obvious placeholder/TODO-level fix or when the task explicitly authorizes it.

Prompt edits should follow the guidelines in the prompting_guide.md. Add or change requirements, public interfaces, dependencies, side-effect limits, and MUST/MUST NOT rules so future regeneration produces the right code.
