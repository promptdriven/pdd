---
name: pdd-prompting
description: The PDD Prompting guide. Use when you write, change or review a module prompt (*.prompt.md), a Story or test cases, when the person asks how to write prompts in PDD, or asks to set up real behavior verification for a repository. In PDD, prompts are the source and code follows them.
metadata:
  pdd-skills: 0.1.35
---

# PDD prompting

Each module's `.prompt.md` is the source; code implements it.

## Core rules

- Read `RUNBOOK.md` first, `guide.md` in full before prompts/cases, and `story-guide.md` before a Story; open routed `runbook/*.md` files when needed.
- Change the prompt first, then code.
- One prompt per module: purpose, `## Domain decisions` (technical invariants/bounds) and failure edges. Give each rule one owner prompt. Link shared rules instead of copying. For a CLI, say if a rule belongs to the whole-CLI prompt or to one module's prompt.
- Inject outside effects (DB, files, net, clock, RNG, programs) via `<port>.<op>` ports; never link `kind: native-only` adapters under `## Dependencies` of checkable prompts ([RUNBOOK §21](runbook/cli-and-ports.md#21-fake-the-outside-world)).
- Linked `.ui.svg` is the layout spec: parts, words, order, ids and states. Check with `pdd lint --local`; render PNGs only if asked (RUNBOOK §13).
- Derive expectations from requirements (`1` observable check per material claim); never copy code output.
- Show prompt, Story and cases first. Record actual chat approval with --said (RUNBOOK §2), never invent it.
- Do not run `pdd lint` before `pdd test`; test includes lint. Report only real output.

## Files

- `RUNBOOK.md`: concise topic router and core commands (`pdd test`, `pdd lint --local`, `pdd simulate`).
- `guide.md`: the Prompting guide.
- `story-guide.md`: Story sizing and criteria rules.
- `review.md`, `verification-setup.md`, `verification-recipe.md`, `autopilot-job-rules.md`: check, code and Autopilot references.

## How to write

1. Name applicable `guide.md` rules and find the owning prompt.
2. Write or change the prompt. Use `0` Stories + `"No Story:"` for internal changes, edit the existing Story when changing a slice, or write 1 cohesive standalone-loop Story in the person's words, with no function calls or type names.
3. Derive normal, limit and error cases (`<= 15` steps, `1` observable check per material claim; align `simulation_overrides` ports) and run `pdd files` + `pdd lint --local`.
4. Show drafts and open choices.
5. After changing prompt, Story and tests, run `pdd test` as RUNBOOK.md says, and show the person the `Prompt tests` line(s) and the report link(s). Offer `pdd simulate STORY`. If a check fails, show it; never change the expected value yourself.

Without prompts, use code, callers and tests as evidence. Change no code until asked.

Workflow skills: pdd-small-change, pdd-bug, pdd-feature and pdd-product.
