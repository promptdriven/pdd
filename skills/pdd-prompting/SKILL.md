---
name: pdd-prompting
description: The PDD Prompting guide. Use when you write, change or review a module prompt (*.prompt.md), a Story or test cases, when the person asks how to write prompts in PDD, or asks to set up real behavior verification for a repository. In PDD, prompts are the source and code follows them.
metadata:
  pdd-skills: 0.1.34
---

# PDD prompting

Each code module's `.prompt.md` is the source; code implements it.

## Core rules

- Read `RUNBOOK.md` first, `guide.md` in full before writing/changing prompts or cases, and `story-guide.md` before a Story. Use `RUNBOOK.md`'s fast path; do NOT open `runbook/*.md`, `review.md`, `verification-*.md`, or `autopilot-job-rules.md` during authoring unless hitting a named router edge case.
- Change the prompt first, then the code.
- One prompt per module: purpose and behavior. Give each rule one owner prompt. Link to a shared rule. Do not copy it. For a CLI, say if a rule belongs to the whole-CLI prompt or to one module's prompt.
- Keep caller behavior and important edges. Outside code (database, files, network, clock, randomness, programs): use an injected `<port>.<op>` port, never direct calls, and never link `kind: native-only` adapters under `## Dependencies` of checkable prompts ([RUNBOOK §21](runbook/cli-and-ports.md#21-fake-the-outside-world)).
- Linked `.ui.svg` is the layout spec: parts, words, order, ids and states. Check with `pdd lint --local`; render PNGs only if asked (RUNBOOK §13).
- Derive expectations from requirements before code; never copy code output.
- Show prompt, Story and cases before building. The person decides; record their actual chat approval with --said (RUNBOOK §2), never invent it.
- Do not run `pdd lint` before `pdd test`; test includes lint. Report only real checks and output.

## Files

- `RUNBOOK.md`: self-contained authoring fast path and router for optional `runbook/` edge-case files (`pdd test` and `pdd simulate`).
- `guide.md`: the Prompting guide.
- `story-guide.md`: how to write a Story that a test can check.
- `review.md`, `verification-setup.md`, `verification-recipe.md`, `autopilot-job-rules.md`: check/code/Autopilot references (skip during authoring).

## How to write

1. Name applicable `guide.md` rules and find the owning prompt by path.
2. Write or change the prompt. Then write the Story in the person's words, with no function calls or type names. A Story is one "I can…" behavior, checked in a minute.
3. Derive normal, limit and error cases (`<= 15` small steps; align `simulation_overrides` ports) and run `pdd lint --local`.
4. Show drafts and open choices.
5. After changing prompt, Story and tests, run `pdd test` as RUNBOOK.md says, and show the person the `Prompt tests` line(s) and the report link(s). Offer `pdd simulate STORY`. If a check fails, show it; never change the expected value yourself.

Without prompts, use code, callers and tests as evidence. Change no code until asked.

Workflow skills: pdd-small-change, pdd-bug, pdd-feature and pdd-product.
