---
name: pdd-prompting
description: The PDD Prompting guide. Use when you write, change or review a module prompt (*.prompt.md), a Story or test cases, or when the person asks how to write prompts in PDD. In PDD, prompts are the source and code follows them.
metadata:
  pdd-skills: 0.1.11
---

# PDD prompting

Each code module's `.prompt.md` is the source; code implements it.

## Core rules

- Read `guide.md` in full before you write or change a prompt, Story or test cases. Read RUNBOOK.md §2–§4 before you write a prompt or a test file.
- Change the prompt first, then the code.
- One prompt per module: purpose and behavior. Give each rule one owner prompt. Link to a shared rule. Do not copy it. For a CLI, say if a rule belongs to the whole-CLI prompt or to one module's prompt.
- Keep caller behavior and important edges. Outside code (database, files, network, clock, randomness, programs): use an injected port that the PDD interpreter fakes, never direct calls. See [RUNBOOK §21](RUNBOOK.md#21-fake-the-outside-world).
- Linked `.ui.svg` is the layout spec: parts, words, order, ids and states. Prose and drawing must agree (RUNBOOK §13).
- Derive expectations from requirements before code; never copy code output.
- Show prompt, Story and cases before building. The person decides; never approve for them.
- Report only checks that you ran, with their real output.

## Files

- `guide.md`: the full Prompting guide.
- `review.md`: how to review drafts and report results.
- `RUNBOOK.md`: how to write prompts and tests that the PDD interpreter can check (§2–§10), and how to run `pdd test` and `pdd simulate`.

## How to write

1. Name applicable `guide.md` rules.
2. Find the owning prompt by path.
3. Write or change the prompt. Then write the Story in the person's words, with no function calls or type names. A Story is one "I can…" behavior, checked in a minute.
4. Derive normal, limit and error cases. Use one action or about 10 moves/rows/calls. Split long replays with expected state after each part; the server stops a step after 10 minutes.
5. Show drafts and open choices that affect results.
6. After changing prompt, Story and tests, run `pdd test` as RUNBOOK.md says, and show the person the `Runtime check` line(s) and the report link(s). Offer `pdd simulate STORY`. If a check fails, show it; never change the expected value yourself.

Without prompts, use code, callers and tests as evidence. Change no code until asked.

Workflow skills: pdd-small-change, pdd-bug and pdd-feature.
