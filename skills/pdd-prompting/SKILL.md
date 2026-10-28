---
name: pdd-prompting
description: The PDD Prompting guide. Use when you write, change or review a module prompt (*.prompt.md), a Story or test cases, or when the person asks how to write prompts in PDD. In PDD, prompts are the source and code follows them.
metadata:
  pdd-skills: 0.1.9
---

# PDD prompting

Each code module's `.prompt.md` is the source; code implements it.

## Core rules

- Read `guide.md` in full before you write or change a prompt, Story or test cases. Read RUNBOOK.md §2–§4 before you write a prompt or a test file.
- Change the prompt first, then the code.
- Give each rule one owner prompt. Describe behavior; link shared rules. For a CLI, say if a rule belongs to the whole-CLI prompt or to one module's prompt.
- Linked `.ui.svg` is the layout spec: parts, words, order, ids and states. Prose and drawing must agree (RUNBOOK §13).
- Write expected results from the requirement before the code exists. Never copy them from the code's output.
- Show the prompt, Story and cases to the person before you build. The person decides; never approve for them.
- Report only checks that you ran, with their real output.

## Files

- `guide.md`: the full Prompting guide.
- `review.md`: how to review drafts and report results.
- `RUNBOOK.md`: how to write prompts and tests that the runtime can check (§2–§10), and how to run `pdd check` and `pdd try`.

## How to write

1. Tell the person which rules of `guide.md` apply.
2. Find the owning prompt; use repo paths.
3. Write or change the prompt. Then write the Story in the person's words, with no function calls or type names. A Story is one behavior that a person can check in about a minute: one "I can…" sentence.
4. Write normal, limit and error cases from the prompt and Story. Keep steps small: one action or about 10 moves/rows/calls. Split long replays with expected state after each part; the server stops a step after 10 minutes.
5. Show the drafts and mark open questions. Ask only about choices that change the result.
6. After you write or change a prompt, its Story and its test file, run `pdd check` as RUNBOOK.md says, and show the person the `Runtime check` line(s) and the report link(s). Then offer `pdd try STORY` so they can use it by hand. If a check fails, show it; never change the expected value yourself.

Without prompts, use code, callers and tests as evidence. Change no code until asked.

Workflow skills: pdd-small-change, pdd-bug and pdd-feature.
