---
name: pdd-prompting
description: The PDD Prompting guide. Use when you write, change or review a module prompt (*.prompt.md), a Story or test cases, or when the person asks how to write prompts in PDD. In PDD, prompts are the source and code follows them.
---

# PDD prompting

In PDD, prompts are the source. Each code module has one `.prompt.md` file; the code implements it.

## Core rules

- Read `guide.md` in full before you write or change a prompt, Story or test cases. A link or a summary is not enough. Read RUNBOOK.md §2–§4 before you write a prompt or a test file.
- Change the prompt first, then the code.
- Write one prompt for each module: what it must do and why, not the code line by line.
- Give each rule one owner prompt. Link to a shared rule. Do not copy it. For a CLI, say if a rule belongs to the whole-CLI prompt or to one module's prompt.
- Keep the behavior callers need and the edge cases that matter.
- Write expected results from the requirement before the code exists. Never copy them from the code's output.
- Show the prompt, Story and cases to the person before you build. The person decides; never approve for them.
- Report only checks that you ran, with their real output.

## Files

- `guide.md`: the full Prompting guide.
- `review.md`: how to review drafts and report results.
- `RUNBOOK.md`: how to write prompts and tests that the runtime can check (§2–§10), and how to run `pdd check` and `pdd try`.

## How to write

1. Tell the person which rules of `guide.md` apply.
2. Find the prompt that owns the behavior. Use the repo's paths.
3. Write or change the prompt. Then write the Story in the person's words, with no function calls or type names. A Story is one behavior that a person can check in about a minute: one "I can…" sentence.
4. Write test cases for normal input, limits and errors, with expected results from the prompt and the Story.
5. Show the drafts and mark open questions. Ask only about choices that change the result.
6. After you write or change a prompt, its Story and its test file, run `pdd check` as RUNBOOK.md says, and show the person the `Runtime check:` line and the report link. Then offer `pdd try STORY` so they can use it by hand. If a check fails, show it; never change the expected value yourself.

For code with no prompts yet, use the code, callers and tests as evidence. Change no code until asked.

Workflow skills: pdd-small-change, pdd-bug and pdd-feature.
