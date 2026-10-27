---
name: pdd-prompting
description: The PDD Prompting guide. Use when you write, change or review a module prompt (*.prompt.md), a Story or test cases, or when the person asks how to write prompts in PDD. In PDD, prompts are the source and code follows them.
---

# PDD prompting

In PDD, prompts are the source. Each code module has one `.prompt.md` file. The code is one implementation of that prompt.

## Core rules

- Read `guide.md` in full before you write or change a prompt, Story or test cases. A link or a summary is not enough.
- Change the prompt first. Then change the code.
- Write one prompt for each module. Say what the module must do and why. Do not describe the code line by line.
- Give each rule one home. Link to a shared rule. Do not copy it.
- Keep the behavior that callers need and the edge cases that matter.
- Write expected results from the requirement before the code exists. Never copy them from the code's output.
- Show the prompt, Story and cases to the person before you build. The person decides. Never approve for the person.
- Report only the checks that you ran, with their real output.

## Files

- `guide.md`: the full Prompting guide. It owns the rules for prompts.
- `review.md`: how to review a prompt, a Story and test cases, and how to report results.
- `RUNBOOK.md`: how to run a runtime check with `pdd check` and `pdd try`.

## How to write

1. Read `guide.md` in full. Tell the person which of its rules apply to this change.
2. Find the prompt that owns the behavior. Use the paths that the repo already has.
3. Write or change the prompt. Then write the Story: the useful result and the criteria that a person can see.
4. Write test cases for normal input, limits and errors. Take each expected result from the prompt and the Story.
5. Show the drafts. Mark open questions. Ask only about a choice that changes the result.
6. After you write or change a prompt, its Story and its test file, run `pdd check` as RUNBOOK.md says, and show the person the `Runtime check:` line and the report link. Then offer `pdd try STORY` so they can use it by hand. If a check fails, show it; never change the expected value yourself.

For existing code without prompts, read the code, callers and tests as evidence. Keep the code as it is until the person asks for a change.

The PDD workflows are the skills pdd-small-change, pdd-bug and pdd-feature.
