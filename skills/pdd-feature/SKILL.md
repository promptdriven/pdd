---
name: pdd-feature
description: PDD feature workflow. Agree on a solution, write the prompt, Story and test cases, then build.
---

# PDD feature

Use this for new behavior.

Each area is one main chat. Step briefs are in `steps/`. `?` = optional.
1. solution: understand, visual? → gate: approve
2. story: prompt-story, check, try? → gate: approve
3. build: build, verify → gate: pr

## Rules

- The main chat coordinates and talks with the person. It does not write code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Brief it with file paths, not the chat history.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again.
- An optional step is a question in the chat, not a stop.
- Never push, open a PR or merge.

## In a run (see the first message)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- After each step, run `<pdd> workflow done STEP --summary "…"` (or `"skipped"`).
- Never approve for the person. When the person approves in their own words, run `<pdd> workflow approve N`.
- `verify.md` holds the exact test commands and real output. pdd adds it to the PR.
