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
- Run each step in one fresh subagent. Never reuse it. Give it a short brief and file paths, not the chat history.
- verify runs in a fresh subagent that did not write the code.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again.
- An optional step is a question in the chat, not a stop.
- Never push, open a PR or merge.

## In a run (the first message says so)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- After each step, run `<pdd> workflow done STEP --summary "…"`. The first message gives `<pdd>`.
- Never approve for the person. The person approves in their own words or runs `pdd workflow approve`.
- `verify.md` holds the exact test commands and their real output. pdd puts it in the PR.
