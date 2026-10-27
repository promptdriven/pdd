---
name: pdd-feature
description: PDD feature workflow. Use when the person asks for a new feature or new behavior in a PDD project. Agree on a solution, write the prompt, Story and tests (PR 1), then the code (PR 2) if asked.
---

# PDD feature

Use this for new behavior.

Each area is one main chat. Step briefs are in `steps/`. `?` = optional.
1. story: understand, visual?, prompt-story → gate: approve
2. prompt-pr: check, try? → gate: pr (PR 1: prompt, Story, tests), then ask
3. code: build, verify → gate: pr (PR 2)

## Rules

- The main chat coordinates and talks with the person. It does not write code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Brief it with file paths, not the chat history.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again.
- At the PR 1 gate, show the PR 1 link, the `Runtime check:` line and the Try link (when there are any). Ask: "Do you want the code PR now, or stop here and merge PR 1 first?" Then stop. The code area starts only when the person asks.
- An optional step is a question in the chat, not a stop.
- A person decides expected values. Never change a test to make it pass.
- Never push, open a PR or merge.

## In a run (see the first message)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- After each step, run `<pdd> workflow done STEP --summary "…"` (or `"skipped"`).
- Never approve for the person. When the person approves in their own words, run `<pdd> workflow approve N`.
- `verify.md` holds the exact test commands and real output. pdd adds it to the PR.
