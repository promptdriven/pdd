---
name: pdd-small-change
description: PDD small-change workflow. Plan a small change that is easy to undo, make it, then verify it.
---

# PDD small change

Use this for a small change with a clear effect that is easy to undo. If the impact grows, suggest pdd-bug or pdd-feature.

Each area is one main chat. Step briefs are in `steps/`.
1. plan: scope → gate: approve
2. build: change, verify → gate: pr

## Rules

- The main chat coordinates and talks with the person. It does not write code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Give it a short brief and file paths, not the chat history.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again.
- An optional step is a question in the chat, not a stop.
- Never push, open a PR or merge.

## In a run (the first message says so)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- After each step, run `<pdd> workflow done STEP --summary "…"`.
- Never approve for the person. The person approves in their own words or runs `pdd workflow approve`.
- `verify.md` holds the exact test commands and real output. pdd adds it to the PR.
