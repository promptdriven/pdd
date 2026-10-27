---
name: pdd-small-change
description: PDD small-change workflow. Use when the person asks for a small, contained change that is easy to undo, such as a typo, a config value or a small fix. Plan it, make it, verify it, one PR.
---

# PDD small change

Use this for a small change with a clear effect that is easy to undo. If the impact grows, suggest pdd-bug or pdd-feature.

Each area is one main chat. Step briefs are in `steps/`.
1. plan: scope → gate: approve
2. build: change, verify, formal → gate: pr

## Rules

- The main chat coordinates and talks with the person. It does not write code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Brief it with file paths, not the chat history.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again.
- An optional step is a question in the chat, not a stop.
- A person decides expected values. Never change a test to make it pass.
- Never push, open a PR or merge.

## In a run (see the first message)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- After each step, run `<pdd> workflow done STEP --summary "…"` (or `"skipped"`).
- Never approve for the person. When the person approves in their own words, run `<pdd> workflow approve N`.
- `verify.md` holds the exact test commands and real output. pdd adds it to the PR.
