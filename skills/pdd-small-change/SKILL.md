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
- Run each step in a new subagent, never reused, so verify never checks its own code. Give it its full brief at once: the step file and file paths, not the chat history. Then wait for it with one long time-out. Do not send small follow-up messages or use short waits.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again.
- Before an optional step, ask the person and wait for the answer. In a run, run `<pdd> workflow ask` first.
- A person decides expected values. Never change a test to make it pass.
- Never push, open a PR or merge.

## In a run (see the first message)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
