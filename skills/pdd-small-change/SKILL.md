---
name: pdd-small-change
description: PDD small-change workflow. Use when the person asks for a small, contained change that is easy to undo, such as a typo, a config value or a small fix. Plan it, make it, verify it, one PR.
metadata:
  pdd-skills: 0.1.11
---

# PDD small change

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Use this for a small change with a clear effect that is easy to undo. If the impact grows, suggest pdd-bug or pdd-feature.

Each area is one main chat. Step briefs are in `steps/`.
1. plan: scope → gate: approve
2. build: change, verify, formal → gate: pr

## Rules

- The main chat coordinates and talks with the person; no code or checks.
- Use fresh subagents; never reuse builders or let them check their code. Give step file and paths at once, not chat history; wait with one long time-out; no small follow-ups.
- Checks: fresh first. Only verify/formal may reuse after startup failure; agent wrote no code, tests or prompts in this run.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again. Outside a run, open a PR only if the person says yes; in a run, pdd does. Never merge.
- Write each link as its full URL (`https://…`), never as a linked word.
- Before an optional step, ask the person and wait for the answer. In a run, run `<pdd> workflow ask` first.
- A person decides expected values. Never change a test to make it pass.

## In a run

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
