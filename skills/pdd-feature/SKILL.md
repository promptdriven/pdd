---
name: pdd-feature
description: Use when the person asks for a new feature or new behavior in a PDD project.
metadata:
  pdd-skills: 0.1.10
---

# PDD feature

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

`steps/` briefs; `?` = optional.
1. story: understand, visual?, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr, then ask
3. code: build, verify, formal, review → gate: pr

- Main chat: coordinate; no code or checks.
- Use fresh subagents; never reuse builders or let them check their code. Give step file and paths at once, not chat history; wait with one long time-out; no small follow-ups.
- Checks: fresh first. Only verify/formal may reuse after startup failure; agent wrote no code, tests or prompts in this run.
- Review: always fresh; no build, verify, formal, prior reviews or their context. Blocked: RUNBOOK §17.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- At gates show results, ask the person, stop; revise and ask again. Outside runs PRs need the person's yes; in runs pdd opens them. Never merge.
- Use full URLs (`https://…`).
- Before an optional step, ask the person and wait for the answer: "Do you want a visual design step? yes/no". In a run, run `<pdd> workflow ask` first. For a page or a screen, recommend visual: it makes the app map.
- At the story gate, give the full paths of the Story files and the plan, and show the plan list. They can say "make it one Story", "split part 5" or "change Story 5: …". A change request names a Story: redo only that Story and its test file. For issue-only prompts, offer "adopt PDD for this module" later. You may offer: "You can also open it now with `pdd try <story>` before the check." If visual made an app map, tell the person to run `pdd try <story> --new`. End with: "Reply 'I approve' here or run `pdd workflow approve N`, or tell me what to change."
- Before PR 1, show one `Runtime check` line per Story with its report link, and the Try links. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`."
- On verify/formal failure or review must-fixes, go back to build in a new subagent, at most 2 times. 2 repair rounds after initial review: fresh build, verify, formal, then fresh review. PR 2 starts with real `Review:` verdict, remaining must-fixes and "✗ N vectors fail" for failing vectors. No new human gate.
  - Repair pending: with must-fixes and fewer than 2 repairs, do not run `workflow done review`; start a fresh build with the must-fix list.
  - Final review: clear or 2 repairs used; run `workflow done review` to open PR 2.
- A person decides expected values. Never change a test to make it pass. Outside code (databases, files, network, clocks, randomness, programs): runtime-faked ports; no direct calls (pdd-prompting RUNBOOK §21).

## Try tools

If asked: `try_open`, `try_state`, `try_run` with input, `try_check`, `try_save_case`. Runs use Try budget and show in Try page history. Review saved cases with the person, never as approved expected values.

## In a run

- Steps write `<run folder>/STEP.md` and commit code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- On their own approval, run `<pdd> workflow approve N`. Never approve for them.
