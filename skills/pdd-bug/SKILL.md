---
name: pdd-bug
description: PDD bug workflow. Use when fixing PDD bugs, errors or wrong results. Reproduce, fix prompt and tests (PR 1), then code (PR 2) if asked.
metadata:
  pdd-skills: 0.1.10
---

# PDD bug

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Briefs: `steps/`. `?` = optional.
1. story: reproduce, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr (PR 1: prompt, Story, tests), then ask
3. code: build, verify, formal, review → gate: pr (PR 2)

## Rules

- The main chat coordinates and writes no code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Give the step file and paths at once, not chat history. Wait with one long time-out; avoid small follow-ups.
- At a gate, show the result, ask the person, and stop. Revise changes and ask again. Outside a run, open a PR only if the person says yes; in a run, pdd does. Never merge.
- Use full URLs (`https://…`).
- Before an optional step, ask the person and wait for the answer: "Do you want to try it now? yes/no". In a run, run `<pdd> workflow ask` first.
- At the story gate, start with one verdict line, then the details: "Verdict: the bug is in the PROMPT (its check fails on the issue's case).", "Verdict: the prompt is right; the bug is only in the CODE." or "Verdict: no prompt covers this yet; the bug can only be in the code." Give the full paths of the Story files. For an issue-only prompt, offer "adopt PDD for this module" later. You may offer: "You can also open it now with `pdd try <story>` before the check." End with: "Reply 'I approve' here or run `pdd workflow approve N`, or tell me what to change."
- Before PR 1, show the `Runtime check` line(s) with the report link(s) and the Try link, if any. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`."
- If verify or formal fails, or review finds must-fixes, go back to build in a new subagent, at most 2 times. These 2 repair rounds start after the initial review: fresh build, verify, formal, then fresh review. After that, open PR 2 with the actual `Review:` verdict and remaining must-fix list at the top, plus "✗ N vectors fail" if vectors still fail. No new human gate.
- A linked `.ui.svg` is the layout spec in reproduce, build and verify (RUNBOOK §13).
- A person decides expected values. Never change a test to make it pass. Put outside code (databases, files, network, clocks, randomness, programs) behind a runtime-faked port (pdd-prompting RUNBOOK §21).

## Try tools

If the person asks, use `try_open`, `try_state`, `try_run` with input, `try_check` and `try_save_case`. Runs spend the Try budget and show in page history. Review saved observations with the person; they are not approved expected values.

## In a run

- Steps write `<run folder>/STEP.md` notes and commit code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
