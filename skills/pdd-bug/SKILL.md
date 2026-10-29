---
name: pdd-bug
description: PDD bug workflow. Use when the person reports a bug, an error or a wrong result in a PDD project. Reproduce it, fix the prompt and tests (PR 1), then the code (PR 2) if asked.
metadata:
  pdd-skills: 0.1.9
---

# PDD bug

One chat per area. Briefs: `steps/`. `?` = optional.
1. story: reproduce, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr (PR 1: prompt, Story, tests), then ask
3. code: build, verify, formal → gate: pr (PR 2)

## Rules

- The main chat coordinates; it writes no code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Give the step file and paths at once, not chat history. Wait with one long time-out; avoid small follow-ups.
- At a gate, show the result, ask the person, and stop. Revise changes and ask again. Outside a run, open a PR only if the person says yes; in a run, pdd does. Never merge.
- Use full URLs (`https://…`).
- Before an optional step, ask the person and wait for the answer: "Do you want to try it now? yes/no". In a run, run `<pdd> workflow ask` first.
- At the story gate, start with one verdict line, then the details: "Verdict: the bug is in the PROMPT (its check fails on the issue's case).", "Verdict: the prompt is right; the bug is only in the CODE." or "Verdict: no prompt covers this yet; the bug can only be in the code." Give the full paths of the Story files. If a new prompt covers only this issue, say that a bigger "adopt PDD for this module" step can come later. You may offer: "You can also open it now with `pdd try <story>` before the check." End with: "Reply 'I approve' here or run `pdd workflow approve N`, or tell me what to change."
- Before PR 1, show the `Runtime check` line(s) with the report link(s) and the Try link, if any. Ask the person to try it and approve, or ask for changes. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`." The code area starts only when the person asks.
- If verify or formal finds a failing case, go back to build in a new subagent, at most 2 times. If it still fails, PR 2 opens anyway with "✗ N vectors fail" on top.
- A person decides expected values. Never change a test to make it pass. Outside code (databases, files, network, clocks, randomness, programs): use a runtime-faked port, never a direct call. See pdd-prompting RUNBOOK §21.

## In a run

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
