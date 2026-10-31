---
name: pdd-small-change
description: PDD small-change workflow. Use when the person asks for a small, contained change that is easy to undo, such as a typo, a config value or a small fix. Plan it, make it, verify it, one PR.
metadata:
  pdd-skills: 0.1.12
---

# PDD small change

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Use this for a small change with a clear effect that is easy to undo. If the impact grows, suggest pdd-bug or pdd-feature.

Each area is one main chat. Step briefs are in `steps/`.
1. plan: scope → gate: approve
2. build: change, verify, formal → gate: pr

## Rules

- The main chat coordinates and talks with the person; no code or checks.
- Use fresh subagents; never reuse builders or let them check their code. Give the step file and paths at once, not chat history. Wait once with a long time-out; no small follow-ups.
- Checks: fresh first. Only verify/formal may reuse after startup failure; wrote no code, tests or prompts this run.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- At gates, show results, ask and stop. Revise changes and ask again. Outside runs, ask before opening PRs. In runs, pdd opens them. Only the main chat may merge on explicit person request under RUNBOOK §2.
- Use full URLs, never as a linked word.
- Before an optional step, ask the person and wait for the answer. In a run, run `<pdd> workflow ask` first.
- A person decides expected values. Never change a test to make it pass.

## In a run

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- For an answer mid-step, run `<pdd> workflow ask "<question>"`. Ask in plain chat, never request_user_input, and end your turn. The person replies in chat or with `<pdd> workflow changes N "answer"`.
- Show the gate; judge the later chat reply without exact phrases. Never approve questions or changes. Show changed prompts again. Record gate and draft approval:

```sh
<pdd> workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Quote a delimiter absent as a whole line in the words. Stdin keeps newlines. Blank input fails; no word grading. RUNBOOK §2.
