---
name: pdd-small-change
description: PDD small-change workflow. Use when the person asks for a small, contained change that is easy to undo, or for any fix that changes no product behavior (docs, config, CI, package data or tests), also when the issue is written as a bug. Plan it, make it, verify it, one PR.
metadata:
  pdd-skills: 0.1.32
---

# PDD small change

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Use this for a small change that is easy to undo, and for every fix that touches only non-code files (docs, config, CI, metadata or tests) with no product behavior change, even when worded as a bug. If behavior impact grows, suggest pdd-bug or pdd-feature.

Each area is one main chat. Read the step files that its line names.
1. plan: steps/scope.md → gate: approve
2. build: steps/change.md, steps/verify.md, steps/formal.md → gate: pr

## Rules

- The main chat coordinates and talks with the person; no code or checks.
- Fresh subagents in step order once input files exist; never reuse builders or let them check code. Step file/paths at once; no chat history. Every brief requires "the run's main chat" for the chat in briefs/notes; keep actual actors and root paths. Wait once: long time-out; no small follow-ups. Read §11 once; RUNBOOK "Bounded handoffs".
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
