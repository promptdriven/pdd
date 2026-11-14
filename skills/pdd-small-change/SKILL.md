---
name: pdd-small-change
description: PDD small-change workflow. Use when the change stays outside PDD (docs, guides, packages, config, CI, lockfiles or test maintenance — never prompts, Stories or product code), also when written as a bug. Plan it, make it, verify it, one PR.
metadata:
  pdd-skills: 0.1.31
---

# PDD small change

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Use this strictly for changes outside PDD: docs, guides, `package.json`, lockfiles, config, CI, metadata and test maintenance — never `*.prompt.md`, `user_stories/*.md`, owned files or product code (`src/`, `app/`, etc.). Product or prompt-owned code always uses pdd-bug or pdd-feature, even for a small fix or with no prompt yet (create the prompt in PR 1, never bypass PDD).

Each area is one main chat; read its step files.
1. plan: steps/scope.md → gate: approve
2. build: steps/change.md, steps/verify.md, steps/formal.md → gate: pr

## Rules

- The main chat coordinates and talks with the person; no code or checks.
- Fresh subagents in step order once input files exist; never reuse builders or let them check code. Step file/paths at once; no chat history. Every brief requires "the run's main chat" for the chat in briefs/notes; keep actual actors and root paths. Wait once: long time-out; no small follow-ups. Read §11 once; RUNBOOK "Bounded handoffs".
- Checks: fresh first. Only verify/formal may reuse after startup failure; wrote no code, tests or prompts this run.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- At gates, show results, ask and stop. Revise changes and ask again. Outside runs, ask before opening PRs. In runs, pdd opens them. Only the main chat may merge on explicit person request under RUNBOOK §2.
- Use full URLs.
- Before an optional step, ask the person and wait for the answer. In a run, run `<pdd> workflow ask` first.
- A person decides expected values. Never change a test to make it pass.

## In a run

- Write `<run folder>/STEP.md`; commit changes.
- For an answer mid-step, run `<pdd> workflow ask "<question>"`. Ask in plain chat, never request_user_input, and end your turn. The person replies in chat or with `<pdd> workflow changes N "answer"`.
- Show the gate; judge the later chat reply without exact phrases. Never approve questions or changes. Record gate approval:

```sh
<pdd> workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Quote a delimiter absent as a line. Stdin keeps newlines; blank fails. RUNBOOK §2.
