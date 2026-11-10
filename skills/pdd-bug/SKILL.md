---
name: pdd-bug
description: Use when fixing PDD bugs, errors or wrong results. Reproduce, prompt/tests PR 1, code PR 2 if asked.
metadata:
  pdd-skills: 0.1.27
---

# PDD bug

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Briefs: `steps/` (`?` optional).
1. story: reproduce, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr, then ask
3. code: build, verify, formal, review → gate: pr

- If Autopilot is `observe` or `auto`, read `steps/autopilot.md` first. Assign an issue to keep it for a person; unassign it to give it to Autopilot.
- Main chat coordinates; no code or checks.
- Fresh subagents; never reuse builders or let them check code. Step file/paths at once; no chat history. Wait one long time-out; no small follow-ups. Read §11 once; pdd-prompting RUNBOOK "Bounded handoffs".
- Checks: fresh first. Only verify/formal may reuse after startup failure; wrote no code, tests or prompts this run.
- Review: always fresh; no build, verify, formal, prior reviews or their context. Blocked: RUNBOOK §17.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- Ask at person gates only. Normal runs: show the Story card as printed; a full check pass opens PR 1. Strict mode keeps its gates. Outside runs, ask before PRs. Merge only on request (RUNBOOK §2).
- Use full URLs.
- Normal runs skip try; the person can ask for it at the card. Else follow the optional-step gate or Autopilot overlay.
- At the story gate, start with one verdict line, then the details: "Verdict: the bug is in the PROMPT (its check fails on the issue's case).", "Verdict: the prompt is right; the bug is only in the CODE." or "Verdict: no prompt covers this yet; the bug can only be in the code." Give the full paths of the Story files. For issue-only prompts, offer "adopt PDD for this module" later. You may offer `pdd simulate <story>` before the check. Ask for approval or changes in their own words. In a run, show pdd's Story card as printed, not a bare "approve?". Batch: card, then answer.
- Strict: Before PR 1, show the `Prompt tests` line(s) with the report link(s) and the Simulator link, if any. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first?"
- On verify/formal failure or review must-fixes, allow 2 repairs after initial review. Use fresh build, verify, formal and review agents. PR 2 starts with real `Review:` verdict, remaining must-fixes and "✗ N vectors fail" for failing vectors. No new human gate.
  - Repair pending: with must-fixes and fewer than 2 repairs, do not run `workflow done review`; fresh build with the must-fix list.
  - Final review: clear or 2 repairs used; run `workflow done review` to open PR 2.
- `.ui.svg`: layout in reproduce, build, verify (RUNBOOK §13).
- A person decides expected values. Never change a test to make it pass. Inject ports for databases, files, network, clocks, randomness and programs. No direct calls (RUNBOOK §21).

## In a run

- Steps: write `<run folder>/STEP.md`; commit code.
- For an answer mid-step, run `<pdd> workflow ask "<question>"`. Ask in plain chat, never request_user_input, and end your turn. The person replies in chat or with `<pdd> workflow changes N "answer"`.
- Judge the later reply without exact phrases. Never approve questions or changes. Strict mode: show changed prompts again. Record gate and draft approval:

```sh
<pdd> workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Quote a delimiter absent as a line. Blank fails. §2.
