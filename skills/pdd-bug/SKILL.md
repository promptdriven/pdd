---
name: pdd-bug
description: Use when fixing PDD behavior bugs (non-behavior fixes use pdd-small-change). Reproduce, prompt/tests PR 1, code PR 2 if asked.
metadata:
  pdd-skills: 0.1.39
---

# PDD bug

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

1. story: steps/reproduce.md, steps/prompt-story.md → gate: approve
2. prompt-pr: steps/check.md, steps/try.md (optional) → approve, then gate: pr, then ask
3. code: steps/build.md, steps/verify.md, steps/formal.md, steps/review.md → gate: pr

- Single coupled slice: read `pdd-prompting/RUNBOOK.md`, author Story, prompt and test (plus `.ui.svg` when visual) in 1 session (0 authoring subagents), and run `pdd files` + `pdd lint --local`.
- Independent decoupled modules, main chat coordinates; no code or checks: lock shared contracts first, then parallelize.
- Fresh subagents in step order for verify, review and decoupled builds; never reuse builders or let them check code. Step file/paths at once, no chat history; wait one long time-out, no small follow-ups (§11).
- Checks: fresh first. Only verify/formal may reuse after startup failure; no code, tests or prompts this run.
- Review: always fresh; no build/verify/formal/prior reviews or context. Blocked: RUNBOOK §17.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- Ask at gates. Normal runs show the Story card verbatim and open PR 1 on full check pass; strict keeps gates. Outside runs, ask before PRs; merge on request (§2).
- Use full URLs.
- Normal runs skip try unless asked at the card; else follow the optional-step gate.
- At the story gate, start with one verdict line, then the details: "Verdict: the bug is in the PROMPT (its check fails on the issue's case).", "Verdict: the prompt is right; the bug is only in the CODE." or "Verdict: no prompt covers this yet; the bug can only be in the code." Give the full paths of the Story files. For issue-only prompts, offer "adopt PDD for this module" later. You may offer `pdd simulate <story>` before the check. Opens shell/page/Form (no Story: project). Ask for approval or changes in their own words. In runs, show pdd's Story card verbatim (batch: card, then answer).
- Strict: Before PR 1, show the `Prompt tests` line(s) with the report link(s) and the Simulator link, if any. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first?"
- On verify/formal failure or review must-fixes, allow 2 repairs after initial review. Use fresh build, verify, formal and review agents. PR 2 starts with `Review:` verdict, left must-fixes and "✗ N vectors fail". No new human gate.
  - Repair pending: with must-fixes and fewer than 2 repairs, do not run `workflow done review`; fresh build with the must-fix list.
  - Final review: clear or 2 repairs used; run `workflow done review` to open PR 2.
- `.ui.svg`: layout in reproduce, build, verify (RUNBOOK §13).
- A person decides expected values. Never change a test to make it pass. Inject ports for DB, files, net, clocks, RNG, programs; no direct calls (§21).

## In a run

- Write `<run folder>/STEP.md`; commit code.
- For an answer mid-step, run `<pdd> workflow ask "<question>"`. Ask in plain chat, never request_user_input, and end your turn. The person replies in chat or with `<pdd> workflow changes N "answer"`.
- Judge replies by intent; never approve questions/changes. Strict: re-show changed prompts. Record approval:

```sh
<pdd> workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Quote unused delimiter; blank fails (§2).
