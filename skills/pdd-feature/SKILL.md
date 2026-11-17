---
name: pdd-feature
description: Use when the person asks for a new feature or new behavior in a PDD project.
metadata:
  pdd-skills: 0.1.34
---

# PDD feature

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

1. story: steps/understand.md, steps/visual.md (optional), steps/prompt-story.md → gate: approve
2. prompt-pr: steps/check.md, steps/try.md (optional) → approve, then gate: pr, then ask
3. code: steps/build.md, steps/verify.md, steps/formal.md, steps/review.md → gate: pr

- Single coupled slice (1–2 prompts, CLI/Autopilot): read `pdd-prompting/RUNBOOK.md`, author Story, prompt, test, `.ui.svg` and `app-map.json` in 1 session (0 authoring subagents), and run `pdd files` + `pdd lint --local`.
- On 3+ independent prompts/modules, main chat coordinates; no code or checks: lock shared contracts (`app-map.json`/interfaces) first, then parallelize.
- Fresh subagents in step order for verify, review and 3+ builds; never reuse builders or let them check code. Step file/paths at once, no chat history; wait one long time-out, no small follow-ups (§11).
- Checks: fresh first. Only verify/formal may reuse after startup failure; no code, tests or prompts this run.
- Review: always fresh; no build/verify/formal/prior reviews or context. Blocked: RUNBOOK §17.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- Ask at gates. Normal runs open PR 1 on check pass; strict keeps gates. Outside runs, ask before PRs; merge on request (§2).
- Use full URLs.
- Before an optional step, ask the person and wait for the answer: "Do you want a visual design step? yes/no". In a run, run `<pdd> workflow ask` first. For a page or a screen, recommend visual: it makes the app map.
- At the story gate, give the full paths of the Story files and the plan, and show the plan list. They can say "make it one Story", "split part 5" or "change Story 5: …". A change request names a Story: redo only that Story and its test file. Issue-only prompts: offer "adopt PDD for this module" later. You may offer `pdd simulate <story>` before the check. If visual made an app map, tell the person to run `pdd simulate <story> --new`. Ask for approval or changes in their own words. In runs, show pdd's Story card verbatim (batch: card, then answer).
- Strict: Before PR 1, show one `Prompt tests` line per Story with its report link, and the Simulator links. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first?"
- On verify/formal failure or review must-fixes, allow 2 repairs after initial review. Use fresh build, verify, formal and review agents. PR 2: `Review:` verdict, must-fixes, "✗ N vectors fail". No extra gate.
  - Repair pending: with must-fixes and fewer than 2 repairs, do not run `workflow done review`; fresh build with the must-fix list.
  - Final review: clear or 2 repairs used; run `workflow done review` to open PR 2.
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
