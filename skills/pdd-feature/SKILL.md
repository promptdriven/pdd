---
name: pdd-feature
description: Use when the person asks for a new feature or new behavior in a PDD project.
metadata:
  pdd-skills: 0.1.12
---

# PDD feature

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

Step briefs are in `steps/`. `?` means optional.
1. story: understand, visual?, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr, then ask
3. code: build, verify, formal, review → gate: pr

- Main chat: coordinate; no code or checks.
- Use fresh subagents; never reuse builders or let them check their code. Give the step file and paths at once, not chat history. Wait once with a long time-out; no small follow-ups.
- Checks: fresh first. Only verify/formal may reuse after startup failure; wrote no code, tests or prompts this run.
- Review: always fresh; no build, verify, formal, prior reviews or their context. Blocked: RUNBOOK §17.
- Read pdd-prompting RUNBOOK §17 before checks: cleanup, unrun checks, recovery and result replacement.
- At gates, show results, ask and stop. Revise and ask again. Outside runs, ask before PRs. In runs, pdd opens them. Main chat merges only on person request under RUNBOOK §2.
- Use full URLs.
- Before an optional step, ask the person and wait for the answer: "Do you want a visual design step? yes/no". In a run, run `<pdd> workflow ask` first. For a page or a screen, recommend visual: it makes the app map.
- At the story gate, give the full paths of the Story files and the plan, and show the plan list. They can say "make it one Story", "split part 5" or "change Story 5: …". A change request names a Story: redo only that Story and its test file. For issue-only prompts, offer "adopt PDD for this module" later. You may offer `pdd simulate <story>` before the check. If visual made an app map, tell the person to run `pdd simulate <story> --new`. Ask for approval or changes in their own words.
- Before PR 1, show one `Runtime check` line per Story with its report link, and the Simulator links. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first?"
- On verify/formal failure or review must-fixes, allow 2 repairs after initial review. Use fresh build, verify, formal and review agents. PR 2 starts with real `Review:` verdict, remaining must-fixes and "✗ N vectors fail" for failing vectors. No new human gate.
  - Repair pending: with must-fixes and fewer than 2 repairs, do not run `workflow done review`; start a fresh build with the must-fix list.
  - Final review: clear or 2 repairs used; run `workflow done review` to open PR 2.
- A person decides expected values. Never change a test to make it pass. Inject ports for databases, files, network, clocks, randomness and programs. No direct calls (RUNBOOK §21).

## Try tools

`try_open`, `try_state`, `try_run`, `try_check`, `try_save_case` if asked. AI calls; Simulator history. Person reviews expected values.

## In a run

- Steps write `<run folder>/STEP.md` and commit code.
- For an answer mid-step, run `<pdd> workflow ask "<question>"`. Ask in plain chat, never request_user_input, and end your turn. The person replies in chat or with `pdd workflow changes N "answer"`.
- Show the gate. Judge the later reply in any chat. No exact phrase is needed. Never approve questions or changes. Show changed prompts again. Record approval for gate and drafts:

```sh
pdd workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Choose a delimiter absent as a whole line in the words. Keep it quoted. Stdin keeps newlines. Blank input fails. No word grading. RUNBOOK §2.
