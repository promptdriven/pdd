---
name: pdd-small-change
description: PDD small-change workflow. Use when the person asks for a small, contained change that is easy to undo, such as a typo, a config value or a small fix. Plan it, make it, verify it, one PR.
metadata:
  pdd-skills: 0.1.12
---

# PDD small change

Fix the defect and add a test/check that catches it. Fix the defect first; if its cause is unclear, first add a failing reproducer, precise error or logging to expose it, then fix it. A diagnostic-only PR must say 'Not fixed yet: this helps find the cause' and leave the issue open.

Use this for a small change with a clear effect that is easy to undo. If the impact grows, suggest pdd-bug or pdd-feature.

Each area is one main chat. Step briefs are in `steps/`.
1. plan: scope → gate: approve
2. build: change, verify, formal → gate: pr

## Rules

- The main chat coordinates and talks with the person; no code or checks.
- Use fresh subagents; never reuse builders or let them check their code. Give step file and paths, not chat history. Wait once; no small follow-ups. Run `pdd test`/`--read BATCH` with the shell's longest timeout (Codex: long `timeout_ms`) or exit-notifying background task (Claude Code: `run_in_background`). If stopped, resume once with the saved `--read` command; never poll every minute.
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
