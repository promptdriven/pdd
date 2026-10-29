---
name: pdd-bug
description: PDD bug workflow. Use when fixing PDD bugs, errors or wrong results. Reproduce, fix prompt and tests (PR 1), then code (PR 2) if asked.
metadata:
  pdd-skills: 0.1.9
---

# PDD bug

Briefs: `steps/`. `?` = optional.
1. story: reproduce, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr (PR 1: prompt, Story, tests), then ask
3. code: build, verify, formal → gate: pr (PR 2)

## Rules

- The main chat coordinates, without writing code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Give it its full brief at once: the step file and file paths, not the chat history. Then wait for it with one long time-out. Do not send small follow-up messages or use short waits.
- At a gate, show the result, ask the person, and stop. Ask before a PR outside a run; pdd opens it in a run. Never merge.
- Write each link as its full URL (`https://…`), never as a linked word.
- Before an optional step, ask the person and wait for the answer: "Do you want to try it now? yes/no". In a run, run `<pdd> workflow ask` first.
- At the story gate, start with one verdict line, then the details: "Verdict: the bug is in the PROMPT (its check fails on the issue's case).", "Verdict: the prompt is right; the bug is only in the CODE." or "Verdict: no prompt covers this yet; the bug can only be in the code." Give the full paths of the Story files. For an issue-only prompt, offer "adopt PDD for this module" later. You may offer: "You can also open it now with `pdd try <story>` before the check." End with: "Reply 'I approve' here or run `pdd workflow approve N`, or tell me what to change."
- Before PR 1, show the `Runtime check` line(s) with the report link(s) and the Try link, if any. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`."
- If verify or formal finds a failing case, go back to build in a new subagent, at most 2 times. If it still fails, PR 2 opens anyway with "✗ N vectors fail" on top.
- A person decides expected values. Never change a test to make it pass.

## Use the Try tools when they are available

On intent, the person's agent may use `try_open`, `try_state`, fill input in `try_run`, `try_check`, `try_save_case`. Runs spend the Try budget and appear in page history. Review saved observations with the person; never treat them as approved expected values.

## In a run

- Steps write `<run folder>/STEP.md` notes and commit code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
