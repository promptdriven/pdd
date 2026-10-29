---
name: pdd-feature
description: Use when the person asks for a new feature or new behavior in a PDD project.
metadata:
  pdd-skills: 0.1.9
---

# PDD feature

Briefs: `steps/`. `?` = optional.
1. story: understand, visual?, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr (PR 1: prompt, Story, tests), then ask
3. code: build, verify, formal → gate: pr (PR 2)

## Rules

- The main chat coordinates, without writing code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Give it its full brief at once: the step file and file paths, not the chat history. Then wait for it with one long time-out. Do not send small follow-up messages or use short waits.
- At a gate, show the result, ask the person, and stop. Ask before a PR outside a run; pdd opens it in a run. Never merge.
- Write each link as its full URL (`https://…`), never as a linked word.
- Before an optional step, ask the person and wait for the answer: "Do you want a visual design step? yes/no". In a run, run `<pdd> workflow ask` first. For a page or a screen, recommend visual: it makes the app map.
- At the story gate, give the full paths of the Story files and the plan, and show the plan list. The person can say "make it one Story", "split part 5" or "change Story 5: …". A change request names a Story: redo only that Story and its test file. For an issue-only prompt, offer "adopt PDD for this module" later. You may offer: "You can also open it now with `pdd try <story>` before the check." If visual made an app map, tell the person to run `pdd try <story> --new`. End with: "Reply 'I approve' here or run `pdd workflow approve N`, or tell me what to change."
- Before PR 1, show one `Runtime check` line per Story with its report link, and the Try links. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`."
- If verify or formal finds a failing case, go back to build in a new subagent, at most 2 times. If it still fails, PR 2 opens anyway with "✗ N vectors fail" on top.
- A person decides expected values. Never change a test to make it pass.

## Use the Try tools when they are available

On intent, the person's agent may use `try_open`, `try_state`, fill input in `try_run`, `try_check`, `try_save_case`. Runs spend the Try budget and appear in page history. Review saved observations with the person; never treat them as approved expected values.

## In a run

- Steps write `<run folder>/STEP.md` notes and commit code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
