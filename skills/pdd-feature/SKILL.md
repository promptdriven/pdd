---
name: pdd-feature
description: PDD feature workflow. Use when the person asks for a new feature or new behavior in a PDD project. Write the prompt, Story and tests (PR 1), then the code (PR 2) if asked.
---

# PDD feature

Each area is one main chat. Step briefs are in `steps/`. `?` = optional.
1. story: understand, visual?, prompt-story → gate: approve
2. prompt-pr: check, try? → approve, then gate: pr (PR 1: prompt, Story, tests), then ask
3. code: build, verify, formal → gate: pr (PR 2)

## Rules

- The main chat coordinates and talks with the person. It does not write code.
- Run each step in a new subagent, never reused, so verify never checks its own code. Give it its full brief at once: the step file and file paths, not the chat history. Then wait for it with one long time-out. Do not send small follow-up messages or use short waits.
- At a gate, show the result, ask the person, and stop. For changes, revise here and ask again. An optional step is a question in the chat, not a stop. For a screen, recommend visual: it makes the app map.
- At the story gate, give the full paths of the Story files and the plan, and show the plan list. The person can say "make it one Story", "split part 5" or "change Story 5: …". A change request names a Story: redo only that Story and its test file. If a new prompt covers only this issue, say that a bigger "adopt PDD for this module" step can come later. You may offer: "You can also open it now with `pdd try <story>` before the check." If visual made an app map, tell the person to run `pdd try <story> --new`. End with: "Reply 'I approve' to go on, or tell me what to change."
- Before PR 1, show one `Runtime check` line per Story with its report link, and the Try links, if any. Ask the person to try it and approve, or ask for changes. pdd opens PR 1 only after the approval. Then show the PR 1 link and ask: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`." The code area starts only when the person asks.
- If verify or formal finds a failing case, go back to build in a new subagent, at most 2 times. If it still fails, PR 2 opens anyway with "✗ N vectors fail" on top (RUNBOOK §17). Say so at the gate.
- A person decides expected values. Never change a test to make it pass.
- Never push, open a PR or merge.

## In a run (see the first message)

- Each step writes notes to `<run folder>/STEP.md` and commits its code.
- When you need the person's answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.
- When the person approves in their own words, run `<pdd> workflow approve N`. Never approve for them.
