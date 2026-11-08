# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

It changes these rules of SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): read the owner notes. Follow [$pdd-merge](../../pdd-merge/SKILL.md) for scoped delegation and native approvals, overriding generic ask-and-stop rules. A fresh pdd-check checks the head; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Do the visual step only for a page or screen design. Skip try (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Story gate: put the checker's verdict line, the plan list and the full Story paths in the PR 1 body.
- Code PR: start it as soon as PR 1 is open, stacked on PR 1; do not wait for PR 1 to merge. In `auto`, do this in every repo. In `observe`, a repo with a release does it too; a new product waits for a person's "code now".
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11): ask one question only for a product call the issue does not settle; else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- No AI verdict, busy or not run (§11): ask no person; follow [$pdd-autopilot interpreter outage](../../pdd-autopilot/steps/handoff.md#interpreter-outage): `pdd workflow park --interpreter`; end the turn.
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Still in force: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

After failure, find the cause and change the repair. Two failed rounds alone do not block work. Keep repairing while a useful correction is available, preserving expectations and checks, for at most 5 repair rounds in one area (a round is a return to an earlier step that clears later steps; a retry of the same step is not one); pdd refuses a 6th. Then, or on a real blocker, record cause and next action and take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress; continue other work. Never repeat an uncertain external action.

A prompt that a test, command or prompt runs needs an interface block: draft it through pdd from the prompt text and save it; one that nothing runs needs none.

Screens: before/after screenshots in the code PR.

Work: `node scripts/affected-tests.mjs --base BASE --run --report REPORT`
uses the run base, run report and smoke or queued full fallback.
Report files, commands, counts and fallback causes in verify.md and the PR.
Follow pdd-check's suite gate and reuse.
