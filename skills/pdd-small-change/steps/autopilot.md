# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

It changes these rules of SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): read the owner notes. Follow [$pdd-merge](../../pdd-merge/SKILL.md) for scoped delegation and native approvals, overriding generic ask-and-stop rules. A fresh pdd-check checks the head; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Skip them (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Plan gate: put the scope and the checker's verdict line in the PR body.
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11): ask one question only for a product call that the issue does not settle. Else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- No verdict from the AI service, busy or not run (§11): ask no person. Follow [$pdd-autopilot interpreter outage](../../pdd-autopilot/steps/handoff.md#interpreter-outage): `pdd workflow park --interpreter`; end the turn.
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Still in force: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

After failure, find the cause and change the repair. Two failed rounds alone do not block work. Keep repairing while a useful correction is available, preserving expectations and checks, for at most 5 repair rounds in one area (a round is a return to an earlier step that clears later steps; a retry of the same step is not one); pdd refuses a 6th. Then, or on a real blocker, record cause and next action and take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress; continue other work. Never repeat an uncertain external action.

Something runs a prompt (a test, a command or another prompt) that has no interface block: draft the block from the prompt text through pdd and save it. A prompt that nothing runs needs none.

Native work: `node scripts/affected-tests.mjs --base BASE --run --report REPORT`
uses the run base and an external report. Use its smoke set or queued full fallback.
Report files, commands, counts and fallback causes in verify.md and the PR.
Follow pdd-check's suite gate and reuse.
