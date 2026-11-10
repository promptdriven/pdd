# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

Overrides SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): read handoff/run notes; use scoped delegation in [$pdd-merge](../../pdd-merge/SKILL.md). A fresh pdd-check checks each PR at its head; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Visual only for a page/screen design. Skip try (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Story gate: put the checker's verdict line, the plan list and the full Story paths in the PR 1 body.
- Code PR: start it as soon as PR 1 is open, stacked on PR 1; do not wait for PR 1 to merge. In `auto`, do this in every repo. In `observe`, a repo with a release does it too; a new product waits for a person's "code now".
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- Story/value doubt (§11): ask only for an unsettled product call; else pick one and explain on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- No AI verdict, busy or not run (§11): ask no person; follow [$pdd-autopilot interpreter outage](../../pdd-autopilot/steps/handoff.md#interpreter-outage): `pdd workflow park --interpreter`; end the turn.
- Missing route: [record it](../../pdd-autopilot/steps/handoff.md#missing-pdd-route). Cases outside an interface widen the prompt and interface first (draft); ask a route question only when prose cannot express the behavior.
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Keep: unresolved product calls, irreversible actions, `--max-calls`, strict mode, and never sending a failed check again.

Fix the failed check's cause before retrying; two failed rounds do not block work. Keep repairing while a useful correction is available, preserving behavior expectations and required validation, for at most 5 repair rounds in one area (a round is a return to an earlier step that clears later steps; a retry of the same step is not one); pdd refuses a 6th. For a real blocker or at the limit, record cause and next action; take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress; the coordinator continues other eligible work. Never repeat an external action with an unknown outcome.

Executed prompts: draft through pdd. Show coverage; unmapped/conflicting sentences need one grouped person decision with quotes, never delegation. Unused prompts need none.

A screen change gets before/after screenshots in the code PR.

Full suites/builds follow the [shared queue rule](../../pdd-autopilot/steps/handoff.md).
