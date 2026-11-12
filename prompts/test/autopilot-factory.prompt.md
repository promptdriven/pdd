# Autopilot factory test

This contract owns the offline factory harness, its entry test and its shell runner.
It does not change production Autopilot policy. Keep candidate failures visible with
a named gap; never skip, todo, catch-and-pass, or change an expected outcome to fit
the candidate.

Run the native CLI dispatch, workflow runner and durable stores against a disposable
project. Use real Git commits, branches, worktrees and a local bare origin. Fake
external services, agent reasoning and machine resource observations through the
existing `machineGuard` port; no test reads the host's live memory or capacity.
GitHub must retain mutations and reject unsupported service operations. The interpreter must support verdict, no
verdict, refusal and delayed completion. Scripted workers read the actual bundled
workflow and step briefs and use public done, gate, open, resend and evidence
commands. They must not write native approval fields or invent a runtime receipt.

For check planning, exercise a full native CLI batch with a target Story and an
unrelated baseline obligation. Assert a saved plan before dispatch, separate
target/baseline result groups, and the same classification on a saved read. A
missing interface must block paid dispatch with one named prerequisite. Retain
the ordinary workflow gates; this scenario needs no synthetic approval action.
For missing interfaces, missing entry limits, missing nested call bounds and
recursion, exercise saved reads and the supported retry command. Keep the named
local repair cause and batch history, with no paid dispatch. After the owner
repairs the named declaration, a fresh check must reach a verdict.

## Core factory

`test/autopilot-factory-core.e2e.test.mjs` runs each user path of Autopilot end to end through the real launcher
(`runAutopilotLauncher` start, status, add and stop, and `tickAutopilot`) and the real core tick, with a real bare
origin and clones, the shared fake GitHub of the core world and scripted agent jobs. Only GitHub and agent reasoning
are fake. The tick calls no Herdr, launchctl or systemctl. Cases:

1. Start with the opt-in label in pdd.json: the first tick claims only the labeled issue, the build opens one PR, the
   review and the full suite run at its head, and the tick merges it once; the issue closes; status shows the merge.
2. A start with no label asks for one and saves nothing; `pdd autopilot add N` labels one issue; a start with `--label`
   takes only that issue.
3. A red full suite gets one repair on the same branch; the new head is reviewed and merged.
4. With `maxRepairs` 1, a review FAIL after the repair ends the job: one END comment, `pdd:stuck`, no merge.
5. A build that needs a person posts one question and adds `pdd:needs-decision`; a trusted answer and the label removal
   start the next build with the question and the answer; it merges.
6. A base change that conflicts with the PR starts a conflict update (not a repair); after it the PR merges.
7. A person who removes `pdd:working` stops that job; `pdd autopilot stop` stops the timer, and a later tick starts
   nothing; status says disabled.
8. Two independent repository checkouts share one state folder and compete at the same time for one machine slot.
   Only one build starts; the second tick reads the first job while holding the machine admission lock and starts no
   build. Fix the machine guard result to one slot so the case does not depend on host memory.

## Dependencies

- [Launcher](../cli/autopilot-launcher.prompt.md) and [core engine](../cli/autopilot-core.prompt.md): the core factory.

- [Workflow runner](../cli/workflow-runner.prompt.md): workflow and gates.
