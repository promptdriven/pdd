# Autopilot factory test

This contract owns the offline factory harness, its entry test and its shell runner.
It does not change production Autopilot policy. The Phase 1 request supplies the
expected outcomes. Keep candidate failures visible with a named gap; never skip,
todo, catch-and-pass, or change an expected outcome to fit the candidate.

Run the native CLI dispatch, launcher ticks, workflow runner and durable stores
against a disposable project. Use real Git commits, branches, worktrees and a
local bare origin. Only external services and agent reasoning are fake. GitHub
must retain mutations and answer REST, GraphQL, claims, PR head/check readback
and merge requests. Reject unsupported service operations. The interpreter must
support verdict, no verdict, refusal and delayed completion. Scripted workers
read the actual bundled workflow and step briefs and use public done, gate,
park, open, resend, evidence and base-check commands. They must not write native
approval fields or invent a runtime receipt. Scripted checker/merge behavior
follows the bundled skills; it is a deterministic policy actor, not an AI check.

Exercise these independently, with an asserted final merge or a real decision
question and no lead repair commands:

1. Small change to one merged PR; bug and feature to merged PR 1 and PR 2.
2. Restart during work: retained claim, run, completed steps and native chat
   identity resume without another allocation or publication.
3. Lost verdict: ticks send nothing again; the explicit synthetic person's
   resend decision permits exactly one new attempt, then completion.
4. A stuck run parks, keeps progress and wakes when its named blocker clears.
5. A full pane budget and full check slots defer work without losing it; release
   admits it. An undispatched dead interpreter holder is reclaimed. A dead dispatched holder keeps an unknown outcome; queue recovery never
   sends its old request again.
6. Another machine takes the claim: the old machine cannot continue or publish.
7. PR 1 changes after code begins (#2897): code retains its approved boundary,
   returns through the supported prompt route and integrates the current source.
8. A persisted pre-card run resumes on the candidate after an upgrade. Its
   historical decisions are retained; missing coverage cannot authorize a merge.
   Model unavailable coverage by omitting the recorded Story contract and path
   inventory as well as derived coverage. Removing only the cache leaves the
   approved reconstruction evidence available to the workflow runner.
9. A base-only merge retains the issue patch, uses a separate bounded integration
   count, retains failed validation in history and clears later evidence. Fresh
   validation reaches merge without consuming a defect repair. A real issue
   edit uses the defect budget; neither budget resets the other.

9. An automatic merge starts a fresh scripted auditor through the native audit
   command, saves OK with parent/merge evidence and posts the verdict once. A
   repeat command reuses the saved result without launching another agent. A BAD
   verdict creates a real revert branch and PR, preserves the remote base and
   records one alert.

Every scenario records its actual commands and useful structural observations.
Assertions use states, identities, hashes, counts and effects, not exact English
sentences. A bounded failure must name the stage and saved state. The shell
entry runs the complete factory in less than 15 minutes, returns nonzero on any
failure and removes its own temporary data. The `claim-transfer-open` scenario
must pass: after claim transfer, the old coordinator cannot open its current chat.
Keep this assertion enabled and return nonzero on failure. Select private HOME,
XDG_CONFIG_HOME, PDD_STATE_DIR, suite and interpreter queues. No external network,
real gh, agent, system timer or live Herdr process may run. Never touch another
process or its state. Use the repository fakes as the starting point. Keep
execution reports outside source.

After a real merge and completed audit, damage its local audit JSON. Repeated
ticks must still select and deliver a new eligible issue. Status names the held
run, PR and cause. No auditor, repeated audit publication or audit time rule is
permitted for the damaged record. Keep the shared audit authority intact.


## Stopped-pane factory (#3123)

Include a complete pane budget held by several stopped runs. Each has several area chats in one worktree, no saved session IDs, an old layout without createdWorkspaceId and an older coordinator ID for the same machine and folder. Hide Herdr IDs so bounded native discovery must prove the correct sessions. Start a second repository's coordinator and its first workflow run against the shared Herdr service; both must obtain panes through native reclamation. Verify the first run has a live area chat before waking the held runs. Later clear the blockers and resume every held run with its own current-area UUID. Assert screens exist before closes, saved sessions match each area, claim recovery preserves each admitted claim era, and foreign workspaces and busy agents survive. Use only disposable homes, config, queues and service fakes; select a unique throwaway session name for the harness.

## Validation session change (#3117)

Start a controlled validation with the native suite queue in a real factory
workflow. Hold it after it emits more than a terminal tail. End its calling
process and change the fake chat session while validation is running. A fresh
workflow status process must find the same ticket, source, log and owned child.
Release the validation once. Its full stdout/stderr, nonzero exit and complete
TAP counts must survive in the saved receipt. Command identity follows the
shared queue contract: a redacted command and its original command fingerprint. Assert one command invocation,
no duplicate ticket, no signal to a recovered process, and unchanged receipt
bytes after later observations. Finish the workflow with a fresh successful
validation; the failed attempt stays available. Use only the factory's private
home, config and queues. Retain this scenario as a failing assertion on the base.

## Dependencies

- [Launcher](../cli/autopilot-launcher.prompt.md): native tick and recovery boundary.
- [Workflow runner](../cli/workflow-runner.prompt.md): workflow and gates.
- [Parking](../cli/autopilot-parking.prompt.md): park and wake policy.
- [Interpreter queue](../cli/interpreter-queue.prompt.md): local admission boundary.
- [Autopilot skill](../../skills/pdd-autopilot/SKILL.md),
  [check](../../skills/pdd-check/SKILL.md), and
  [merge](../../skills/pdd-merge/SKILL.md): scripted agent responsibilities.
