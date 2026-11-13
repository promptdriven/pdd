# Autopilot supervision: discussion plan

Planning proposal for [#3014](https://github.com/promptdriven/pdd/issues/3014).
Implementation and an acceptance run require Serhan's agreement on scope. This
document supplies discussion material only; it grants no recovery, account,
workspace, spending or merge authority and does not enable a supervisor.

## User outcome and scope

An ordinary operator can use a PDD-owned supervision runbook saved with the
repository's Autopilot setup to identify stalled work, recover within their saved
authority, and verify that the same issue advances. The supervisor may be an
agent following a tested runbook. A controller for every failure is unnecessary.

The proposed deliverable is a reusable runbook plus a repository-local selection
of permitted recoveries, relevant setup references and acceptance evidence. Its
storage location and setup integration remain design choices. Private manager
conversations, credentials and captured operational fixtures are excluded.

Existing fixes, issue owners and PRs stay with their work:

| Existing work | Supervision integration boundary |
| --- | --- |
| [#2951](https://github.com/promptdriven/pdd/issues/2951), timed wakeups | Observe and reuse the existing wake; do not add another timer. |
| [#2952](https://github.com/promptdriven/pdd/issues/2952), reviews | Reconcile the current review event and head through its existing route. |
| [#2939](https://github.com/promptdriven/pdd/issues/2939) / [#2974](https://github.com/promptdriven/pdd/issues/2974), delivery/readiness | Use guarded delivery and inspect its result; do not replay an uncertain send. |
| [#2949](https://github.com/promptdriven/pdd/issues/2949), notices | Reuse incident notices and their deduplication. |
| [#2907](https://github.com/promptdriven/pdd/issues/2907), accounts | Reuse supported profile selection and account-change recovery. |
| [#2962](https://github.com/promptdriven/pdd/issues/2962), durable permission scope | Read and preserve saved authority; do not create another approval system. |

No new fleet service, paid resource, reset credit use or purchase is proposed.
Product decisions, enforced approvals, repository human reviews and merge
authority retain their existing owners.

## Existing interfaces and limits

These are source contracts to consult during implementation, not evidence that
this proposal has been executed:

- [Launcher](../prompts/cli/autopilot-launcher.prompt.md): coordinator identity,
  status, delivery custody, timed reconciliation and claim recovery.
- [Core engine](../prompts/cli/autopilot-core.prompt.md): headless issue jobs,
  saved job/process evidence and terminal outcomes. Core has no coordinator chat,
  Herdr or parking; its rule is that every failure ends one job. Resuming an ended
  core job would require a separately agreed contract change.
- [Run view](../prompts/cli/workflow-view.prompt.md): passive saved progress,
  gates, approvals, decisions and evidence. [Area chats](../prompts/cli/workflow-chat.prompt.md)
  and [handoff](../skills/pdd-autopilot/steps/handoff.md) cover full-engine workers.
- [Launch profiles](../prompts/cli/workflow-launch-profile.prompt.md) and
  [local agents](../prompts/cli/agent-config.prompt.md): saved account selection
  and user-configured launchers; neither is permission to rotate accounts.
- [Parking](../prompts/cli/autopilot-parking.prompt.md): existing full-engine
  blocker, wake and release rules, including unknown custody.
- [Metrics](metrics.md): explicit recovery evidence, stable event identities and
  participating-machine coverage gaps.

The [CLI reference](cli.md#autopilot-on-this-machine) documents inspection through
`pdd autopilot status` and `pdd autopilot doctor`. For full-engine runs,
`pdd workflow view ISSUE` reads saved state, while status may inspect chat health.
Resume, replacement and account changes have distinct guarded routes in
[the run reference](cli.md#runs-on-a-github-issue). A setup must identify its engine
before choosing an interface; workflow chat commands are not a core-job repair.

## Proposed supervision pass

1. Identify the repository, machine, engine, current issue owner and saved run/job.
   Bind observations to its branch, worktree, stage, PR head and actual worker
   session or process. Inspect worker evidence separately from the coordinator.
   An idle, missing or replaced coordinator pane proves nothing about its worker.
2. Read the saved state and new observable evidence: worker/session health,
   current progress, check custody, review events, pending gates and delivery
   status. Missing or conflicting observations remain unknown. Do not infer a
   stopped worker from elapsed time or a label alone.
3. Classify the condition using the table below. Read saved user authority and
   the selected recovery permissions before any effect. Refresh ownership and
   worker custody immediately before acting. A foreign live claim stops action.
4. Apply at most the permitted recovery for this condition through the normal
   PDD and documented native agent/session interface. Retain the issue,
   conversation where supported, completed stages and pending decisions. An
   uncertain delivery is inspected, not blindly repeated. Never launch a second
   worker while the first worker or its startup remains unconfirmed.
5. Re-observe that same worker and stage. Record progress only with new matching
   evidence such as a completed tool action, saved step result, commit or PR/check
   event. A successful send or launch response alone is not verified recovery.
   If no result can be verified, preserve custody and record waiting or unknown;
   use the existing bounded retry/incident route rather than replaying stages.

## Recovery choices to agree

Every action below is a candidate for discussion, not an enabled permission.

| Condition and required evidence | Candidate action within selected authority | Verification or reason to wait |
| --- | --- | --- |
| Worker failed or ended; saved identity and end evidence match | Resume its saved session where supported; replace only through the guarded route after confirming old custody ended | Same issue and stage advances; no concurrent old worker; completed stages retained |
| Startup dialog or unconfirmed launch in the actual worker | Inspect the prompt and saved scope; resolve only an explicitly permitted routine startup action | Matching worker becomes ready and performs work; product/access decisions and enforced approvals wait |
| Account quota reached, with reset evidence when available | Wait for the reset, or select a configured account only under explicit opt-in and supported recovery | Fresh allowance/readiness evidence and same saved work advances; unknown allowance remains waiting |
| Default login changed while saved worker uses another profile | Preserve saved profile on ordinary resume; use the supported account-change route only when authorized | Selected account is ready and issue/conversation custody is preserved; otherwise show waiting for account |
| New review event for an existing PR | Deliver through the existing review route after matching current PR/head and pending work | Worker records handling that event once; stale-head review does not authorize current-head delivery or merge |
| Apparently abandoned claim | Reconcile saved owner, worker and claim evidence using existing recovery/takeover rules | One winning owner, retained branch/PR and verified continuation; live foreign or unknown ownership waits |
| Product choice, enforced gate or insufficient workspace authority | Keep the pending decision and route the exact need to the existing person/incident channel | Only the applicable later decision or saved delegation clears it; no dialog click substitutes for authority |

Account selection requires a separate explicit user choice. Discuss whether to
allow automatic selection at all, which user-configured accounts are eligible,
their priority/tie rule, and what evidence establishes available allowance.
Do not treat built-in discovery or a changed default login as selection consent.
Without opt-in, show waiting for account and recheck after the user's login
change through the supported route. If a provider cannot preserve the saved
conversation across accounts, report that limit instead of inventing continuity.
Never store credentials in PDD records, spend reset credits or buy usage.

## Recovery evidence for kitchen metrics

For each detected incident, retain the condition, timestamp, repository/issue,
machine source, run/job and worker identity, stage and relevant head, supporting
evidence, selected authority, attempted action and observed result. Keep attempted,
waiting, unknown and verified outcomes distinct. These are proposed runbook
evidence requirements, not a new metrics schema.

Use the existing metrics recovery event contract for supported facts, with stable
source/event IDs and a sanitized evidence link; repeated observations must not
count the same recovery twice. Keep private paths, raw chats and credentials out
of shared metrics. Identify missing participating sources. A newly discovered
product bug becomes an evidence-backed issue, or reopens the matching still-broken
issue through the authorized issue-reporting route; do not duplicate its owner.

## Proposed delivery and acceptance sequence

1. Agree scope: permitted automatic actions, account-selection policy and the
   single-machine acceptance run. Also select the initial engine and record
   unsupported recovery routes. This is the implementation gate.
2. After agreement, draft the owning prompt changes, small Stories and expected
   cases for setup storage and supervision. Derive expectations from the agreed
   policy. Preserve existing recovery owners; a missing interface is an explicit
   gap, not permission to create an alternate controller.
3. Prove single-machine recovery with reproducible, sanitized fixtures and native
   session/process evidence. Candidate cases are below; agree exact expectations
   before implementing. No live account or startup dialog experiment is performed
   merely by accepting this discussion document.
4. Only after single-machine acceptance, use two existing machines against the
   shared ownership records. Attempt simultaneous recovery and an ownership
   change during inspection; require one admitted worker, no foreign-session
   effects and retained saved work. Collect evidence from both machines and mark
   any missing source. Do not provision a service or paid machine.

| Proposed single-machine case | Required observation to discuss |
| --- | --- |
| Pause/resume a saved issue at an unfinished stage | Same issue, branch and resumable conversation; one continuation; completed stages unchanged; new stage evidence |
| Replace a positively ended worker | Old custody confirmed ended before replacement; same saved issue/progress; new worker advances once |
| Coordinator idle or absent while worker works | No worker restart, duplicate worker or claim release |
| Quota wait and changed default login | No unconfigured selection or spending; wait without opt-in; authorized supported account change preserves saved work |
| Startup requires an unresolved decision or enforced approval | Decision remains pending; no automatic click-through or fabricated approval |
| Uncertain send, duplicate wake/review, or restart during recovery | Inspect saved delivery and worker evidence; no duplicate action or replay of completed stages |
| Stale claim and competing owner | Existing ownership route admits one owner; unknown/live foreign custody prevents recovery |

Acceptance must attach the before-state, injected condition, permitted action,
after-state and observed progress for each selected case, including negative
controls. Native tests and any prompt checks prove only their declared surfaces;
the real single-machine and two-machine runs need their own evidence. This plan
contains no implementation or executed supervision acceptance result.
