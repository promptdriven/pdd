# Autopilot factory test

Run the complete offline factory from a source checkout:

```sh
scripts/factory-test.sh
```

The shell entry selects private home, configuration, runtime state and queue
folders and a unique fake Herdr session name. No real Herdr server is opened.
It removes its temporary folder when it exits. It has a 890-second
limit and a five-second termination grace. Any failed scenario returns a nonzero
status. A candidate gap stays a failing assertion, with its gap name in the output.

The test entry is `test/autopilot-factory.e2e.test.mjs`. Each command and timer tick
runs in a fresh Node process. Native CLI dispatch, workflow definitions, gates,
publication, parking, recovery and queue code run against real Git worktrees and
a local bare origin. Git is restricted to file transport. The private service
executables cannot call a real agent or GitHub. Service ports model GitHub REST
and GraphQL, Herdr panes and sessions, and interpreter responses. Interpreter
requests use an in-memory fetch port. No service socket is needed. Worker sockets
are denied. Tests do not read a person's agent credentials or machine queues.

The scripted worker reads the bundled workflow and each selected step brief. It
writes a small constant-value project, records completed steps through the CLI,
runs its native regression, and supplies evidence from those executions. Native
old-code proof and the interpreter fake both reject the value-one base against
the value-two expectation. The interpreter supports a verdict, a lost verdict,
a provider refusal, and delayed completion.

The scripted coordinator uses native dependency review, gates and claim checks.
The scripted checker uses a separate checkout of the published head. It runs
fresh prompt checks and a negative control on the base prompt. For a recorded
code-only bug, it verifies unchanged prompt bytes and passing checks on both
snapshots, then independently repeats the native old-code assertion failure and
new-code pass. The PR body records this evidence. A wrong or changed prompt still
requires a failing old-prompt check. A code PR must
pass its native test. PR 1 may contain the failing new native test only when its
paired code PR passes. The scripted merge actor checks explicit auto-start scope,
trust, strict mode, the current head, successful checks, and native base checks
before and after the fake GitHub merge. These actors replace AI reasoning. They
do not prove that an AI will follow the briefs or that hosted GitHub will accept
the same merge.

| Group | Required result |
|---|---|
| Post-merge audit | A closed issue still offers its pending audit. One fresh scripted auditor reproduces parent failure and merge success; its saved OK and issue comment survive a repeated command. BAD with a revert recommendation creates a real revert branch and open PR. BAD without that recommendation keeps the merge and reopens the original issue with one comment naming the gaps. Each form sends one alert that states the recommendation, preserves the base and creates no duplicate publication on repeat. |
| Check plan | A full native check saves target and baseline scope; a saved read retains it. A missing interface blocks paid dispatch. |
| Small change, bug, feature | One or two PRs reach merge; PR 2 starts stacked on PR 1. |
| Code-only bug | An unchanged correct prompt passes on both snapshots; native old code fails for the issue reason and new code passes. Independent review reaches merge. A saved route wait wakes once when the checker capability is installed. |
| Validation session change | A held native validation keeps its source, bounded secret-safe log and child identity after caller loss and a changed fake chat session. A fresh observer reads the same ticket. The custodian saves the nonzero exit and TAP counts. A later pass keeps that failed receipt. |
| Restart | Claim, allocation, completed steps and chat session survive; no duplicate publication. |
| Lost verdict | Timer ticks send nothing again; one explicit synthetic person decision permits one resend. |
| Stuck dependency | The run yields its panes, keeps its work and wakes after merge evidence. |
| Closing capacity | Absent starting panes gain confirmed close records. A working agent defers parking. A done current chat saves its screen and session before close. Retained cleanup names its retry cause, and a closing reservation blocks new starts at the run cap. |
| Stopped panes across repositories | A full shared pane budget is reclaimed from stopped runs without saved session IDs or workspace-creation fields. Same-machine coordinator claims are recovered. A second repository starts its coordinator and first workflow run. Every held run then resumes its own current session. |
| Capacity and queues | Pane and check-slot waits recover; dead holders release reservations without resending an uncertain request. |
| Claim transfer | The old coordinator cannot continue the current chat or publish after another machine takes the claim. |
| Base integration | A clean base merge uses the separate bounded integration counter, retains failed evidence and needs fresh validation before merge. |
| PR 1 re-entry | The corrected prompt survives code entry and merge; expected values stay fixed. |
| Run serialization compatibility | Without Story coverage or its recorded contract and path inventory, publication waits for a supported gate; prior decisions survive and the run reaches merge. |
| Person assignment | Manual workflow start assigns the issue to the signed-in user and warns when Autopilot holds a live claim. Assigning a claimed issue lets the active step finish, parks and releases the claim (keeping the run folder, branch and PRs), and keeps Autopilot from taking the issue again while assigned. Status shows `skipped: assigned to a person` with the count and lists assignments with no activity for 7 days. Doctor states the rule. |

Synthetic operator and person actions apply only to disposable fixtures. The test
never approves a prompt in the source checkout. The command transcript records
actor roles and child process IDs. Each scenario checks that no command used a
lead role. Fault injection changes the external fake world; the compatibility
case also removes additive fields from a disposable run record.

For one group, use Node's test-name filter, for example:

```sh
node --test --test-name-pattern='factory 2:' test/autopilot-factory.e2e.test.mjs
```

This test does not call the process-replay test. It does not run the source
repository's full suite. Its fixture project has one native test, which runs
through the native shared suite queue. The source repository's public suite is a
separate check.

The first-start scenario uses a fresh repository with a stale executable pdd on
PATH and no agent sign-in. Doctor reports both failures and start returns the
same report. No coordinator state, pane, timer, claim, PR or interpreter job is
created. Programs and account reads use controlled ports.

Every factory start runs the real doctor. Setup files and skill entrypoints live
in the private fixture home. Program, account and health observations use the
factory ports. The restart case signs out the caller profile and keeps the saved
coordinator profile healthy. Doctor and start must use that saved profile and
retain the coordinator identity.
The full-budget recovery case also runs doctor. Capacity warnings must reach
the existing guarded sweeps. A busy personal pane stays open.
The Herdr fake keeps `--session` and separate `pdd` and `pdd-autopilot`
inventories. A full workflow session admits reuse of the healthy coordinator
without allocating or closing panes. The launcher admission table also compares
the repaired start with a disposable native base when `PDD_ADMISSION_BASE_ROOT`
names that checkout. It covers capacity, saved targets, JSON 404 and the
missing-sign-in refusal.
