# Autopilot factory test

Run the complete offline factory from a source checkout:

```sh
scripts/factory-test.sh
```

The shell entry selects private home, configuration, runtime state and queue
folders. It removes its temporary folder when it exits. It has a 890-second
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
fresh prompt checks and a negative control on the base prompt. A code PR must
pass its native test. PR 1 may contain the failing new native test only when its
paired code PR passes. The scripted merge actor checks explicit auto-start scope,
trust, strict mode, the current head, successful checks, and native base checks
before and after the fake GitHub merge. These actors replace AI reasoning. They
do not prove that an AI will follow the briefs or that hosted GitHub will accept
the same merge.

| Group | Required result |
|---|---|
| Small change, bug, feature | One or two PRs reach merge; PR 2 starts stacked on PR 1. |
| Restart | Claim, allocation, completed steps and chat session survive; no duplicate publication. |
| Lost verdict | Timer ticks send nothing again; one explicit synthetic person decision permits one resend. |
| Stuck dependency | The run yields its panes, keeps its work and wakes after merge evidence. |
| Capacity and queues | Pane and check-slot waits recover; dead holders release reservations without resending an uncertain request. |
| Claim transfer | The old coordinator cannot continue the current chat or publish after another machine takes the claim. |
| PR 1 re-entry | The corrected prompt survives code entry and merge; expected values stay fixed. |
| Run serialization compatibility | Missing Story coverage cannot publish automatically; supported gates retain prior decisions and reach merge. |

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
