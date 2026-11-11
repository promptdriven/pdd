# Autopilot base red

Own `src/autopilot-base-red.mjs`. When a CI check or the full test suite of a PR is
red, the [Autopilot core](autopilot-core.prompt.md) asks this module whether the red
is the PR's own or the base branch's. A failure that also fails on the base is
**base-red**: the job gets no repair, no END and no `pdd:stuck`. Its PR stays open
and waits, the job holds no slot, and the work repository gets one deduplicated
main-red issue. A CI check that failed once runs once more first.

Why: a red or flaky test on the base blocks every PR, but no PR caused it (#3181).
In chaos run B7 a failing test on main cost one repair and gave a healthy issue
`pdd:stuck`; in T03 a known flaky CI test ended a run after 2 repairs. A repair
cannot fix the base, so it only spends the repair budget. A wrong base-red never
merges anything: its cost is a wait. So the rules choose base-red when a side
cannot be read.

## CI: one rerun, then the base tip

`ciVsBase(ctx, job, ci)` takes a red `ci` from the core's `ciState`: `failed` (the
names of the failed check runs and commit statuses), `failedRuns` (`{id, name, app}`
of each failed check run, `app` is the app slug), `running` (the names of the head's
checks that are not completed yet) and `sig`. It returns a CI result for the merge
check.

1. **Rerun once (B1).** Each failed check run whose name has no rerun at this head
   gets one: `POST repos/REPO/actions/jobs/ID/rerun` when `app` is
   `github-actions`, else `POST repos/REPO/check-runs/ID/rerequest`. While another
   check of the head still runs (`running` is not empty) and such a rerun is still
   due, the result is pending and no rerun is asked yet: GitHub refuses a job rerun
   while its workflow run still runs (review R1, S2). The job saves `ciRerun {head,
   names, asked}`: `names` are the check names that had their one rerun at this head
   (a new head starts empty), each added only after a 2xx answer; `asked` the run ids
   that were rerun, each with its time. A commit status, a run without a safe integer
   `id`, and a rerun call that returns a status of 300 or more get no rerun in this
   call; they go to step 2 at once.
2. **Wait for the rerun.** The result is pending while a rerun was asked in this
   call, or while the failed run of a name is still an asked run (GitHub does not
   show the new run yet), for at most the quiet period (`ctx.quiet`) after the ask:
   `{...ci, state: 'pending', pending: NAMES, sig: 'SIG|rerun:NAMES'}`. The check-runs
   read gives the latest run of each name, so a rerun shows as pending, then green or
   red.
3. **Compare with the base tip (B2).** The base tip is `origin/BASE` after a fetch.
   For each failed name, the check runs and commit statuses of the tip decide (one
   read per tip and tick; a merge in this tick reads the tip again): a completed run
   or a status of that name that failed is red; one that is not completed, or that
   ended with no result (`cancelled`, `stale`, `action_required`: review R1, S4), is
   pending; otherwise (good: `success`, `neutral`, `skipped`, or no run of that name)
   it is green. So a run that someone cancelled on the tip is never base-red and
   files no main-red issue.
   - Any name pending on the tip: `{...ci, state: 'pending', pending: NAMES, sig:
     'SIG|base:TIP'}`. No repair.
   - Names that are not red on the tip are the PR's own red: `{...ci, state: 'red',
     failed: OWN}`. When other names are red on the tip, `onBase` is the second line
     "Also red on the base (BASE at SHA7), not from this change: NAMES."
   - Every name red on the tip: `{...ci, state: 'base-red', baseRed: {what: 'ci',
     sha: TIP, names}}`.
4. A **main-red job** gets step 1 and 2, never step 3: its own red is red.

A main-red job is a job whose issue body (`job.body`) holds the marker prefix
`<!-- pdd:autopilot-core:base-red:`.

## Suite: the same tests at the merge base

`suiteVsBase(ctx, job, {ci, review, suite, vectors, reds}, tools)` returns `'wait'`
(the merge check stops for this tick) or a suite result for the merge check. A suite
that is not `fail`, and every suite of a main-red job, comes back unchanged unless
the CI is `base-red` (the hold, below).

1. **The base commit** is `git merge-base origin/BASE HEAD` of the job head, after a
   fetch of the base.
2. **The base suite (B3)** is one run of the same test command at the base commit,
   for the whole machine: every job of this machine on the same base commit reuses
   it. Its record is `ROOT/base-suite/SHA.json` (below). No record: start it. A
   record in state `running`: wait for it. Any other state is the result, also
   `broken`; there is one run per base commit.
3. While the base suite runs, the result is `'wait'`: the job saves `baseSuite: SHA`
   and its quiet clock starts again (`progress {at: now, running: true}`), so no
   repair starts before the compare, also when the review is red. The base suite's
   own process rule bounds the wait.
4. Base `pass` or `broken`: the suite result comes back unchanged (the PR's own red,
   as before the compare).
5. Base `fail`: the head's failing tests come from the job's suite log, the base's
   from the record (`failingTests`, below). A head test also fails on the base when
   the base has a test with the same name and the same file, or with no file on one
   side (`sameTest`).
   - A side with no failing test, or with more than 50: every failure counts as
     base-red.
   - Head tests that do not fail on the base are the PR's own red: `{...suite, text}`
     with two lines after the first line of `suite.text`: "Failing tests from this
     change: TESTS." and, when some head tests also fail on the base, "Also red on
     the base (SHA7), not from this change: TESTS." (each test as `NAME (FILE)`, or
     `NAME` with no file). So the repair does not chase them.
   - No new head test: the suite is base-red: `{state: 'base-red'}` with `{what:
     'suite', sha: BASE COMMIT, names, tests: THE HEAD TESTS, tail: THE BASE TAIL}`.

## The hold (B4)

After the compare, the hold applies when the CI or the suite is `base-red`. When both
are, the suite wins (it names the tests).

- Another red finding (`reds` is not empty, or the suite is the PR's own red): no
  hold. The base-red part adds no red line, so the repair gets only the PR's own
  findings; it comes back as `{state: 'base-red'}` (a suite) or is left out (a CI).
- The review is not `pass` yet, the job's suite or the replay run (`vectors`) is
  still `running`, or a CI check is still pending (review R1, S1): no hold yet; the
  merge check waits as usual and the job keeps its slot. So a CI red of the PR's own
  that comes later still gets its repair.
- Else the job enters the base-red state and the result is `'wait'`: it leaves the
  merge lane (`tools.leaveLane`), saves `baseRed {what, sha, tip, names, tail,
  fingerprint, since, report}` (`tip` is the base tip at entry, `report` is the
  main-red issue `{number, ref}` or null) and files or finds the main-red issue.
  A failed GitHub call keeps `report` null and only warns.

`baseRedWait(ctx, job, tools)` is the merge check of a job in the base-red state,
each tick:

- The quiet clock starts again (`progress {at: now, running: true}`): waiting never
  ends a job. A null `report` is filed again.
- Read the base tip (fetch) and, with a report, the main-red issue (a deleted or
  moved issue, status 404 or 410, counts as closed; another failed read is a tick
  error and the job waits). A closed report while another open issue has the same
  marker (for example the first issue of a two-machine race, after this machine's
  duplicate was closed): the report becomes that open issue and the job waits on.
  When the tip is
  not `baseRed.tip` and the issue is closed (or there is no report): clear `baseRed`
  and `ciRerun` and refresh the PR onto the base (`tools.refreshBase`). CI and the
  suite run again on the new head; a red again compares again. When the issue is
  closed and the tip did not move (a person closed it, for example as flaky): clear
  `baseRed` and run the red check once more at the same head (review R1, S3): a CI
  red clears `ciRerun` (one more rerun), a suite red clears `suite`. A red again
  compares again; then a new main-red issue names the closed one.
- After the quiet period in the base-red state, one `stuck` alert through
  `ctx.ports.alert` (`baseRed.alerted`), as the merge lane's wait alert.

`baseRedWaiting(job)` is true for a job in phase `pr` with `baseRed`: it holds no
slot, so other issues go on. `baseRedStatus(job)` is `; main is red (NAME) since
TIME; no slot` for such a job (NAME the first name, `and N more` for the others; TIME
in ISO form), else the empty string.

## The main-red issue

`fileMainRed(ctx, job, red)` returns `{number, ref, found, earlier}` or null.

- **Where** (release lead, Nov 11; in one place, `mainRedRoute(settings)`): always
  `file`, in the work repository (`ctx.repo`), in auto and observe mode and with every
  `report` setting (also `off`). It is the repository's own work, not a report to
  PDD; the [report owner](autopilot-reports.prompt.md) stays for promptdriven/pdd.
- **Fingerprint**: the first 16 hex digits of the SHA-256 of `WHAT` and the sorted
  names, one per line (never the commit), so the same failure on a later base commit
  is the same issue. **Marker**: `<!-- pdd:autopilot-core:base-red:FINGERPRINT -->`.
- **This machine first** (review R1): the machine record `ROOT/main-red/FINGERPRINT.json`
  (`{number, at}`) is written right after a post or a match. When it names an issue
  that is open (`GET repos/REPO/issues/N`, a consistent read), that issue is the
  result (`found: true`) and the list is not read: GitHub's label list can lag a
  write, so several jobs that turn base-red in one tick would each file an issue.
- **Dedup**: then read `issues?state=all&labels=pdd:main-red&per_page=100` (at most
  5 pages) and look at the issues (not PRs) whose body has the marker. Only an **open**
  match is the result (`found: true`), the one with the lowest number; nothing is
  posted. So a second job with the same base-red files no second issue. A closed match, of any age, means that the
  same red came back after its issue was closed: a new red event. It files a new
  issue, and `earlier` is the number of the newest closed match (the highest
  number). So no job waits on a closed issue while nobody works on the new red.
- **Two machines at once** (review R1): both can read no open match and both post.
  After its post, a machine reads the open matches again. When an open match has a
  lower number than its own new issue, it closes its own issue (`state: closed`,
  `state_reason: not_planned`) with one comment "Duplicate of #N." and the result is
  #N (`found: true`). A failed close or comment only warns; the result is still #N.
  A machine whose read did not show the other issue yet keeps its own; the wait (below)
  corrects it later.
- **New issue**: title `Main is red: NAME` (the test or check name, `(and N more)`
  for the others, at most 200 characters, public text). Labels: `pdd:main-red` and,
  only in auto mode when `settings.label` is set, that label, so Autopilot takes the
  issue as its own work (Serhan, Nov 10: "Autopilot fixes a failing or flaky test on
  main itself, as its own issue"). Observe mode builds nothing, so it adds no opt-in
  label (release lead, Nov 11). The body (public text through `ctx.publicBody`) has: the base
  branch and commit, the check names or the failing tests (at most 20, with "and N
  more"), the PR and issue where it was seen, `Earlier: #N` when a closed issue had
  the same marker, what Autopilot does while it is red
  (no repair; the PRs wait with no slot, then update onto the base when this issue is
  closed and the base moves), a redacted log tail of the base suite (at most 30
  lines, [secret redaction](secret-redaction.prompt.md)) and the marker as its last
  line.

## Failing tests

`failingTests(text, limit = 50)` returns `[{name, file}]` (`file` is a string or
null), in log order, at most `limit` entries. It has the shape of the core's
`failingTests` of #3227 fix 4, so that one can replace it with one import.

- **TAP** (node --test): a line `not ok N - NAME` at any depth (a subtest is
  indented). The `location: 'FILE:LINE:COL'` line in the next 12 lines gives its
  file. The failure stays open until its location line, the next `ok N` or `not ok
  N` line, or 12 lines; only then does it join the list (by the one-test rule below).
  So two failures with one name in two files are two tests (review R1, P2: else a
  new failure in a second file hid behind a base failure in the first).
- **Spec reporter**: a line `✖ NAME (DURATION)` at any depth; a `test at
  FILE:LINE:COL` line right before it (the failure summary) gives its file. The
  summary header `✖ failing tests:` is not a test. Color codes are removed first.
- A line with a `# TODO` or `# SKIP` directive is not a failure. NAME is trimmed and
  cut to 200 characters; a blank NAME does not count.
- One test is one entry (`sameTest`): the same name with the same file, or with no
  file on one side (then the entry keeps the file that is known). So the spec
  reporter's summary repeats no test.

The engine reads the job's suite log and the base suite log in 1 MB parts, whole lines
only, so a long log never sits in memory at once. It keeps only the lines that
`failingTests` reads (`not ok`, `location:`, `test at`, `✖`, each cut to 4,000
characters, and each `ok N` line as a short `ok` line) and calls `failingTests` once
on them with a limit of 51; more than 50 tests sets `more`. Every `ROOT/` and
`file://ROOT/` (the checkout root) goes from names and files, so one test in two
checkouts is one test.

## The base suite record

`ROOT/base-suite/SHA.json` (`ROOT` is `ctx.root`, mode 0600, written atomically):
`{sha, state, tests, more, tail, text, at, cwd, agent, restarts, deaths, quiets}`.
`state` is `running`, `pass`, `fail` or `broken`; `tests` (`[{name, file}]`, at most
50) and `more` come from `failingTests`; `tail` is the redacted last 30 lines of its log; `text` says why a
broken run is broken; `at` is the last change. A record that cannot be read counts as
missing.

- **Start**: a clean detached checkout `worktrees/base-suite-SHA12` (an old folder is
  removed first) and `tools.startJob(ctx, {issue: 'base', branch: BASE, head: SHA},
  'suite', CWD, '', tools.queuedCommand(ctx, CWD, settings.testCommand), {CI:
  'true'})`: the machine's suite queue, the dependency install of the core, and a job
  id that starts with `base-suite-`, so no issue's cleanup removes its files.
- **Watch**: once per tick and record, the core's process rule
  (`tools.watchProcess(ctx, job, agent, 'suite')`, for the job that reads it). A quiet
  stop, a dead run, a signal, exit 86 or 127, a runner line (`tools.runnerLine`) or an
  empty log starts it again in the same checkout, at most twice; then `broken`. The
  backstop gives `broken` at once.
- **End**: exit 0 is `pass`; another exit is `fail`. Then the checkout goes
  (`tools.removeTree`).
- **Prune**: when a run starts, records older than 14 days go, and the oldest go
  past 50 records, with the log files of their run.

`stopBaseSuite(ctx, job)` runs with the core's `stopChecks`: when `job.baseSuite`
names a running record and no other job file in phase `pr` has the same
`baseSuite`, it stops that process and removes the record, so a later need starts it
again. It clears `job.baseSuite`. It never throws.

## Public contract

Exports: `ciVsBase`, `suiteVsBase`, `baseRedWait`, `baseRedWaiting`,
`baseRedStatus`, `stopBaseSuite`, `fileMainRed`, `failingTests`, `sameTest(a, b)`,
`baseRedFingerprint(what, names)`, `mainRedRoute(settings)`, `MAIN_RED_LABEL`
(`pdd:main-red`) and `BASE_RED_MARKER` (`pdd:autopilot-core:base-red`).

Ports come from the core: `ctx` (`gh {call, ok}`, `git`, `fs`, `now`, `root`, `dirs`,
`repo`, `state`, `settings`, `jobs`, `quiet`, `saveJob`, `publicBody`, `warn`,
`ports.alert`) and `tools` (`startJob`, `queuedCommand`, `watchProcess`, `readTail`,
`removeTree`, `refreshBase`, `leaveLane`, `runnerLine`).

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): required for the log tails.

The link to the core above is navigation only (the core requires this module, so a
required link back would be a cycle).
