# Autopilot CI jobs

Own `src/autopilot-ci-jobs.mjs`. This module reads the GitHub Actions workflows of a
repository's base branch and sorts each CI job into one of three kinds: **covered**
(Autopilot's own full suite runs the same command), **local** (Autopilot can run its
commands on its own machine) or **CI-only** (the job needs GitHub). It also plans the
local jobs for a PR head, reads their results, writes the CI lines of the merge note,
and keeps the record of the CI-only jobs that did not run before a merge, so that they
run on the base branch later.

Why (#3260, Serhan's decision B with CI job sorting, Nov 11): in a person's private
repository GitHub Actions often does not start a run (the account's Actions minutes or
spending limit). Autopilot must not wait forever for CI that cannot start. When CI runs,
its own result counts and nothing runs twice. When CI does not start, the local full
suite and the local jobs are the proof, and the CI-only jobs run on the base branch when
CI works again. The [Autopilot core](autopilot-core.prompt.md) finds that CI did not
start (`ci.notStarted`, the machine record `ciDown`); this module never decides that.

Security: the commands come only from the workflow files of the base tip
(`origin/BASE`), never from the PR head, because a PR can change a workflow. A job
whose text has a `secrets.` reference, or a `${{ }}` expression outside the known list,
is never run.

Every reader here fails safe: what it cannot read is CI-only, never local or covered.

## Read the workflows of the base tip

`readCiJobs(input, ports)` reads the base tip with the `git(args)` port (it returns the
trimmed stdout and throws when git fails). `input.base` is a branch name (letters,
digits, `.`, `_`, `/` and `-`, not starting with `-` and with no `..`); any other value
throws `TypeError("base must be a branch name")` before any git call.

1. `rev-parse --verify -q origin/BASE^{commit}` gives the tip, then `ls-tree -z TIP --
   .github/workflows` gives the folder's tree id. No folder: no CI
   (`{tree: null, jobs: [], summary: "CI: none"}`).
2. **Cache.** `ROOT/ci-jobs.json` (`input.root` is the state folder) keeps
   `{schema: "pdd.ci-jobs.v1", tree, files, summary}`. When its `tree` is the current
   tree id, the files come from the cache with no other git call. Else
   `ls-tree -z -l TREE` lists the folder. Only blobs named `*.yml` or `*.yaml` at the top
   of the folder count, in the order of the listing (GitHub reads no subfolder). A blob
   larger than 256 KiB is not read (`text: null`, `error: "the file is larger than
   256 KiB"`). Each other blob is read with `cat-file blob SHA`; a read that throws gives
   `text: null` with the git message. More than 50 files: no file is read, and the result
   is one CI-only entry (below). The new cache is saved (mode 0600, the folder 0700;
   a temp file, then a rename), with the summary of this read. A cache hit whose summary
   changed (other sort inputs) saves the new summary.
3. A git error in step 1 or 2 is fail safe: one CI-only entry for the folder, and the
   cache is not changed.
4. Then `sortCiJobs` sorts the files (below) and the result is
   `{tree, jobs, summary}`.

`cachedCiSummary({root}, {fs})` returns the `summary` of the cache file, or `null` when
there is none or it cannot be read. Status uses it with no git call.

## The YAML subset

`parseWorkflowYaml(text)` reads the part of YAML that workflow files use, with no
dependency. It returns the value, or throws an `Error` whose `code` is `yaml` and whose
message names the line ("line N: WHY").

It reads:

- block mappings and block sequences by indentation (spaces only), also a sequence at
  the same indentation as its key, and a mapping that starts on its item line
  (`- uses: x`);
- plain, single-quoted (`''` is one quote) and double-quoted scalars on one line
  (escapes `\\ \" \/ \n \t \r \0 \b \f \xHH \uHHHH`);
- flow sequences `[a, b]` and flow mappings `{a: b}` on one line, also nested;
- block scalars `|` and `>` with the chomping indicator `-` or `+` and an optional
  indentation digit (`>` folds lines with one space; a blank line is a line break);
- comments (a `#` at the start of a line or after a space, outside a quoted scalar or a
  flow collection; a `#` in a plain scalar after a space starts a comment, as in YAML),
  one leading `---` line and a final `...` line.

Values: an empty value, `~` and `null` are `null`; `true` and `false` are booleans; every
other plain scalar is a string (numbers stay text, so `22` and `'22'` are the same). Keys
are strings.

It refuses: a tab in the indentation, an anchor (`&`), an alias (`*`), a tag (`!`, also
`if: !cancelled()`), a merge key `<<`, the key `__proto__`, a complex key `?`, a reserved
start (`@`, `` ` ``, `%`), a second document, a duplicate key, a quoted scalar or a
flow collection over several lines, a plain scalar that goes on to the next line, a
`key: a: b` value, a line with unexpected indentation, more than 5000 lines, and a depth
over 40.

## Sort each job

`sortCiJobs({files, base, branch, changed, testCommand, scripts, machine})` is pure.
`files` is `[{name, text, error?}]` (text `null`: unreadable). It returns
`{jobs, summary}`.

**Which workflows count.** A file counts only when `workflowRunsOnPr(text, branch, base,
changed)` of the core is true: it can run on a PR head of `branch` into `base` for the
changed files (`changed: null` admits every path filter). The core's reader owns the
`on:` rules; an unreadable file counts (the safe side). `branch` defaults to
`pdd/core-autopilot` (the form of the core's job branches).

**An unreadable file** (no text, a YAML error, a root that is not a mapping, or `jobs`
that is not a non-empty mapping) is one CI-only entry with `job: null`, `check: null`,
`checks: []`, need `unreadable` and why "Autopilot could not read the workflow file:
WHY". **More than 50 files** is one CI-only entry with `workflow: null`, need
`too many workflows` and why "the base has N workflow files (more than 50)".

Each job of a counted file (in file order) is sorted for this machine:
`machine.platform` (`process.platform` by default: `linux`, `darwin` or `win32`, so the
family Linux, macOS or Windows) and `machine.node` (`process.versions.node` by default).

### Job rules (in this order; the first match decides)

| Job | Result |
|---|---|
| not a mapping | CI-only, need `unreadable`: "Autopilot could not read the job" |
| `uses` (a reusable workflow) | CI-only, need `reusable workflow`: "calls the reusable workflow X" |
| `steps` is not a non-empty list of mappings | CI-only, need `unreadable`: "Autopilot could not read the job" |
| a `secrets.` or `secrets[` reference or `github.token` anywhere in the job or in the workflow's `env` | CI-only, need `secrets`: "uses a secret" |
| `environment` | CI-only, need `environment`: "deploys to the environment NAME" |
| `services` | CI-only, need `services`: "needs service containers" |
| `container` | CI-only, need `container`: "runs in a container" |
| `if` is false for a ready PR (the conditions below) | not listed: the job does not run on a PR |
| `if` that Autopilot cannot check | CI-only, need `condition`: "has a condition that Autopilot cannot check: IF" |
| `strategy` or `strategy.matrix` that is not a mapping, or that the matrix rules refuse | CI-only, need `matrix`: "builds its matrix from an expression" (or its strategy) or the matrix error |

Then each matrix entry (one entry `{}` when there is no matrix) is sorted by the runner,
the versions and the steps. A job with no `runs-on` is CI-only (need `unreadable`).

**Conditions.** A condition is the `if` text, also inside `${{ }}`, made of terms joined
by `||` and `&&` (`&&` binds closer; no parentheses). Known terms, for a ready (not
draft) PR: `github.event_name == 'NAME'` and `!=` (the event is `pull_request`),
`github.event.pull_request.draft == false` or `== true`, `!github.event.pull_request.draft`
and `github.event.pull_request.draft`, `always()`, `success()`, `!cancelled()` (true),
`failure()`, `cancelled()` (false), `true` and `false`. The YAML booleans `true` and
`false` are the same. Any other term makes the condition unknown. So the draft filter
`github.event_name != 'pull_request' || github.event.pull_request.draft == false` is true.

**Matrix.** Each key of the mapping except `include` and `exclude` is an axis whose value
must be a non-empty list of scalars. The entries are the product of the axes in key order (the
first axis changes slowest). `exclude` (a list of mappings of scalars) removes each entry
that has all of its pairs. Each `include` mapping of scalars is added to every entry
whose own values it does not change; when it fits no entry, it is a new entry. More than
256 entries, an axis or an include value that is not a scalar, and an `include` or
`exclude` that is not a list of mappings are matrix errors.

**Check name.** The job's `name` (a scalar) or its id. When the name has a `${{ }}`
expression, `matrix.KEY` expressions become the entry's values and the name gets no
suffix; else a non-empty entry adds ` (V1, V2)`: its values in entry key order. This is
the name of the check run on GitHub.

**Runner.** `runs-on` is a string, or a list of one string; `matrix.KEY` expressions
become the entry's values. `ubuntu-*` is Linux, `macos-*` is macOS, `windows-*` is
Windows. Another family than the machine's: CI-only, need `Linux`, `macOS` or `Windows`,
"runs on LABEL (this machine is FAMILY)". Any other label, a list of more labels or a
mapping: CI-only, need `runner LABEL`: "runs on LABEL".

**Versions.** A setup step decides the versions:
- `actions/setup-node` whose `node-version` has a `${{ matrix.KEY }}` expression: the
  value with the entry's values filled in must match the machine's Node version: `N` or `N.x` the major, `N.M` or `N.M.x` major and minor,
  `N.M.P` the full version. Another value (also `lts/*`): CI-only, need `Node V`, "uses Node
  V (this machine has Node X)". A version written once, not from the matrix, is not
  compared: the machine runs its own version.
- another `actions/setup-*` step with a `with` value from `${{ matrix.KEY }}`: CI-only,
  need `TOOL V` (TOOL is the action name after `setup-`), because Autopilot cannot know
  the machine's version of that tool.

### Step rules

Steps are read in order. Each step is a setup step (not run), a suite step, a local
command, or a reason for CI-only. A step that has `uses`:

- `actions/checkout`, `actions/cache` (also `actions/cache/restore` and
  `actions/cache/save`) and every `actions/setup-*`: a setup step (any `@ref`).
- any other action (a local `./` action, a `docker://` image, CodeQL and others):
  CI-only, need `CodeQL` for `github/codeql-action/*`, else the action's `OWNER/REPO` (or
  `local action`, `docker image`): "uses ACTION".

Any other step (no `uses` and no `run` string) is CI-only (need `unreadable`). A step
with `run` (a string):

1. **Condition** (`if`): false skips the step; unknown is CI-only (need `condition`).
2. `continue-on-error: true` skips the step (it cannot fail the job); another value that
   is not `false` is CI-only (need `condition`).
3. **A report step** is skipped: its `if` has `always()` or `!cancelled()` and its text
   writes `GITHUB_STEP_SUMMARY`.
4. **Shell**: the step's `shell`, else `defaults.run.shell` of the job, else of the
   workflow. Only no shell, `bash` and `sh` run locally; another shell is CI-only (need
   `shell`: "uses the shell X").
5. **Working directory**: the step's `working-directory`, else the job's, else the
   workflow's `defaults.run`. Only `matrix.KEY` (the entry's value) and `github.workspace`
   (the checkout itself, `.`) are filled in. The result must be a relative path with no
   `..` part and no other expression; else CI-only (need `working directory`).
6. **Environment**: the workflow's, the job's and the step's `env` mappings, in that
   order (a later name wins). Names must be shell names; values are scalars (`null` is
   empty). An `env` that is not such a mapping is CI-only (need `unreadable`).
7. **Expressions** in the run text and the environment values: the known list is `matrix.KEY` (a key of the entry), `runner.os`, `runner.temp`,
   `github.workspace` and `env.NAME` (a name of the environment above whose value has no
   expression). Any other expression, and a `${{` with no `}}`, is CI-only (need
   `expression`: "uses the expression ${{ X }}"). The expressions stay in the text; the
   plan fills them in.
8. A text that writes `GITHUB_ENV` or `GITHUB_PATH` is CI-only (need `GITHUB_ENV`):
   Autopilot cannot pass values between its steps that way.
9. **Commands.** Lines joined after a final `\`; the body of a here-document
   (`<<WORD`, `<<-WORD`, `<<'WORD'`) belongs to its command line; blank and `#` lines go.
   Each line splits at `;`, `&&` and `||` outside quotes into commands, after leading
   `if`, `elif`, `then`, `else`, `do`, `while`, `until` and `!` go. Each command is one of:
   - control: nothing left, `fi`, `done`, `esac`, `{`, `}`, `(`, `)`, or a `for` or
     `case` head;
   - plumbing: `set …`, `exit …`, `true`, `:`, an assignment alone (`NAME=VALUE`), or
     `export`/`readonly`/`local` with only assignments or names;
   - probe: `echo` or `printf`; `command -v`, `which`, `type` or `hash` with names; or one
     word with `--version`, `-v`, `-V` or `version`;
   - system install: a package manager (`apt-get`, `apt`, `brew`, `yum`, `dnf`, `apk`,
     `choco`, `snap`, `port`, `pacman`, `zypper`), also after assignments, `sudo` and its
     flags;
   - install: `npm ci`, `npm install`, `npm i`, `pnpm install`, `pnpm i`, `yarn install`,
     or `yarn` with only flags;
   - suite: the full test command (below), also with redirections (`2>&1`, `>FILE`,
     `>>FILE`) and pipes into `tee`;
   - sudo: another command that starts with `sudo`;
   - real: anything else.
10. The step is: CI-only (need `system packages`) when it has a system install and a real
    command; CI-only (need `sudo`) when it has a sudo command; a suite step when it has a
    suite command and no real command; a local command when it has a real command; else
    a setup step (installs, system installs, probes, plumbing and control only). Autopilot
    never runs a setup step: a local job that needs a tool that the machine lacks fails
    locally with a missing tool.

**The full test command** is `testCommand` (spaces made single). When it is an npm test
spelling (`npm test`, `npm run test`, `npm t`, `npm run-script test`), or it is exactly
`scripts.test`, every npm test spelling and the text of `scripts.test` also count.

### Kinds

| Kind | When | `commands` |
|---|---|---|
| CI-only | any reason above | `[]` |
| local | no reason, and at least one local command | the local commands' texts |
| covered | no reason, no local command | the suite commands (empty when the job has only setup steps) |

A local job that also has a suite step has `suite: true`: its suite part is covered by
the local full suite, and only its other commands run locally (#3260: "if ... same thing
is being done by github ci then no point").

**Entries.** A job with no matrix is one entry. In a matrix job, each covered or local
matrix entry is its own entry, and all CI-only matrix entries of the job are one CI-only
entry: `checks` lists their check names, `need` is their distinct needs (at most 3,
joined with `, `) and `why` is the first one's (with ", and N more" for more). A CI-only
reason of the whole job (the job rules) gives one entry whose `checks` are the check names
of all its matrix entries (the job name when the matrix cannot be read).

Each entry is `{workflow, title, job, check, checks, kind, why, need, suite, commands,
steps, matrix, dispatch}`:

| Field | Meaning |
|---|---|
| `workflow` | the file name, for example `ci.yml` (`null` for the too-many entry) |
| `title` | the workflow's `name` when it is a string, else the file name |
| `job` | the job id (`null` for a file entry) |
| `check` | the check name; for a combined entry, the job's name |
| `checks` | the exact check names the entry stands for |
| `kind` | `covered`, `local` or `ci-only` |
| `why` | one line for a person |
| `need` | for CI-only, the short need (above); else `null` |
| `suite` | `true` when the job also runs the full test command |
| `commands` | see Kinds |
| `steps` | for local, the steps to run: `{name, shell, script, workingDirectory, env}` (`shell` is `null`, `bash` or `sh`; `env` the merged environment); else `[]` |
| `matrix` | the entry's matrix values (`{}` with no matrix; `null` for a combined entry) |
| `dispatch` | `true` when the workflow has `workflow_dispatch` (the core's `workflowTriggers`) |

The `why` of a local entry is "runs N command(s) that Autopilot can run on this machine"
(", and the full test command" with `suite`); of a covered entry "runs only the full test
command (COMMAND)", or "runs only setup steps".

## The summary line

`ciJobsSummary(jobs)` is `CI: A covered, B local, C CI-only` and, when C is above 0,
` (NEEDS)`: the distinct needs of the CI-only entries in order, at most 4, then
`, and N more`. With no entry it is `CI: none`. Example: `CI: 2 covered, 1 local, 1 CI-only
(CodeQL)`.

## Local jobs at the final head

These run only when CI did not start for the head. When CI runs, CI's own result counts.

`localJobPlan({jobs, head, checkout, temp, machine})` plans each local entry for the PR
head (`head` is 40 hex digits; `checkout` and `temp` are absolute paths; else it throws
a `TypeError`; `machine.platform` as for the sort). The commands are the base tip's, read by `readCiJobs`, never the head's.
The caller runs each plan entry in a clean checkout of the head, after the same
dependency install as the full suite. Each plan entry is
`{key, workflow, job, check, head, cwd, env, command, steps}`:

- `key` is `WORKFLOW#CHECK`; `cwd` is the checkout.
- `env` is the process environment to add: `CI=true`, `GITHUB_WORKSPACE` (the checkout),
  and `RUNNER_TEMP`, `GITHUB_STEP_SUMMARY` and `GITHUB_OUTPUT` in the entry's own folder
  `TEMP/job-N` (N from 1, the entry's place among the local entries).
- `steps` are `{name, command, args, cwd, env}`: `bash` with `-e -c SCRIPT` for no shell,
  `bash --noprofile --norc -eo pipefail -c SCRIPT` for `bash`, `sh -e -c SCRIPT` for
  `sh` (GitHub's shells); `cwd` is the checkout joined with the working directory; `env`
  is the plan `env` with the step's environment. The step name is its `name`, else the
  first line of its script (at most 80 characters).
- Expressions are filled in: `matrix.KEY` with the entry's value, `runner.os` with
  `Linux`, `macOS` or `Windows` (this machine), `runner.temp` with `RUNNER_TEMP`,
  `github.workspace` with the checkout, `env.NAME` with that value.
- `command` is one `bash -c` text for the suite queue: it makes the temp folder, then
  runs each step in order in its folder with its environment, prints
  `pdd-ci-local: step N of M: NAME` before it, and at the first failure prints
  `pdd-ci-local: step N failed with exit CODE` and exits with that code. After the last
  step it prints `pdd-ci-local: all M steps passed`. Every value is in single quotes.

`localJobResult(entry, run)` reads one finished run (`run` is `{exit: {code, signal},
log}` or `null`) into `{key, workflow, job, check, head, state, step, exit, tool, why,
tail}`:

| Run | `state` |
|---|---|
| exit code 0 | `pass` |
| exit code 127 (also at the failed step): a missing tool | `could-not-run`; `tool` from the last `TOOL: command not found` or `TOOL: not found` line; why "TOOL is missing on this machine" |
| no run, or no exit code (a signal) | `could-not-run`; why "the local run did not finish" (with the signal) |
| any other exit code | `fail`; `step` is the failed step's name, `exit` the code, `tail` the last 15 lines of the log, redacted ([secret redaction](secret-redaction.prompt.md)), each at most 300 characters |

Fields that do not apply are `null`. `localJobsRecord({head, plan, runs, at})` is
`{head, at, jobs}`: the result of each plan entry from `runs[KEY]`.

`localJobReds(record)` gives one red line for the repair for each `fail`: `CI job CHECK
failed when Autopilot ran it on this machine for head SHA7 (CI did not start): step
"STEP" exited with CODE.` and, with a tail, a line break, `Last lines:` and the tail. A
`could-not-run` job is no red: it counts as CI-only.

## The CI lines of the merge note

`ciMergeNote({jobs, record, notStarted})` gives the CI lines of the merge note when CI
did not start. `notStarted` is the core's `ci.notStarted`: the reason is `GitHub said
"MESSAGE"` for `billing`, `queued since HH:MM UTC` for `queued`, else `reason unknown`.

1. `- CI: did not start (REASON); covered by the local full suite: CHECKS`: the checks of
   the covered entries and of the local entries with `suite`, in order. With none:
   `- CI: did not start (REASON)`.
2. Then one line for each local or CI-only entry, in order. A local entry: `- CI job
   CHECK: local pass`, `- CI job CHECK: local fail (step "STEP", exit CODE)`, or `- CI job
   CHECK: not run yet (CI did not start; WHY)` for `could-not-run` or a missing result (WHY
   "no local result"). A CI-only entry: `- CI job CHECKS: not run yet (CI did not start)`
   (its `checks` joined with `, `, or its `check`); a file entry: `- CI workflow FILE: not
   run yet (CI did not start)`.

## Missed CI on the base

`missedCiJobs({jobs, record})` lists what did not run before the merge: each CI-only
entry, and each local entry whose result is `could-not-run` or missing, as
`{workflow, job, checks, dispatch}`. An entry with no workflow file (`workflow: null`) or
with no check name (an unreadable file) is left out: Autopilot cannot find its run again.

`recordMissedCi({root, merge, pr, issue, missed}, {fs, now})` appends one line to the
machine file `ROOT/ci-missed.jsonl` (mode 0600): `{merge, pr, issue, at, jobs}`, each
job with `state: "missed"`. An empty `missed` writes nothing and returns `null`; else it
returns the record. `readMissedCi({root}, {fs})` returns the valid records (a record has a
40-hex `merge` and a non-empty `jobs` list), oldest first.

`checkMissedCi({root, repo, base, tip, ciDown}, {gh, fs, now, billing})` runs when the
core sees that CI works again. With `ciDown` set it makes no call and does not write the
file: the saved states decide (a red job stays red, the others wait). `gh.call(method, endpoint, body)` returns `{status, value}`;
`billing(checkRun)` (the core's billing reader) returns the billing message or `null`
(default: always `null`). For each job of each record that has not passed:

1. **A red job** stays red until the check names pass at the current base tip `tip`:
   then it passes.
2. **The state of a name.** The check runs of a commit are read once per call: `GET
   repos/REPO/commits/SHA/check-runs?per_page=100`. The run with that name and the
   highest id decides: completed with `success`, `neutral` or `skipped` is a pass;
   completed with another conclusion is red, unless `billing` gives a message (GitHub did
   not run it); not completed is running; no run is missing. The merge commit decides when
   it gives a pass or red. Else the current base tip decides when it gives a pass, red or
   running: a later commit holds the merged change, so a rerun, a dispatch, a person's own
   run or a later push counts there.
3. Any red name: the job is red (`red: {names, sha, at}`, `sha` where it failed). Every
   name passed: the job passed. Any name running, or a stuck job: wait (a stuck job is
   read again, never asked again).
4. Else (missing, or not run by GitHub), ask once:
   - The newest workflow run of the job's file at the merge commit (`GET
     repos/REPO/actions/runs?head_sha=MERGE&per_page=50`, `path` is
     `.github/workflows/FILE`): when it is completed, `POST
     repos/REPO/actions/runs/ID/rerun`; when it is not completed, wait (no ask).
   - No such run: when the workflow has `workflow_dispatch`, `POST
     repos/REPO/actions/workflows/FILE/dispatches` with `{ref: BASE}` (it runs at the base
     tip). Else the job is stuck.
   - The job saves `asked: {how, sha, at, status}` (`how` is `rerun` or `dispatch`) and the
     file is saved at once, so a later error does not ask twice. An ask with a status of
     300 or more makes the job stuck.
5. An asked job that has no result 6 hours after the ask is stuck.

A read that does not return status 200 throws an `Error` with `code: "github"`; the file
keeps what was saved before. At the end the file is written again (a temp file, then a
rename): passed jobs go, a record with no job left goes, a record older than 14 days goes
unless it has a red job, and at most 50 records stay (the newest).

The result is `{state, red, waiting, stuck, lines}`:

- `red`: `[{merge, pr, issue, workflow, names, sha}]`. The caller files the deduplicated
  main-red issue ([base-red owner](autopilot-base-red.prompt.md) `fileMainRed`, `what:
  "ci"`) and holds new merges while it is not empty.
- `waiting` and `stuck`: `[{merge, pr, issue, workflow, checks}]`.
- `state`: `red` with a red job, else `waiting` while records stay, else `clear`.
- `lines`: one status line for each waiting or stuck job:
  `missed CI: CI job CHECKS for PR #N (MERGE7) waits to run on BASE` and
  `missed CI: CI job CHECKS for PR #N (MERGE7) did not run on BASE, and Autopilot cannot
  start it: run the workflow FILE by hand`.

`missedCiHeldLine(red, base, issue)` is the status line of a red job:
`merges held: CI job NAMES failed on BASE after a merge without CI (issue #N)`, or with
`(MERGE7)` when there is no issue number.

## Public contract

Exports: `parseWorkflowYaml`, `sortCiJobs`, `ciJobsSummary`, `readCiJobs`,
`cachedCiSummary`, `localJobPlan`, `localJobResult`, `localJobsRecord`, `localJobReds`,
`ciMergeNote`, `missedCiJobs`, `recordMissedCi`, `readMissedCi`, `checkMissedCi` and
`missedCiHeldLine`.

Ports: `git(args)` (trimmed stdout; throws on failure), `fs` (`node:fs` by default),
`now()` (`Date.now` by default), `gh.call(method, endpoint, body)` and `billing(checkRun)`.
No function here starts a process or reads the network except through these ports.

## Dependencies

- [Autopilot core](autopilot-core.prompt.md): required for `workflowTriggers` and
  `workflowRunsOnPr` (the `on:` reader and the rule of which workflows run on a PR).
- [Secret redaction](secret-redaction.prompt.md): required for the log tails.

The link to the base-red owner above is navigation only: the caller files the main-red
issue.
