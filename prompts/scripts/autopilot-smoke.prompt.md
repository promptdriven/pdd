# Disposable Autopilot release smoke repo

Own `scripts/autopilot-smoke.mjs` and the thin `scripts/autopilot-smoke.sh`
entrypoint. This is a source-checkout team tool, not a public pdd command or a
core engine policy. Create one fresh private GitHub sandbox from vendored files
and read its results without touching any Autopilot installation or starting an
agent. The authorized builder brief supplies the new behavior; no existing CLI
behavior changes. Do not record approvals, delete repos, run paid checks, or
change the shared core. Export `readSmokeResults` as the small optional hook for
future callers; do not wire it into core now.

## Commands and effects

- `scripts/autopilot-smoke.sh --owner OWNER [--apply]`: dry run by default.
  Generate `OWNER/autopilot-smoke-<UTC timestamp>-<random id>` anew each time;
  there is no reuse or user-chosen repository name. Owner is one GitHub login
  containing ASCII alphanumerics and internal hyphens, at most 39 characters.
  Validate arguments and all fixtures before effects. Dry run prints the planned
  repo, private visibility, ordered issue titles and `pdd:autopilot` label, check
  command and manual delete command. It calls neither gh nor git and creates no
  files. `--help` prints usage. Invalid flags, missing owner or mixed check/create
  options exit 1 with a concise diagnostic.
- Apply stages the exact base bytes in a new temporary directory, initializes
  and commits main locally with a fixed synthetic author and no commit hooks,
  then uses `gh repo create --private --source ... --push`. Never clone or mutate
  an existing remote. Native subprocesses discard inherited `GIT_*` variables
  so a caller's repository/index/author overrides cannot redirect sandbox work.
  Disable init templates and configure the staged repo's hooks path to `/dev/null`
  for both commit and push. Print repo identity and manual cleanup command before the
  remote mutation, so a partial failure is recoverable. Create the opt-in label
  then the fixed issues in filename order with that label and their identity
  markers. Print each returned issue URL as soon as created. Any failed command
  stops with nonzero exit, keeps prior remote effects, performs no retry or
  deletion, and always removes local temporary files. Do not echo subprocess
  stdout/stderr on failure, which may include credentials. No setup, start,
  timer, approval, default home state or live-service operations are permitted.
- `scripts/autopilot-smoke.sh --check OWNER/REPO` only reads GitHub. Repo owner
  follows the owner rule; name contains ASCII alphanumerics, `.`, `_`, `-`, is
  1–100 characters and is neither `.` nor `..`. Read all issue/comment pages via
  `gh api --method GET --paginate --slurp`. Select smoke identity markers rather
  than current labels, because labels may change. Require exactly one issue for
  every fixture id; missing/duplicate smoke issues are an error, not success.
  Read merged PRs using `gh pr list --state merged --limit 1000` with
  `number,url,mergedAt,closingIssuesReferences`. Refuse a saturated 1000-row
  response instead of silently claiming completeness. Match closing references
  by full issue URL, not just number (cross-repo references must not match).

## Result meaning and interfaces

`loadSmokeFixture({root}, ports)` synchronously returns `{baseDir, files, issues}`.
Default root is `fixtures/autopilot-smoke` relative to this checkout. Files are
lexically ordered recursive `{path, content}` entries with UTF-8 text bytes;
`baseDir` is the absolute base directory. Refuse symlinks/special files, empty
base, missing package manifest or missing test script. Issues are 3–5 sorted
Markdown files with safe `NN-slug.md` names, a nonempty first-line `# TITLE`
and nonempty body. Each issue is `{id, title, body}`, id is filename minus `.md`,
body ends in `<!-- pdd:autopilot-smoke:ID -->`. Reject preexisting identity
markers to avoid ambiguous identity.

`readSmokeResults({repo, fixture}, ports)` returns
`{repo, checkedAt, issues}`; fixture is the loader result and defaults to loading
the vendored fixture. `checkedAt` is ISO UTC. Issues stay in fixture order, each
with exactly `{id, number, title, url, state, createdAt, finishedAt, elapsedSeconds}`.
Times are ISO UTC strings, `finishedAt` is null for open work, elapsedSeconds is
nonnegative whole seconds from creation to finish or check time. Invalid dates
or malformed remote rows fail the read. Terminal precedence is:

1. A closed issue with a linked merged PR is `merged`, at the latest linked
   `mergedAt` (all merged closing PRs, not a merely mentioned PR).
2. Otherwise an exact own-issue `<!-- pdd:autopilot-core:end:NUMBER:RUN -->`
   comment makes it `ended` at the latest such comment's creation time; a closed
   issue without such a comment is `ended` at its `closed_at`.
3. Otherwise `open`, even with a linked PR. Unmerged PRs never prove success.

Ended describes recorded terminal evidence, not current retry liveness. Missing
or failed gh output never counts as a pass. Print one line per issue with state,
created/finished times, elapsed seconds and URL; print checkedAt and manual delete
command. `runSmoke(argv, ports)` returns `{exitCode, message}` for usage/error,
streams successful progress through `ports.log`, and catches errors. Normal
completion exits 0 even when issues are open/ended: this command reports, it does
not act as a release approval.

Ports are synchronous: `fs` (Node fs shape including temp/copy operations),
`run(program,args,{cwd,input})` returns `{code,stdout,stderr}` without shell
interpolation, `now()` milliseconds, `id()` safe random lowercase hex, `log(line)`.
Native defaults bind filesystem, spawnSync, Date.now, randomUUID and stdout only
at the script boundary. Tests inject outside operations. No product or team
account names are embedded in sandbox behavior.

## Dependencies

- [Base helper contract](../../fixtures/autopilot-smoke/base/prompts/helpers.prompt.md):
  required fixture behavior and deliberate uncovered bug; load for fixture authoring.
- [Core](../cli/autopilot-core.prompt.md): navigation only; the reader consumes
  its emitted end marker as explicitly specified here, without importing core.
- Node filesystem, path, URL, crypto, process and child_process builtins; native
  apply needs git and authenticated gh. Checks need gh only; dry run needs Node.

<details><summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[{"operation":"runSmoke","input_schema":{"type":"object","properties":{"argv":{"type":"array","items":{"type":"string"}}},"required":["argv"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"exitCode":{"type":"integer"},"message":{"type":"string"}},"required":["exitCode","message"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":5,"max_model_calls":0},"conventions":["Partial interface covers usage and argument rejection only; native fake-process tests cover external creation and reading."]}
```

</details>
