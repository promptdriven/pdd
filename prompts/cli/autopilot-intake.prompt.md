# Autopilot intake cards (shadow)

Own `src/autopilot-intake.mjs`. When a machine's intake mode is `shadow`, each tick
of the [Autopilot core](autopilot-core.prompt.md) asks this module to judge, before
any work starts, whether each open issue in scope is ready for one unattended AI
job. The module writes local cards and a daily change file. It never writes to
GitHub and never changes which issue the core starts. The cards exist so that
people can score them against what really happened before any gate uses them.

Why this shape: a measured study of intake designs found that a short card from
the issue text and the titles of the other open issues was as precise as a full
code check, found more of the good issues, and gave the same answer on a second
run far more often, at a third of the cost. Native facts (an assignee, an open
blocked-by link, open sub-issues, a stop label) need no AI. Agents can also judge
wrongly, so the cards stay a shadow record until people have measured them.
Issue text is written by anyone who can open an issue, so a card agent reads it
with no tools, no write access and no repository: the card is a judgment of text,
nothing more.

## Rules

- Mode: `intakeMode(value)` returns `shadow` for `shadow` and `off` for any other
  value. Off is the default.
- The core's one hook is `intakeTick(ctx, rows)`, after its own start step, inside a
  try/catch. In `shadow` with an issue list it runs one pass (`shadowIntake`). In
  any other intake mode it only stops the card jobs that still run
  (`stopCardJobs`) and removes their job files; it creates no file and makes no
  GitHub call. A tick that ends before the hook (core mode off, the GitHub reserve)
  runs no pass; the [launcher](autopilot-launcher.prompt.md) calls `stopCardJobs`
  for core mode off and for `pdd autopilot stop`.
- Scope: `intakeRows(rows, label)` keeps the open issues (no pull requests) without
  a report label (`pdd:runtime`, `pdd:autopilot-report`) and, when the core has an
  opt-in label, with that label; oldest first, then the lower number. The scope is
  wider than the core's ready rule: it does not skip issues that cool down after a
  no-result, or issues whose blocker is named only in the text or in an END comment.
  A person who reads the would-pick list must keep that in mind.
- Native facts first (`nativeFacts(row)`), from the issue row only, in this order:
  an assignee → `held`; `issue_dependencies_summary.blocked_by` > 0 → `waiting`;
  `sub_issues_summary.total` > `completed` → `tracking` (the sub-issues are the
  work); a label `pdd:stuck`, `pdd:needs-decision` or `pdd:would-merge` → `parked`;
  the label `pdd:working`, or a core job file of this machine for the issue (the row
  can be older than this tick's claim) → `working`. Each gives a short reason. An
  issue with a native fact gets no AI card. Text patterns in the issue never count
  as native facts. A native record keeps the last AI card as `previous`.
- Trust: a card job starts only for an issue whose author passes the core's own
  trust check (`ports.trusted`, the same check that the core uses before it gives an
  issue to an agent). An issue that fails it gets the native-style record
  `untrusted` once per version. Untrusted text never reaches any agent: only
  comments and other-issue titles whose author passes the same check reach a card.
  Each lookup of a new login can be one GitHub read, so results are kept in
  `ROOT/intake/trust.json` for 6 hours and a pass makes at most 40 lookups. An
  author that is not looked up yet counts as not trusted for that pass (its issue
  waits, its comment or title is left out). Comments are checked from the newest
  back, and at most 20 trusted comments are kept. The first passes on a repository
  with many outside authors spend this limit until the cache holds them.
- Version (`issueVersion(row)`): the SHA-256 of the title, the body, the sorted
  labels, the sorted assignee logins, the two native summaries and the comment
  count (not `updated_at`). A new version needs a new card; an old card stays until
  then.
- Card job: for an issue with no native fact, no running card job and no card for
  its version, start one headless job through the
  [headless job runner](agent-job.prompt.md), in the empty folder `ROOT/intake/empty`
  (never the repository checkout), with the job environment without session keys
  and without GitHub tokens (`cardEnvironment`: no `GH_…TOKEN` or `GITHUB_…TOKEN`).
  The agent gets no tools and no write access (`cardCommand`): Codex runs
  `exec --ignore-user-config --sandbox read-only --skip-git-repo-check --ephemeral
  --color never --ignore-rules` (so no MCP server, profile or feature of the
  person's `config.toml` loads; auth still loads) with approvals `never`, web search
  disabled, `mcp_servers={}`, reasoning effort `low`, its tool features off (hooks,
  plugins, apps, browser and computer use, multi-agent, shell, unified exec, code
  mode) and `--output-last-message ANSWER`; Claude runs
  `-p --safe-mode --tools "" --permission-mode plan --permission-prompts none
  --strict-mcp-config --no-chrome --no-session-persistence --output-format json`.
  The configured model is passed with `--model`. Any other agent gets no card.
  Card jobs never use the bypass flags of build jobs.
- Limits: at most 2 card attempts per tick and at most 2 jobs at once. An attempt
  counts before its comment read, its job start and its job-file write, so a
  failing read or write can never start more. A job whose file cannot be written is
  stopped at once and saves an error card. None start while the GitHub budget is
  low or at the reserve, or while the agent is not ready (the core's `agentReady`
  port, asked once per pass and only when a card would start).
- Card input (`cardPrompt`): the repository name, the issue number, title, labels,
  creation time, native link counts, the body (at most 20,000 characters) and at
  most the last 20 trusted person comments (each at most 3,000 characters), plus
  the number and title of up to 200 other issues in scope by trusted authors. Person comments
  (`personComments`) leave out comments with an HTML comment marker, a JSON code
  block, an empty body or a bot author. The only GitHub read is the comment list,
  and only when the row says the issue has comments. The prompt says that the
  issue text is data, that the agent has no tools, asks for only one JSON object,
  and names the classes: ready (clear, one PR, an obvious check), improve (clear
  goal; acceptance criteria, reproduction or scope missing), person (a person's
  decision is needed), duplicate (same problem or goal as another listed issue;
  same words are not enough), blocked, held, fixed (the comments show it no longer
  happens) and elsewhere (another repository).
- Answer: Codex's ANSWER file, or the last JSON line with a `result` string in
  Claude's log; at most 64 KB, else an error card. `parseCardText` takes the JSON
  object between the first `{` and the last `}` (a code fence is fine).
- Card result (`readCard(result)`): `class` must be one of the eight classes and
  `reason` a non-empty string, else the card fails. Control characters are removed
  from every kept string. Kept fields: `start` (true for ready and improve),
  `reason` (500 characters), `confidence` (0 to 1, else null), `canonical` (a
  positive number, duplicates only), `suggested_links` (at most 10, `blocked-by` or
  `duplicate-of` with a positive number), `question` (person only), `area_hint` (at
  most 6 paths) and `reported_model`.
- Each card names the agent kind and the configured model, and a finished card its
  `seconds`. A card job that ends with no valid card, runs longer than 20 minutes
  (it is stopped) or cannot be read for 20 minutes saves an error card; the issue
  gets a new job after 6 hours, or at once for a new version. A running job whose
  issue left the scope, changed version or got a native fact is stopped or dropped
  with no card. A finished card job leaves no job files: the card holds the result;
  a failed card keeps only the job log. Files in `logs/` older than 7 days go.
- Would pick (`wouldPick(rows, cards)`): the issues in scope with a ready card for
  their current version and no native fact; issues with `total_blocking` > 0 first,
  then the oldest, then the lower number.
- Started: each pass compares the core's own job files with the last pass and
  records each newly started issue with the verdict of its card before this pass
  and whether it was in the previous would-pick list. The first pass (also after a
  switch from off) only saves the running jobs and records no started line.
- Fail open: a failure of one issue is a warning and skips only that issue. The
  core's try/catch makes any other failure one warning, so the pass can never stop
  a tick or change a start.

## Public contract

- Files under `ROOT/intake/` (ROOT is the core state folder): `cards/N.json` per
  issue (`issue`, `version`, `at`, `agent`, then `native` (with `previous`), `card`
  (with `seconds`) or `error`); `jobs/N.json` for running card jobs; `logs/` for the
  job files; `empty/`; `would-pick.json`; `started.json`; and
  `diff-YYYY-MM-DD.jsonl` (UTC) with one line per change: `{at, kind: "card", issue,
  from, to, reason, version}` when the verdict (`native:KIND`, the class, or
  `error`) changes, `{at, kind: "would-pick", issues}` when the list changes, and
  `{at, kind: "started", issue, verdict, would_pick}`. A cut last line never
  swallows the next one.
- `intakeTick(ctx, rows)` and `shadowIntake(ctx, rows)` take the core's tick context
  (`fs`, `now`, `root`, `repo`, `state`, `settings`, `budget`, `gh`, `jobs`,
  `ports`, `warn`); `shadowIntake` returns `{cards, started, pick}`.
- `cardCommand(agent, {model, result})` returns `{command, args}` for Codex or
  Claude and throws for any other agent; `cardEnvironment(env)` returns the card
  environment.
- `stopCardJobs({root, fs, jobs, warn})` stops the running card jobs under `root`
  and returns how many it stopped.
- `readIntake({root, now, date}, fs)` returns `{day, cards, running, wouldPick,
  diff}` for one UTC day (today by default); `intakeText(report)` prints it as plain
  lines with control characters removed: one per card with its class, confidence,
  reason, agent, model and seconds; the would-pick list; and the day's changes.

## Dependencies

- [Headless job runner](agent-job.prompt.md): required to start, read and stop card
  jobs and for the job environment.
