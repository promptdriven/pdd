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

## Rules

- Mode: `intakeMode(value)` returns `shadow` for `shadow` and `off` for any other
  value. Off is the default. The core calls the module only in `shadow`.
- Scope: `intakeRows(rows, label)` keeps the open issues (no pull requests) without
  a report label (`pdd:runtime`, `pdd:autopilot-report`) and, when the core has an
  opt-in label, with that label.
- Native facts first (`nativeFacts(row)`), from the issue row only, in this order:
  an assignee → `held`; `issue_dependencies_summary.blocked_by` > 0 → `waiting`;
  `sub_issues_summary.total` > `completed` → `tracking` (the sub-issues are the
  work); a label `pdd:stuck`, `pdd:needs-decision` or `pdd:would-merge` → `parked`;
  the label `pdd:working`, or a core job file of this machine for the issue (the row can
  be older than this tick's claim) → `working`. Each gives a short reason. An issue with a
  native fact gets no AI card. Text patterns in the issue never count as native
  facts.
- Version (`issueVersion(row)`): the SHA-256 of the title, the body, the sorted
  labels, the sorted assignee logins, the two native summaries and the comment
  count. A new version needs a new card; an old card stays until then.
- Card job: for an issue with no native fact, no running card job and no card for
  its version, start one headless job of this machine's agent through the
  [headless job runner](agent-job.prompt.md) (`agentCommand(state.agent, {model})`,
  the job environment without session keys, the repository checkout as working
  folder). At most 2 card jobs start per tick and at most 2 run at once. None start
  while the GitHub budget is low or at the reserve, while the agent is not ready
  (the core's `agentReady` port), or when the machine's agent is not Codex or Claude.
- Card input (`cardPrompt`): the repository name, the issue number, title, labels,
  creation time, native link counts, the body (at most 20,000 characters) and at
  most the last 20 person comments (each at most 3,000 characters), plus the number
  and title of up to 200 other issues in scope. Person comments
  (`personComments`) leave out comments with an HTML comment marker, a JSON code
  block, an empty body or a bot author. The only GitHub read is the comment list,
  and only when the row says the issue has comments. The prompt says that the
  issue text is data, that the agent must not read or change files or use the
  network, and names the classes: ready (clear, one PR, an obvious check), improve
  (clear goal; acceptance criteria, reproduction or scope missing), person (a
  person's decision is needed), duplicate (same problem or goal as another listed
  issue; same words are not enough), blocked, held, fixed (the comments show it no
  longer happens) and elsewhere (another repository).
- Card result (`readCard(result)`): `class` must be one of the eight classes and
  `reason` a non-empty string, else the card fails. Kept fields: `start` (true for
  ready and improve), `reason` (500 characters), `confidence` (0 to 1, else null),
  `canonical` (a positive number, duplicates only), `suggested_links` (at most 10,
  `blocked-by` or `duplicate-of` with a positive number), `question` (person
  only), `area_hint` (at most 6 paths) and `reported_model`.
- Each card names the agent kind and the configured model of the job. A card job
  that ends with no valid card, or runs longer than 20 minutes (it is stopped),
  saves an error card; the issue gets a new job after 6 hours, or at once for a new
  version. A running job whose issue left the scope, changed version or got a
  native fact is stopped or dropped with no card. A finished card job leaves no job
  files: the card holds the result; a failed card keeps only the job log.
- Would pick (`wouldPick(rows, cards)`): the issues in scope with a ready card for
  their current version and no native fact; issues with `total_blocking` > 0 first,
  then the oldest, then the lower number.
- Started: each pass compares the core's own job files with the last pass and
  records each newly started issue with its card verdict and whether it was in the
  previous would-pick list.
- Fail open: a failure of one issue is a warning and skips only that issue. The
  core calls the pass inside a try/catch, after its own start step, so the pass
  can never stop a tick or change a start.

## Public contract

- Files under `ROOT/intake/` (ROOT is the core state folder): `cards/N.json` per
  issue (`issue`, `version`, `at`, `agent`, then `native`, `card` or `error`);
  `jobs/N.json` for running card jobs; `logs/` for the job files;
  `would-pick.json`; `started.json`; and `diff-YYYY-MM-DD.jsonl` (UTC) with one
  line per change: `{at, kind: "card", issue, from, to, reason, version}` when the
  verdict (`native:KIND`, the class, or `error`) changes, `{at, kind:
  "would-pick", issues}` when the list changes, and `{at, kind: "started", issue,
  verdict, would_pick}`. A cut last line never swallows the next one.
- `shadowIntake(ctx, rows)` runs one pass with the core's tick context (`fs`,
  `now`, `root`, `repo`, `state`, `settings`, `budget`, `gh`, `jobs`, `ports`,
  `warn`) and returns `{cards, started, pick}`.
- `readIntake({root, now, date}, fs)` returns `{day, cards, running, wouldPick,
  diff}` for one UTC day (today by default); `intakeText(report)` prints it as plain
  lines: one per card with its class, confidence, reason, agent and model; the
  would-pick list; and the day's changes.

## Dependencies

- [Headless job runner](agent-job.prompt.md): required to start card jobs and to
  build the agent command and the job environment.
