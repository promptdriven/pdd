# Local issue cost ledger

Own `src/cost-ledger.mjs`. Record measured resource use for normal and automatic
workflow attempts. Preserve workflow decisions and command results when measurement
fails. Never read credentials, message content, tool arguments or agent output into
the ledger. Agent account identity is a hash of agent kind and the saved config
folder; it is a local profile identity, not a claim about the billing login.

## Capture and public data

`captureCosts(before, run, ports={})` returns the cumulative `run.cost` record.
Run storage calls it inside its local ownership boundary before publication.
`ports.fs`, `ports.sessionFs`, `ports.env`, and `ports.now` replace native file,
session file, environment and millisecond clock facilities. `ports.skipCostSessions` retains token checkpoints with `session-capture-deferred` coverage, so workflow health status keeps its existing single-tail read budget; explicit cost status refreshes tokens. The result has
`schema: "pdd.cost.v1"`, `capturedAt`, `outcomeAt` (milliseconds), `outcome`
(`running`, `merged`, `reverted`, `stuck`, `closed`, `parked`), `tokens` (rows of
`account`, `agent`, `input`, `cachedInput`, `output`, `reasoningOutput`, `total`),
`sessions` (private numeric checkpoints), `person` (`questions`, `answers`,
`approvals`, `waitingMinutes`, `activeMinutes`), `suiteMinutes`, `ciMinutes`,
`githubCalls`, `events`, `measurements`, `coverage`, optional `explicitOutcome` (the last explicit outcome), and `waits` (private identity
and timestamps). Unknown suite, CI and active person minutes are null, not zero.
Cached input and reasoning output are subsets of input and output; do not add them
to total. Token rows are sorted by account. A run with no captured ledger has `not-captured` coverage and an outcome derived from saved state; do not invent historical usage. Coverage is a list of finite codes.
Events have `at`, `metric`, `value`, and optional `account` and `agent`; metric is
`input`, `cachedInput`, `output`, `reasoningOutput`, `total`, `suiteMinutes`,
`ciMinutes`, `githubCalls`, `questions`, `answers`, `approvals`, `waitingMinutes`,
or `activeMinutes`. Zero measurements also create events so measured zero differs from unknown. Keep no message text, paths or environment values in cost data.

Read every saved current chat, abandoned chat and replacement-original or replacement session once by kind/config/id, including custody from before and after the current mutation. Use each chat's saved agent, config directory and session id. Moving a chat into abandoned custody or replacing the replacement envelope must preserve its deduplication identity and forward-read checkpoint, so bounded transcript backlogs can finish on later captures.
Deduplicate resumed sessions. Resolve only the saved valid UUID, in the saved
config directory (else the environment default). Codex searches the date folders
within 31 days, as chat health does; consume the newest cumulative `token_count`
`info.total_token_usage`, never sum repeated cumulative counts. Claude sums
assistant `message.usage`, deduplicating streaming rows by message id (or uuid),
including cache creation and cache read input. Ignore user/meta/error rows and
unrelated session ids. Read at most 256 KiB per session per capture using open,
fstat, positioned read and close. Codex reads the tail. Claude reads forward from
a retained byte offset so large transcripts can catch up over successive captures.
Only complete newline-terminated JSON rows count. Skip corrupt rows. Keep prior
measurements if a file vanishes. Truncation or backlog is visible in coverage.
Missing, unsupported or unreadable sessions are unknown, never free usage.

Capture each question identity and each gate identity when shown. A recorded answer
ends its question wait; an actual approval ends its gate wait. Replacing or clearing
a question without an answer ends waiting without inventing an answer. Count each recorded approval decision. The evidence actor identifies the recording
process, so an agent actor can record a person approval. Do not infer automatic
approval from that actor or invent an unsupported evidence route. Approval counts
are interaction events, not measured active person effort. Sum elapsed waiting
for each request, including open requests up to capture time. Active effort needs
an explicit measurement. Capture outcome from saved workflow state and PR states;
paused is parked, stuck is stuck, cancelled or a closed final PR is closed, and
only a merged final-area PR is merged. Do not guess reversions from Git history.

`applyCostMeasurement(run, input, at)` accepts an object with only `id` (nonempty
string, at most 100 safe alphanumeric/dot/underscore/hyphen characters), optional
nonnegative finite `suiteMinutes`, `personMinutes`, and optional `outcome`
(`merged`, `reverted`, `stuck`, `closed`, `parked`). Require a metric or outcome.
Keep each id once per attempt; equal retries have no effect, conflicting retries
fail. It adds measured minutes and an explicit outcome without changing workflow
state, approval, progress or GitHub. It returns the updated run; invalid input
throws a finite validation error. Explicit outcomes remain until replaced by a
later explicit measurement. Suite measurements are elapsed runner wall time, not
summed parallel test durations. The caller owns truthful measurement.

`recordCostGithub(runDir, entry, ports={})` appends only numeric call identity to
`github-cost.jsonl` in that run directory, mode 0600, folder 0700. It uses the same
best-effort append style as the GitHub call ledger. Capture uses the line count
as a cumulative checkpoint, so GitHub ledger compaction cannot erase issue costs.
Unattributed repository-wide coordinator calls are not allocated to every issue.

## CI closure boundary

`captureClosedCi(run, ports={})` is asynchronous. For each PR observed closed or
merged, atomically reserve `cost-ci-N.json` with exclusive create before any read.
Make at most one `gh api` GET using `ports.execFile`, with no pagination or writes.
Use `repos/O/R/actions/runs?branch=BRANCH&per_page=100` when the PR has a saved
branch, so earlier heads of that PR count too. URL-encode the branch. Without a
branch, use `?head_sha=SHA&per_page=100` from observed `head` (or `headSha`) and
mark coverage incomplete because earlier heads are unknown. Without either, make
no call. Filter by PR number; when GitHub omits pull_requests, match the branch
or the fallback head SHA. Sum elapsed minutes
from `run_started_at` to `updated_at` for completed workflows. An incomplete run,
failed read, malformed response, rerun attempts or truncated page means partial/unknown coverage;
never retry this measurement automatically. Save only `{attempted, minutes,
complete}`. Status reads these files locally; status never fetches CI durations.
An exclusive reservation left by a crash means unknown, not permission to retry.

## Reports

`costReport(runs, now)` returns `{schema:"pdd.cost-report.v1", generatedAt, runs,
day, week}`. Public run rows have `repo`, `issue`, `runId`, `outcome`, `outcomeAt`,
`tokens`, `person`, `suiteMinutes`, `ciMinutes`, `githubCalls`, `coverage` only.
Each window has `since`, `totals` (token rows, person counts/minutes, suiteMinutes,
ciMinutes, githubCalls), `coverage` (union of run coverage), `mergedIssues`, and
`p50`, `p90` (the same totals shape, null for no merged issues). Totals include `totalTokens` (sum across measured accounts, null without token observations); percentiles compute this across issue totals, not by summing account percentiles. Totals use events
observed in `(now-window, now]`, not the entire cost of an old attempt. Unknown
minute values stay null unless at least one measured contribution exists; coverage
identifies partial totals. Percentiles use nearest rank over cumulative issue costs
for issues whose latest outcome is merged in the window; combine attempts of the
same repo/issue once. Do not combine different repositories with equal issue numbers.
`costStatusLines(report)` returns readable day/week totals and P50/P90 per merged
issue for tokens, suite, CI, GitHub calls, person interactions, active and wait
minutes, plus outcome counts, per-account token totals and coverage.


Include native auditor chats in `runDir/audits/*.json` with matching runId in
the same session accounting and deduplication as workflow chats. Auditor chats
carry `root` for their private checkout; resolve Claude's project transcript there
rather than at the worker checkout. A launched audit
without a captured session adds `audit-session-unavailable` coverage. A damaged,
malformed or unreadable audit record also adds that marker before any runId filter.
An unreadable audit folder adds the marker; only ENOENT means no folder. Valid
records for a different attempt may be excluded. Validate schema, runId, PR,
merge/parent identity and chat shape before accepting an audit record. Include
optional ports.auditRecords (shared records already read under repository custody),
filtered by runId, in the same session inventory and deduplication. Read through
the filesystem port. Repeated status reads never count a session twice.

## Dependencies

The [GitHub call counter](github-calls.prompt.md) is a navigation-only consumer
reference; this module does not load it or call it.
- Native Node filesystem, crypto hashing, path joins and deterministic arithmetic
  are injected at the file and clock boundaries above. No AI/model call is needed.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

Only explicit measurement and supplied-data reporting are bound. Native transcript checkpoints, account hashing, session/audit reads, journal durability, CI reservation and actual GitHub accounting remain native. Native evidence owners: test/cost-ledger-repair.test.mjs, test/cost-ledger.test.mjs, test/issue-cost-ledger.vectors.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "f011928cc9944e0b776c087957db6344378db23f94e4cdab12da08d3b53b972b",
  "entries": [
    {
      "operation": "applyCostMeasurement",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "string",
            "description": "JSON text encoding of the saved run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "input": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              },
              "suiteMinutes": {
                "type": "number"
              },
              "personMinutes": {
                "type": "number"
              },
              "outcome": {
                "type": "string",
                "enum": [
                  "merged",
                  "reverted",
                  "stuck",
                  "closed",
                  "parked"
                ]
              }
            },
            "required": [
              "id"
            ],
            "additionalProperties": false
          },
          "at": {
            "type": "number"
          }
        },
        "required": [
          "run",
          "input",
          "at"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the updated run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": []
    },
    {
      "operation": "costReport",
      "input_schema": {
        "type": "object",
        "properties": {
          "runs": {
            "type": "string",
            "description": "JSON text encoding of the saved runs. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "now": {
            "type": "number"
          }
        },
        "required": [
          "runs",
          "now"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the pdd.cost-report.v1 report. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "costStatusLines",
      "input_schema": {
        "type": "object",
        "properties": {
          "report": {
            "type": "string",
            "description": "JSON text encoding of the cost report. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "report"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "lines": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "lines"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 64,
    "max_model_calls": 16
  },
  "conventions": [],
  "kind": "partial"
}
```
</details>
