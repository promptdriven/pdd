# Offline Autopilot comparison

Own `scripts/autopilot-compare.mjs` and the optional `environment` input of the
existing GitHub test world. That input overlays the world's environment before
local Git setup and is passed to its Git subprocesses. Omitted input preserves
existing helper behavior. Failed helper construction also cleans its directory.
Issue #3063 authorizes a development
harness and a comparison plan. Preserve production Autopilot behavior, approval
rules, existing tests and merge gates. This harness supplies local evidence only.
It never approves a prompt or decides that autopilot-next may merge.

Run two selected local source trees through their actual launcher and tick
exports. Give each an isolated repository, HOME, state, fake clock, fake GitHub,
fake Herdr and fake timer. Clear inherited environment values in the harness;
retain only the local executable search path and the world's isolated HOME.
Only local Git commands may execute. Reuse the
repository's counting GitHub world. Never run an agent, timer service, real gh,
network request or interpreter. Always remove each temporary world, including on
failure. Do not read credentials or operational state. Source trees are trusted
local code, not a security sandbox for arbitrary programs.

Input is a replay object with `schema_version: "pdd.autopilot-compare.v1"`,
`synthetic` (Boolean), and a nonempty `frames` array. Each frame has a unique
`name`, increasing epoch-millisecond `at`, and `snapshot`. Use the native saved
GitHub snapshot shape: `v: 1`, `repository`, `refreshedAt`,
`list: {rows, since, readAt}`, `issues` and `invalid`. Rows use GitHub REST issue
fields; per-issue entries use `version`, `observedAt`, `kinds` and optional `raw`.
Require all four saved page kinds for every row; partial snapshots are rejected
rather than filled with invented empty pages. Comment counts, native summary
counts and both directions of native links must agree. Reject duplicate page
identities. This checks internal consistency, not the truth of a real capture.
The current repo fake counts full linked pages in all four native summary fields.
Accept only that convention. A recording with different active and total counts
needs a fake adapter first; do not claim closed-blocker coverage for that case.
The replay adapter serves the list rows and the saved complete `comments`,
`blockedBy`, `blocking` and `timeline` pages through the fake. Closed referenced
issues come from `issues[N].raw`. Reject malformed identity, unsupported page
kinds, incomplete references, nonfinite clocks, duplicate frames and decreasing
time before loading either source. The fixture contains synthetic data only.
Never commit operational snapshots or tokens. External input must already be
sanitized. Do not print its bodies.

Each frame replaces the fake's external observations, preserving writes to
untouched rows across frames. Apply only rows whose recorded observation changed;
removed open rows disappear. Feed identical serialized observations to both
versions. Do not force either version's internal cache to the other's format.
The first frame initializes the fake launcher; later frames call real ticks.
Include setup calls in that first frame. Record dependency-review subjects and
offered issue numbers/time-rule kinds from real delivered packets, plus current
eligible issues, whether a delivered dependency review lacks a synthetic completion,
the numeric retry time
(null when absent), whether PR observations are unknown, and tick return status
(`started` or `tick-returned`). Each dependency delivery is `{kind:
"dependency-review", issues}` with sorted issue numbers. Each work delivery is
`{kind: "work", issues, timeRules}`: issues keep `number`, `eligible`, `claimed`
and `expiredClaim` Booleans from the packet; time rules keep `kind` and `number`,
sorted by number then kind. The native
public tick has no structured reconciliation outcome; a successful return alone
does not prove progress. Compare these structured decisions, not English
messages. An optional `completeIndependent: true` is permitted only for synthetic
replays with no native dependency edges. It uses the existing deterministic fake
review answer and drains at most 20 requests per frame. Otherwise leave AI work
pending. A missing export, failed launcher, malformed packet, failed completion
or exhausted drain is an error, never a successful comparison.

Export `compareAutopilot({oldRoot, newRoot, replay})` and `comparisonTable(report)`.
The result has `schema_version`, `synthetic`, `inputSha256` (the exact shared JSON
input), `selfComparison`, `old`, `new`, and `comparison`. Each side has `root`,
`version` (package version), `frames` and `totals`. A frame has `name`, `at`,
`outcome`, `decisions` (`delivered`, `eligible`, `pendingReview`, `retryAt`,
`reviewQueueUnknown`), `calls`, `writes` and `metrics`. Calls contain `api`,
`method`, `endpoint`, `status`, `conditional`, and for GraphQL `mutation`.
Writes include all non-GET/HEAD REST attempts and GraphQL mutations; a GraphQL
query sent by POST is not a write. Calls compare ordered routes and statuses.
Writes also carry `payloadSha256`, a SHA-256 of the canonical JSON request body.
For reviewer lease content only, decode base64 JSON and normalize this world's
random coordinator ID, generation IDs (by first occurrence), and subsequent
lease-blob SHAs (by first occurrence). Preserve all other values, including head
SHAs, labels, comments, timestamps, permissions and evidence. Never print payloads.
Different bodies at the same route must compare unequal. Metrics and summed totals have `restCalls`,
`restWrites`, `graphqlCalls`, `graphqlWrites`, `writes`, and `deliveries` (fake
Herdr prompt submissions). `comparison` has one row per frame with `name`,
`decisionsEqual`, `callsEqual`, `writesEqual`, and `restDelta`, `writeDelta`,
`deliveryDelta` (new minus old). Different calls or decisions are findings, not
automatic failures or permission to merge. Unknown real-world safety and cost
remain unmeasured, never zero or green. Self comparison is explicitly labeled.

CLI: `node scripts/autopilot-compare.mjs --old ROOT --new ROOT`
with optional `--replay FILE` and `--json`; `--help` prints usage. Roots default
to no value: both are required. With no replay, load the committed synthetic
fixture. Reject unknown, missing or repeated options with exit 2. Print a Markdown
table by default or the report JSON; exit 0 on completed replay, 1 on execution
or data failure. Write errors to stderr. Every nonempty stream ends in a newline.
The table shows source roots/versions, shared input hash, per-side counts,
per-frame equal/different decisions and traces, and unmeasured live metrics.

## Dependencies

- [Launcher](autopilot-launcher.prompt.md): actual selected version's launcher
  and tick behavior; this harness supplies ports and does not replace policy.
- [Snapshot storage](issue-dependencies-github.prompt.md): native saved snapshot
  representation used as replay input, not captured operational data.
- [GitHub world](../../test/helpers/autopilot-github-world.mjs): source-selectable
  isolated fake world and synthetic independent-review answer.
- [Counting GitHub fake](../../test/helpers/github-repo-fake.mjs): REST/GraphQL
  responses, ETags, pagination, calls and writes without a network.
- [Synthetic replay](../../test/fixtures/autopilot-compare-backlog.json): controlled
  external observations for the default command.
- Node builtins: filesystem, paths, URLs, hashing and command-line I/O.
