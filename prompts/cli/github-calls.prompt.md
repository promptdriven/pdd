# GitHub calls: count, budget and conditional reads

Own `src/github-calls.mjs`. Count pdd GitHub calls, budget from the active
identity's observed limit, and keep conditional read caches. Personal gh login
is the default. The [App adapter](github-app.prompt.md) authenticates native
calls when configured; this module never records credentials.
Autopilot chat calls pass through the same counter via its private gh wrapper.

<a id="call-primitives"></a>
The call-primitives context selection is this module's classification, reply,
ledger and countGithubCalls contract. It excludes nativeGithubCounter and the
native counter transport dependency. These primitives do not load the proxy.

## Exports

| Export | Result |
|---|---|
| `GITHUB_PURPOSES` | `['dependencies','claims','issues','pulls','writes','setup','other']`, in status order |
| `GITHUB_SHARE`, `GITHUB_FLOOR` | The defaults `30` (percent) and `1000` (calls) |
| `githubCall(args)` | `{api, method, endpoint, conditional}` of one gh argument list |
| `githubPurpose(args)` | The purpose of a call that its caller does not name |
| `githubRepository(args)` | The lowercase `owner/name` that a call names, or `null` |
| `githubReply(text)` | `{status, etag, link, rate, body}` of a `gh api --include` reply, or `null` |
| `githubEntry(args, outcome, purpose, at)` | One ledger entry |
| `githubStateRoot(env, stateRoot)` | `stateRoot`, else `$HOME/.local/state/pdd/autopilot` |
| `githubLedger({root, repository, fs})` | `{file, repository, record(entry), read(), compact(now)}` |
| `githubMachineEntries({root, fs})` | The entries of every ledger under `root` |
| `countGithubCalls(exec, {ledger, purpose, now, writes, env})` | A runner like `exec` that records each `gh` call |
| `nativeGithubCounter(exec, {env, stateRoot, purpose, fs, now})` | A counting runner that finds the ledger from the call |
| `githubUsage(entries, now)` | The last hour: see [Usage](#usage) |
| `githubBudgetSettings(value)` | `{share, floor}` from `autopilot.github` in `pdd.json` |
| `githubBudget({usage, share, floor})` | See [Budget](#budget) |
| `githubStatusLine({usage, machine, budget})` | The one status line |
| `githubEtagCache({root, repository, fs, now})` | `{file, get(endpoint), set(endpoint, entry), save()}` |
| `githubFloorGuard({floor, entries, now})` | `{floor, observe(reply), blocked(resource), stopped}`: see [Floor guard](#floor-guard) |
| `githubFullLastPage(endpoint, items, next)` | True for a [full last page](#full-last-page): never read it with its ETag |

`fs` is the injected file port (native `node:fs`). `now` is a clock in
milliseconds (native `Date.now`).

## One call

When a write-budget resolver is supplied, reserve content cost only for writes.
Observe every gh outcome, including free REST reads and GraphQL queries, through
the shared budget so a secondary-limit reply delays later writes from other
runners. Resolve a free read's budget only after a throttle outcome; ordinary
reads require no identity lookup or content reservation. Preserve the original
read result or error if cooldown observation fails. Use the shared budget's
`githubWriteThrottle` classification before resolving a free read's budget;
successful payload text must not start a cooldown or an identity lookup.

`githubCall` reads only the argument list. For `gh api`, the endpoint is the
first word that is not an option and not the value of an option. These options
take a value: `-X --method -H --header -f --raw-field -F --field --input -q --jq
-t --template --hostname --cache -p --preview`. The method is the `--method`
value in capitals; without it, it is `POST` when a field or `--input` is given,
as gh does, else `GET`. `api` is `graphql` for the endpoint `graphql`, else
`rest`. `conditional` is true when a header `If-None-Match:` is sent. gh's own
commands (`pr`, `issue`, `repo`, `auth`) use GraphQL: `api` is `graphql`,
`method` is null and `endpoint` is empty.

`githubPurpose` gives the first match:

| Call | Purpose |
|---|---|
| `gh auth …`, `gh repo …` | `setup` |
| `gh pr view/checks/list/status/diff` | `pulls`; other `gh pr` commands are `writes` |
| `gh issue view/list/status` | `issues`; other `gh issue` commands are `writes` |
| Another gh command, or `gh api graphql` | `other` |
| `gh api` with a method that is not `GET` | `writes` |
| A path with `/dependencies/`, `/sub_issues` or ending in `/timeline` | `dependencies` |
| `…/issues/comments/N` | `claims` (the claim comment and its heartbeat) |
| `…/pulls…`, check runs, check suites, commit status | `pulls` |
| `…/issues…`, `…/collaborators…` | `issues` |
| `user`, `rate_limit`, `repos/O/R`, contents, labels, git refs | `setup` |
| Any other path | `other` |

A caller that knows the purpose names it; a named purpose that is in
`GITHUB_PURPOSES` wins over this table.

`githubRepository` takes the first of: the `repos/OWNER/NAME` start of the
endpoint, the value of `--repo` or `-R`, a `https://github.com/OWNER/NAME/pull/N`
or `/issues/N` argument, or the name after `gh repo view`.

`githubReply` reads a reply that starts with an HTTP status line. Header names
ignore case. `rate` is null without `x-ratelimit-remaining`; else it is
`{resource, remaining, limit, resetAt}`: `resource` is `x-ratelimit-resource`
(`core` when absent), `resetAt` is `x-ratelimit-reset` in milliseconds. `limit`
and `resetAt` are absent when GitHub does not send them. gh exits with 1 for a
304 reply and prints the headers: a caller reads the reply from the output of the
failed command too.

## Ledger

The ledger uses the logical locator `ROOT/github/H.jsonl`, where `H` is the first
20 hex characters of the SHA-256 of the lowercase `owner/name`. Import that
legacy file into the machine events journal. Native state is private (folder
0700, database 0600). Each journal row is one JSON entry:

| Field | Meaning |
|---|---|
| `at` | Call end, milliseconds |
| `repo` | Lowercase `owner/name` |
| `api` | `rest` or `graphql` |
| `purpose` | One of `GITHUB_PURPOSES` |
| `status` | The HTTP status of the reply; else the `HTTP NNN` in gh's error text; else null |
| `conditional` | `true` only for a conditional request |
| `resource`, `remaining`, `limit`, `resetAt` | Present when the reply had rate-limit headers |

`record` appends one journal row. `read` returns the retained entries; import
skips torn or invalid legacy lines. `compact(now)` deletes entries outside the
last 2 hours in one transaction, when an older entry exists. Measurement is best effort: a failed write or compact is lost, and it
never changes or fails the call. A concurrent append survives compaction unless it meets the expiry rule.

`countGithubCalls` returns `(file, args, options)` that runs `exec`. For `gh`
it removes `options.purpose` and `options.repository`, runs the call, then
first reserves content writes through its optional `writes(args,options)` budget port,
then records one entry with the named purpose (else `purpose`, else `githubPurpose`)
and observes the write outcome for shared secondary-limit cooldowns. It returns
the value or throws the error of `exec` unchanged. Budget refusal happens before
dispatch and makes no call entry. Mark dispatched environments with
`PDD_GITHUB_COUNTED=1`, preserving the explicit call environment (else injected
`env`, native process.env), to prevent nested private gh wrappers from double counting. The ledger is an
object, or a function of the arguments and `options.repository`; null records
nothing. Other programs run unchanged, also without these two options.
`nativeGithubCounter` uses the ledger of `githubRepository(args)`, else of a valid
`options.repository` (a GraphQL call names none in its arguments), under
`githubStateRoot`, so worktrees and the main checkout share it. It appends only
to a ledger that already exists in storage or in a legacy file: the launcher makes it with its first call,
so a pdd command counts its calls for the repositories where Autopilot runs on
this machine. A call without a repository, or for a repository without a
ledger, is not recorded; so a test that puts a fake `gh` on PATH adds nothing
to a real ledger.

## Usage

`githubUsage(entries, now)` returns `{calls, rest, graphql, counted, conditional,
notModified, byPurpose, rate}` for the entries with `now − 1 hour < at ≤ now`:
all calls, REST calls, GraphQL calls, REST calls that count against the limit
(all except 304 replies, because a 304 reply does not count), conditional
requests, 304 replies of conditional requests, and the calls of each purpose.
`rate` has, for each resource, the newest `{remaining, limit, resetAt, at}` of
all given entries whose `resetAt` is later than `now`. An older observation
is no longer valid after its reset, so it is left out.

## Budget

The share budget acts on the Autopilot tick. The reserve floor also covers
native dependency observations for Autopilot repositories:

- `share` is the percent of the hourly REST limit that the counted calls of this
  machine can reach before the tick defers its dependency re-sync (`low`). All
  other reads and writes of the tick go on.
- `floor` is the number of calls left below which the tick makes no GitHub call
  until the reset, except the heartbeats of its own live claims (`reserve`). The
  default is 1,000. Safety reads and other tools can still use this reserve.
- Below the floor, the [floor guard](#floor-guard) also stops the non-safety reads
  of the tick and native dependency observations for an Autopilot repository,
  including `pdd dependencies prepare`, `complete`, direct snapshot reads and
  automatic start. Safety reads and writes go on. Other `pdd` operations are
  counted but do not wait for this floor. The coordinator and worker chats never
  wait for the budget. The App shell wrapper counts their own `gh` calls; personal shell calls are not counted.

`githubBudgetSettings(value)` reads `share` (an integer from 1 to
100) and `floor` (an integer, 0 or more) from the object `autopilot.github` in
`pdd.json`; a missing or invalid value takes the default.

`githubBudget({usage, share, floor})` uses the entries of all ledgers on this
machine. `allowed` is `floor(limit × share / 100)`, with the newest `core` limit,
else 5000. `used` is `usage.counted`. The result is
`{state, allowed, used, share, floor}`, and for `reserve` also
`{resource, remaining, resetAt}`:

| State | When | The tick |
|---|---|---|
| `reserve` | The newest `core` or `graphql` remaining is less than `floor` (first `core`) | Makes no GitHub call until `resetAt`, except the heartbeats of its own live claims ([tick](autopilot-launcher.prompt.md#github-budget)) |
| `low` | Otherwise, `used ≥ allowed` | Defers the dependency re-sync and keeps heartbeats ([tick](autopilot-launcher.prompt.md#github-budget)) |
| `normal` | Otherwise | Works as usual |

## Status line

`githubStatusLine({usage, machine, budget})` returns one line. `usage` is this
repository's usage, `machine` the usage of all ledgers on this machine (default
`usage`), `budget` is optional:

`GitHub calls in the last hour: N (P1 C1, P2 C2); H of K conditional reads were 304 (X%); REST limit R of L left until HH:MMZ; budget S: Autopilot on this machine used U of A (Y%).`

In `reserve`, `S` is `reserve (M REST calls left, below the floor of F)`, with
the budget's `remaining` and `floor`, and `GraphQL points` for the `graphql`
resource. `U` and `A` are the budget's `used` and `allowed`: the counted calls
of this machine, not the calls of the chats.

The purposes come in `GITHUB_PURPOSES` order and only with a count; with no
call the parenthesis is absent. Without conditional reads the second part is
`no conditional reads`. Without a valid `core` observation the third part is
`REST limit not seen in the last hour`. ` of L` is absent without a limit. The
budget part is absent without `budget`. `X` is the rounded percentage.

## ETag cache

`githubEtagCache` uses the logical locator `ROOT/github/H.etags.json` (the same
`H`), imported once into a cache record. The value is an object
from endpoint to `{etag, body, next, at}`: the ETag, the exact body text and the
next page path of a 200 reply, and the time (`now`) when this cache last got or
set it. `get` returns a saved entry with a string `etag` and `body`, else
undefined. `set` keeps an entry with a nonempty `etag`. The tick and the `pdd`
commands of one repository share this record. So `save` merges: it reads the record
inside its transaction, puts the entries that this cache got or set over it, and keeps
the entries used in the last 24 hours, newest first, at most 5,000 entries and
32 MiB of bodies. The merge and replacement commit in one transaction. A
cache that got or set no entry (it failed early) keeps the saved record. A read or
write failure gives an empty cache or a lost save; it only costs counted reads.

<a id="floor-guard"></a>
### Floor guard

`githubFloorGuard({floor, entries, now})` starts from the newest valid rate of
each resource in `entries` and follows each later
reply: `observe(reply)` takes the `rate` of a `githubReply` result, and a reply
without rate headers changes nothing. `blocked(resource)` (default `core`) is
true while the newest remaining of that resource is less than `floor` and its
reset is not past; then `stopped` stays true for this guard. A caller asks
`blocked('core')` before each non-safety REST read, and `blocked('core')` and
`blocked('graphql')` before a non-safety GraphQL read (a dependency snapshot
without REST reads is not complete anyway), and stops that read. Safety reads (claim
checks, heartbeats, trust and permission reads, the reads that a write depends
on and readbacks after writes) and writes never ask it. A rate-limit reply (403
or 429 with no calls left) is a reply with remaining 0, so the reads after it
stop at once instead of failing one by one.

The caller selects `entries` for the active identity before constructing the
guard. Consume that selection without filtering it back to personal identity.
Use the same rate validity rules as `githubUsage`, including reset expiry and
future observation rejection. This preserves a known installation reserve
breach before the first non-safety read. Personal and other installation limits
must not override the caller's selected installation.

<a id="full-last-page"></a>
### A full last page

GitHub's ETag covers only the body of a reply, and a 304 reply has no `Link`
header. So when a list grows past a full page, that page keeps its body and its
ETag, and a conditional read of it gets a 304 with the saved "no next page". The
reader then never asks for the new page and reports the read as complete. In a
list in ascending order (comments, the issue history, reviews) a full page never
changes again, so the miss would last.

`githubFullLastPage(endpoint, items, next)` is true when `items` is a list, `next`
is empty and `items` has at least `P` entries. `P` is the `per_page` value of the
endpoint's query (at most 100), else GitHub's default 30. A caller never sends the
saved ETag for such a page: it reads the page in full and follows a new next
page. A page with a next page, or with fewer than `P` entries, stays conditional:
a new entry changes its body, or GitHub serves the saved next page.

## Dependencies

- [GitHub App identity](github-app.prompt.md): required native generation and
  verification context for authenticating native gh calls and Git network commands and the bundled wrappers.

- [Native counter transport](github-write-proxy.prompt.md#native-counter-transport):
  required generation and verification context for nativeGithubCounter's use of
  githubWriteRunner and githubOriginalExecutable. Load that export selection;
  the proxy uses the call-primitives selection defined above, not this counter.


- [Autopilot machine storage](autopilot-store.prompt.md): required native generation and verification context for local state and atomic migration.

The [shared write budget](github-writes.prompt.md) is required for native
Autopilot write admission. Native counters use the private proxy process adapter
when an Autopilot ledger exists. The file port and clock supply local state. Its consumers, for
navigation only: the [Autopilot launcher](autopilot-launcher.prompt.md#github-budget)
counts its calls, applies the budget, shows the status line and reads review
pages with the full-last-page rule; the
[dependency GitHub reader](issue-dependencies-github.prompt.md#conditional-reads)
uses the ETag cache, the full-last-page rule and the floor guard.

## Machine storage

Use [Autopilot machine storage](autopilot-store.prompt.md) for native machine
state. Import each existing record once and retain its old file unchanged.
SQL belongs only to that backend. Keep existing guards, limits, identity and
failure policy. File paths exposed by adapters remain stable logical locators.
Store call rows in the events journal, scoped by the lowercase repository
hash. Preserve every call, including identical calls. `githubLedger` also
exposes `exists()` for participation checks. Import JSONL once, then compact
inside a transaction. ETag merge and replacement use one cache transaction.
Machine-wide reads isolate each legacy source read failure: keep readable and
already committed observations from other repositories available for budget
decisions. Leave a failed source unmarked so a later read can retry it; a failed
read must not commit any rows from that source. Storage transaction failures
retain the existing empty-result policy.
An injected `store` port replaces the backend alongside the existing `fs` port.

## App accounting

`countGithubCalls` records a non-secret `identity` from outcome.githubIdentity
when present. Personal entries omit it. `githubMachineEntries({root,fs,identity})`
and `githubUsage(entries,now,identity)` select only that identity; omitted
identity means personal entries. App installations therefore share their local
quota across repositories but do not borrow a personal or another installation's
limit. `githubEtagCache` accepts identity and uses a different cache filename for
each identity. Native counters use `githubAppRunner` before execution, accept
`appPorts` for its injected ports, and retain existing counting policy.
