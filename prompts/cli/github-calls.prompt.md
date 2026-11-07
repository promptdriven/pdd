# GitHub calls: count, budget and conditional reads

Own `src/github-calls.mjs`. Autopilot uses the person's own `gh` sign-in. Its
REST limit (5,000 calls each hour for a person) is also the limit of the
person's own work. Several coordinators on one login used the whole limit. This
module counts each `gh` call that pdd makes, keeps a small local ledger for each
repository on this machine, tells the tick when to read less, and keeps ETags
and bodies for conditional reads. It makes no GitHub call itself and adds no
credentials. It counts only the calls that pdd runs: the `gh` calls that the
coordinator and worker chats make themselves are not counted.

## Exports

| Export | Result |
|---|---|
| `GITHUB_PURPOSES` | `['dependencies','claims','issues','pulls','writes','setup','other']`, in status order |
| `GITHUB_SHARE`, `GITHUB_FLOOR` | The defaults `30` (percent) and `500` (calls) |
| `githubCall(args)` | `{api, method, endpoint, conditional}` of one gh argument list |
| `githubPurpose(args)` | The purpose of a call that its caller does not name |
| `githubRepository(args)` | The lowercase `owner/name` that a call names, or `null` |
| `githubReply(text)` | `{status, etag, link, rate, body}` of a `gh api --include` reply, or `null` |
| `githubEntry(args, outcome, purpose, at)` | One ledger entry |
| `githubStateRoot(env, stateRoot)` | `stateRoot`, else `$HOME/.local/state/pdd/autopilot` |
| `githubLedger({root, repository, fs})` | `{file, repository, record(entry), read(), compact(now)}` |
| `githubMachineEntries({root, fs})` | The entries of every ledger under `root` |
| `countGithubCalls(exec, {ledger, purpose, now})` | A runner like `exec` that records each `gh` call |
| `nativeGithubCounter(exec, {env, stateRoot, purpose, fs, now})` | A counting runner that finds the ledger from the call |
| `githubUsage(entries, now)` | The last hour: see [Usage](#usage) |
| `githubBudgetSettings(value)` | `{share, floor}` from `autopilot.github` in `pdd.json` |
| `githubBudget({usage, share, floor})` | See [Budget](#budget) |
| `githubStatusLine({usage, machine, budget})` | The one status line |
| `githubEtagCache({root, repository, fs})` | `{file, get(endpoint), set(endpoint, entry), save()}` |
| `githubFullLastPage(endpoint, items, next)` | True for a [full last page](#full-last-page): never read it with its ETag |

`fs` is the injected file port (native `node:fs`). `now` is a clock in
milliseconds (native `Date.now`).

## One call

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

The ledger of a repository is `ROOT/github/H.jsonl`, where `H` is the first 20
hex characters of the SHA-256 of the lowercase `owner/name`. The folder has mode
0700, the file 0600. Each line is one JSON entry:

| Field | Meaning |
|---|---|
| `at` | Call end, milliseconds |
| `repo` | Lowercase `owner/name` |
| `api` | `rest` or `graphql` |
| `purpose` | One of `GITHUB_PURPOSES` |
| `status` | The HTTP status of the reply; else the `HTTP NNN` in gh's error text; else null |
| `conditional` | `true` only for a conditional request |
| `resource`, `remaining`, `limit`, `resetAt` | Present when the reply had rate-limit headers |

`record` appends one line. `read` returns the entries of the file; a torn or
invalid line is skipped. `compact(now)` rewrites the file with only the entries
of the last 2 hours, through a temporary file and a rename, when an older entry
exists. Measurement is best effort: a failed write or compact is lost, and it
never changes or fails the call. A line that another process appends during a
compact can be lost.

`countGithubCalls` returns `(file, args, options)` that runs `exec`. For `gh`
it removes `options.purpose` and `options.repository`, runs the call, then
records one entry with the named purpose (else `purpose`, else `githubPurpose`)
and returns the value or throws the error of `exec` unchanged. The ledger is an
object, or a function of the arguments and `options.repository`; null records
nothing. Other programs run unchanged, also without these two options.
`nativeGithubCounter` uses the ledger of `githubRepository(args)`, else of a valid
`options.repository` (a GraphQL call names none in its arguments), under
`githubStateRoot`, so worktrees and the main checkout share it. It appends only
to a ledger file that already exists: the launcher makes it with its first call,
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

The budget acts only on the Autopilot tick. It does not keep a part of the
limit for the person:

- `share` is the percent of the hourly REST limit that the counted calls of this
  machine can reach before the tick defers its dependency re-sync (`low`). All
  other reads and writes of the tick go on.
- `floor` is the number of calls left below which the tick makes no GitHub call
  until the reset, except the heartbeats of its own live claims (`reserve`).
- `pdd` commands are counted but never wait for the budget. The coordinator and
  worker chats never wait for it, and their own `gh` calls are not counted.

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

`githubEtagCache` keeps `ROOT/github/H.etags.json` (the same `H`), an object
from endpoint to `{etag, body, next}`: the ETag, the exact body text and the next
page path of a 200 reply. `get` returns a saved entry with a string `etag` and
`body`, else undefined. `set` keeps an entry with a nonempty `etag`. `save`
writes, through a temporary file and a rename, only the entries that this read
got or set, so the file holds the working set of the last read. A read that got
or set no entry (it failed early) keeps the saved file. A read or write
failure gives an empty cache or a lost save; it only costs counted reads.

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

None: this module uses only the injected file port and clock. Its consumers, for
navigation only: the [Autopilot launcher](autopilot-launcher.prompt.md#github-budget)
counts its calls, applies the budget, shows the status line and reads review
pages with the full-last-page rule; the
[dependency GitHub reader](issue-dependencies-github.prompt.md#conditional-reads)
uses the ETag cache and the full-last-page rule.
