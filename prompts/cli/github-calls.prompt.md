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
| `GITHUB_SHARE`, `GITHUB_FLOOR` | The defaults `30` (percent) and `1000` (calls) |
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
| `githubEtagCache({root, repository, fs, now})` | `{file, get(endpoint), set(endpoint, entry), save()}` |
| `githubFloorGuard({floor, entries, now})` | `{floor, observe(reply), blocked(resource), stopped}`: see [Floor guard](#floor-guard) |
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
  wait for the budget, and their own `gh` calls are not counted.

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
from endpoint to `{etag, body, next, at}`: the ETag, the exact body text and the
next page path of a 200 reply, and the time (`now`) when this cache last got or
set it. `get` returns a saved entry with a string `etag` and `body`, else
undefined. `set` keeps an entry with a nonempty `etag`. The tick and the `pdd`
commands of one repository share this file. So `save` merges: it reads the file
as it is then, puts the entries that this cache got or set over it, and keeps
the entries used in the last 24 hours, newest first, at most 5,000 entries and
32 MiB of bodies. It writes through a temporary file and a rename, mode 0600. A
cache that got or set no entry (it failed early) keeps the saved file. A read or
write failure gives an empty cache or a lost save; it only costs counted reads.

<a id="floor-guard"></a>
### Floor guard

`githubFloorGuard({floor, entries, now})` starts from the newest valid rate of
each resource in `entries` (as `githubUsage` gives it) and follows each later
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

## Per-run cost attribution

`nativeGithubCounter` also accepts `costRun(options)` and `costRecord(runDir, entry)` ports. After each gh call, resolve the run from options (production: the exact run worktree in `options.cwd`, found by its Git common dir). Append the numeric call through `recordCostGithub` even for normal runs without an Autopilot ledger. Keep the original result/error if resolution or recording fails. Never allocate a repository-wide call to overlapping issues.

## Dependencies

- [Cost ledger](cost-ledger.prompt.md): required native generation and verification context for per-run call recording through the default costRecord port.

This module also uses the injected file port and clock. Its consumers, for
navigation only: the [Autopilot launcher](autopilot-launcher.prompt.md#github-budget)
counts its calls, applies the budget, shows the status line and reads review
pages with the full-last-page rule; the
[dependency GitHub reader](issue-dependencies-github.prompt.md#conditional-reads)
uses the ETag cache, the full-last-page rule and the floor guard.

In Runtime checks, `ledgers`, `etag_caches` and `floor_guards` (`store`, `load`) hold the state of `GithubLedger`, `GithubEtagCache` and `GithubFloorGuard` handles; `compute.hash_utf8` hashes lowercase `owner/name`; `files` (`read`, `write`, `stat`) and `fs.readdir` bind ledger and ETag files; `exec.run` binds the wrapped subprocess runner (`countGithubCalls` and `nativeGithubCounter` raise `exec-failed` when `exec.run` returns a nonzero `exitCode` after recording the call); `clock.now` binds `now`; and `cost` (`findRun`, `recordGithub`) binds per-run cost attribution. Real atomic temp-file renames, file modes and live `gh` processes stay in `test/github-calls.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "9e78024c7b26e40a589d27302e03ece583f8bfb0b38bd8ba435ce1f66e910e7a",
  "entries": [
    {
      "operation": "githubCall",
      "input_schema": {
        "type": "object",
        "properties": {
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "args"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "api": {
            "type": "string",
            "enum": [
              "rest",
              "graphql"
            ]
          },
          "method": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "endpoint": {
            "type": "string"
          },
          "conditional": {
            "type": "boolean"
          }
        },
        "required": [
          "api",
          "method",
          "endpoint",
          "conditional"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubPurpose",
      "input_schema": {
        "type": "object",
        "properties": {
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "args"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "purpose": {
            "type": "string",
            "enum": [
              "dependencies",
              "claims",
              "issues",
              "pulls",
              "writes",
              "setup",
              "other"
            ]
          }
        },
        "required": [
          "purpose"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubRepository",
      "input_schema": {
        "type": "object",
        "properties": {
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "args"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "repository": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "repository"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubReply",
      "input_schema": {
        "type": "object",
        "properties": {
          "text": {
            "type": "string"
          }
        },
        "required": [
          "text"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "reply": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "status": {
                    "type": "integer"
                  },
                  "etag": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "link": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "rate": {
                    "oneOf": [
                      {
                        "type": "object",
                        "properties": {
                          "resource": {
                            "type": "string"
                          },
                          "remaining": {
                            "type": "integer"
                          },
                          "limit": {
                            "type": "integer"
                          },
                          "resetAt": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "resource",
                          "remaining"
                        ],
                        "additionalProperties": false
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "body": {
                    "type": "string"
                  }
                },
                "required": [
                  "status",
                  "rate",
                  "body"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "reply"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubEntry",
      "input_schema": {
        "type": "object",
        "properties": {
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "outcome": {
            "type": "object",
            "properties": {
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "purpose": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "at": {
            "type": "integer"
          }
        },
        "required": [
          "args",
          "outcome",
          "at"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "entry": {
            "type": "object",
            "properties": {
              "at": {
                "type": "integer"
              },
              "api": {
                "type": "string",
                "enum": [
                  "rest",
                  "graphql"
                ]
              },
              "purpose": {
                "type": "string"
              },
              "status": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "conditional": {
                "type": "boolean"
              },
              "resource": {
                "type": "string"
              },
              "remaining": {
                "type": "integer"
              },
              "limit": {
                "type": "integer"
              },
              "resetAt": {
                "type": "integer"
              }
            },
            "required": [
              "at",
              "api",
              "purpose",
              "status"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "entry"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubStateRoot",
      "input_schema": {
        "type": "object",
        "properties": {
          "env": {
            "type": "object",
            "properties": {
              "HOME": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "stateRoot": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "env"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          }
        },
        "required": [
          "root"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubLedger",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          },
          "repository": {
            "type": "string"
          }
        },
        "required": [
          "root",
          "repository"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "factory",
        "type": "GithubLedger",
        "path": "/handle"
      },
      "resource_operations": [
        "ledgers.store"
      ]
    },
    {
      "operation": "record",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "entry": {
            "type": "object",
            "properties": {
              "at": {
                "type": "integer"
              },
              "api": {
                "type": "string"
              },
              "purpose": {
                "type": "string"
              },
              "status": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "conditional": {
                "type": "boolean"
              },
              "resource": {
                "type": "string"
              },
              "remaining": {
                "type": "integer"
              },
              "limit": {
                "type": "integer"
              },
              "resetAt": {
                "type": "integer"
              }
            },
            "required": [
              "at",
              "api",
              "purpose",
              "status"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "handle",
          "entry"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubLedger",
        "path": "/handle"
      },
      "resource_operations": [
        "ledgers.load",
        "compute.hash_utf8",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "read",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "entries": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "at": {
                  "type": "integer"
                },
                "repo": {
                  "type": "string"
                },
                "api": {
                  "type": "string"
                },
                "purpose": {
                  "type": "string"
                },
                "status": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "conditional": {
                  "type": "boolean"
                },
                "resource": {
                  "type": "string"
                },
                "remaining": {
                  "type": "integer"
                },
                "limit": {
                  "type": "integer"
                },
                "resetAt": {
                  "type": "integer"
                }
              },
              "required": [
                "at",
                "purpose"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "entries"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubLedger",
        "path": "/handle"
      },
      "resource_operations": [
        "ledgers.load",
        "compute.hash_utf8",
        "files.read"
      ]
    },
    {
      "operation": "compact",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "now": {
            "type": "integer"
          }
        },
        "required": [
          "handle",
          "now"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubLedger",
        "path": "/handle"
      },
      "resource_operations": [
        "ledgers.load",
        "compute.hash_utf8",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "githubMachineEntries",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          }
        },
        "required": [
          "root"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "entries": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "at": {
                  "type": "integer"
                },
                "repo": {
                  "type": "string"
                },
                "api": {
                  "type": "string"
                },
                "purpose": {
                  "type": "string"
                },
                "status": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "conditional": {
                  "type": "boolean"
                },
                "resource": {
                  "type": "string"
                },
                "remaining": {
                  "type": "integer"
                },
                "limit": {
                  "type": "integer"
                },
                "resetAt": {
                  "type": "integer"
                }
              },
              "required": [
                "at",
                "purpose"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "entries"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "fs.readdir",
        "files.read"
      ]
    },
    {
      "operation": "countGithubCalls",
      "input_schema": {
        "type": "object",
        "properties": {
          "file": {
            "type": "string"
          },
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "options": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "purpose": {
                "type": "string"
              },
              "repository": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "purpose": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "ledger": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "file": {
                    "type": "string"
                  },
                  "repository": {
                    "type": "string"
                  }
                },
                "required": [
                  "file",
                  "repository"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "file",
          "args"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "stdout": {
            "type": "string"
          },
          "stderr": {
            "type": "string"
          },
          "exitCode": {
            "type": "integer"
          }
        },
        "required": [
          "stdout",
          "stderr",
          "exitCode"
        ],
        "additionalProperties": false
      },
      "errors": [
        "exec-failed"
      ],
      "resource_operations": [
        "exec.run",
        "clock.now",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "nativeGithubCounter",
      "input_schema": {
        "type": "object",
        "properties": {
          "file": {
            "type": "string"
          },
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "options": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "purpose": {
                "type": "string"
              },
              "repository": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "env": {
            "type": "object",
            "properties": {
              "HOME": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "stateRoot": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "purpose": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "file",
          "args"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "stdout": {
            "type": "string"
          },
          "stderr": {
            "type": "string"
          },
          "exitCode": {
            "type": "integer"
          }
        },
        "required": [
          "stdout",
          "stderr",
          "exitCode"
        ],
        "additionalProperties": false
      },
      "errors": [
        "exec-failed"
      ],
      "resource_operations": [
        "exec.run",
        "clock.now",
        "compute.hash_utf8",
        "cost.findRun",
        "cost.recordGithub",
        "files.stat",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "githubUsage",
      "input_schema": {
        "type": "object",
        "properties": {
          "entries": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "at": {
                  "type": "integer"
                },
                "api": {
                  "type": "string"
                },
                "purpose": {
                  "type": "string"
                },
                "status": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "conditional": {
                  "type": "boolean"
                },
                "resource": {
                  "type": "string"
                },
                "remaining": {
                  "type": "integer"
                },
                "limit": {
                  "type": "integer"
                },
                "resetAt": {
                  "type": "integer"
                }
              },
              "required": [
                "at",
                "purpose"
              ],
              "additionalProperties": false
            }
          },
          "now": {
            "type": "integer"
          }
        },
        "required": [
          "entries",
          "now"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "calls": {
            "type": "integer"
          },
          "rest": {
            "type": "integer"
          },
          "graphql": {
            "type": "integer"
          },
          "counted": {
            "type": "integer"
          },
          "conditional": {
            "type": "integer"
          },
          "notModified": {
            "type": "integer"
          },
          "byPurpose": {
            "type": "object",
            "properties": {
              "dependencies": {
                "type": "integer"
              },
              "claims": {
                "type": "integer"
              },
              "issues": {
                "type": "integer"
              },
              "pulls": {
                "type": "integer"
              },
              "writes": {
                "type": "integer"
              },
              "setup": {
                "type": "integer"
              },
              "other": {
                "type": "integer"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "rate": {
            "type": "object",
            "properties": {
              "core": {
                "type": "object",
                "properties": {
                  "remaining": {
                    "type": "integer"
                  },
                  "limit": {
                    "type": "integer"
                  },
                  "resetAt": {
                    "type": "integer"
                  },
                  "at": {
                    "type": "integer"
                  }
                },
                "required": [
                  "remaining",
                  "resetAt",
                  "at"
                ],
                "additionalProperties": false
              },
              "graphql": {
                "type": "object",
                "properties": {
                  "remaining": {
                    "type": "integer"
                  },
                  "limit": {
                    "type": "integer"
                  },
                  "resetAt": {
                    "type": "integer"
                  },
                  "at": {
                    "type": "integer"
                  }
                },
                "required": [
                  "remaining",
                  "resetAt",
                  "at"
                ],
                "additionalProperties": false
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "calls",
          "rest",
          "graphql",
          "counted",
          "conditional",
          "notModified",
          "byPurpose",
          "rate"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubBudgetSettings",
      "input_schema": {
        "type": "object",
        "properties": {
          "value": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "share": {
                    "type": "integer"
                  },
                  "floor": {
                    "type": "integer"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "share": {
            "type": "integer"
          },
          "floor": {
            "type": "integer"
          }
        },
        "required": [
          "share",
          "floor"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubBudget",
      "input_schema": {
        "type": "object",
        "properties": {
          "usage": {
            "type": "object",
            "properties": {
              "counted": {
                "type": "integer"
              },
              "rate": {
                "type": "object",
                "properties": {
                  "core": {
                    "type": "object",
                    "properties": {
                      "remaining": {
                        "type": "integer"
                      },
                      "limit": {
                        "type": "integer"
                      },
                      "resetAt": {
                        "type": "integer"
                      },
                      "at": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "remaining",
                      "resetAt"
                    ],
                    "additionalProperties": false
                  },
                  "graphql": {
                    "type": "object",
                    "properties": {
                      "remaining": {
                        "type": "integer"
                      },
                      "limit": {
                        "type": "integer"
                      },
                      "resetAt": {
                        "type": "integer"
                      },
                      "at": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "remaining",
                      "resetAt"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "counted",
              "rate"
            ],
            "additionalProperties": false
          },
          "share": {
            "type": "integer"
          },
          "floor": {
            "type": "integer"
          }
        },
        "required": [
          "usage"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "state": {
            "type": "string",
            "enum": [
              "normal",
              "low",
              "reserve"
            ]
          },
          "allowed": {
            "type": "integer"
          },
          "used": {
            "type": "integer"
          },
          "share": {
            "type": "integer"
          },
          "floor": {
            "type": "integer"
          },
          "resource": {
            "type": "string"
          },
          "remaining": {
            "type": "integer"
          },
          "resetAt": {
            "type": "integer"
          }
        },
        "required": [
          "state",
          "allowed",
          "used",
          "share",
          "floor"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubStatusLine",
      "input_schema": {
        "type": "object",
        "properties": {
          "usage": {
            "type": "object",
            "properties": {
              "calls": {
                "type": "integer"
              },
              "conditional": {
                "type": "integer"
              },
              "notModified": {
                "type": "integer"
              },
              "byPurpose": {
                "type": "object",
                "properties": {
                  "dependencies": {
                    "type": "integer"
                  },
                  "claims": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "integer"
                  },
                  "pulls": {
                    "type": "integer"
                  },
                  "writes": {
                    "type": "integer"
                  },
                  "setup": {
                    "type": "integer"
                  },
                  "other": {
                    "type": "integer"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "rate": {
                "type": "object",
                "properties": {
                  "core": {
                    "type": "object",
                    "properties": {
                      "remaining": {
                        "type": "integer"
                      },
                      "limit": {
                        "type": "integer"
                      },
                      "resetAt": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "remaining",
                      "resetAt"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "calls",
              "conditional",
              "notModified",
              "byPurpose",
              "rate"
            ],
            "additionalProperties": false
          },
          "machine": {
            "type": "object",
            "properties": {
              "rate": {
                "type": "object",
                "properties": {
                  "core": {
                    "type": "object",
                    "properties": {
                      "remaining": {
                        "type": "integer"
                      },
                      "limit": {
                        "type": "integer"
                      },
                      "resetAt": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "remaining",
                      "resetAt"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "rate"
            ],
            "additionalProperties": false
          },
          "budget": {
            "type": "object",
            "properties": {
              "state": {
                "type": "string"
              },
              "allowed": {
                "type": "integer"
              },
              "used": {
                "type": "integer"
              },
              "share": {
                "type": "integer"
              },
              "floor": {
                "type": "integer"
              },
              "resource": {
                "type": "string"
              },
              "remaining": {
                "type": "integer"
              }
            },
            "required": [
              "state",
              "allowed",
              "used",
              "share",
              "floor"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "usage"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "line": {
            "type": "string"
          }
        },
        "required": [
          "line"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "githubEtagCache",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          },
          "repository": {
            "type": "string"
          }
        },
        "required": [
          "root",
          "repository"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "factory",
        "type": "GithubEtagCache",
        "path": "/handle"
      },
      "resource_operations": [
        "etag_caches.store"
      ]
    },
    {
      "operation": "get",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "endpoint": {
            "type": "string"
          }
        },
        "required": [
          "handle",
          "endpoint"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "entry": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "etag": {
                    "type": "string"
                  },
                  "body": {
                    "type": "string"
                  },
                  "next": {
                    "type": "string"
                  },
                  "at": {
                    "type": "integer"
                  }
                },
                "required": [
                  "etag",
                  "body"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "entry"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubEtagCache",
        "path": "/handle"
      },
      "resource_operations": [
        "etag_caches.load",
        "etag_caches.store",
        "compute.hash_utf8",
        "files.read",
        "clock.now"
      ]
    },
    {
      "operation": "set",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "endpoint": {
            "type": "string"
          },
          "entry": {
            "type": "object",
            "properties": {
              "etag": {
                "type": "string"
              },
              "body": {
                "type": "string"
              },
              "next": {
                "type": "string"
              }
            },
            "required": [
              "etag",
              "body"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "handle",
          "endpoint",
          "entry"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubEtagCache",
        "path": "/handle"
      },
      "resource_operations": [
        "etag_caches.load",
        "etag_caches.store",
        "clock.now"
      ]
    },
    {
      "operation": "save",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubEtagCache",
        "path": "/handle"
      },
      "resource_operations": [
        "etag_caches.load",
        "etag_caches.store",
        "compute.hash_utf8",
        "files.read",
        "files.write",
        "clock.now"
      ]
    },
    {
      "operation": "githubFloorGuard",
      "input_schema": {
        "type": "object",
        "properties": {
          "floor": {
            "type": "integer"
          },
          "entries": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "at": {
                  "type": "integer"
                },
                "purpose": {
                  "type": "string"
                },
                "resource": {
                  "type": "string"
                },
                "remaining": {
                  "type": "integer"
                },
                "limit": {
                  "type": "integer"
                },
                "resetAt": {
                  "type": "integer"
                }
              },
              "required": [
                "at",
                "purpose"
              ],
              "additionalProperties": false
            }
          },
          "now": {
            "type": "integer"
          }
        },
        "required": [],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "factory",
        "type": "GithubFloorGuard",
        "path": "/handle"
      },
      "resource_operations": [
        "floor_guards.store"
      ]
    },
    {
      "operation": "observe",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "reply": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "rate": {
                    "oneOf": [
                      {
                        "type": "object",
                        "properties": {
                          "resource": {
                            "type": "string"
                          },
                          "remaining": {
                            "type": "integer"
                          },
                          "resetAt": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "resource",
                          "remaining"
                        ],
                        "additionalProperties": false
                      },
                      {
                        "type": "null"
                      }
                    ]
                  }
                },
                "required": [
                  "rate"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "handle",
          "reply"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "stopped": {
            "type": "boolean"
          }
        },
        "required": [
          "stopped"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubFloorGuard",
        "path": "/handle"
      },
      "resource_operations": [
        "floor_guards.load",
        "floor_guards.store"
      ]
    },
    {
      "operation": "blocked",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "resource": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "blocked": {
            "type": "boolean"
          },
          "stopped": {
            "type": "boolean"
          }
        },
        "required": [
          "blocked",
          "stopped"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "GithubFloorGuard",
        "path": "/handle"
      },
      "resource_operations": [
        "floor_guards.load",
        "floor_guards.store",
        "clock.now"
      ]
    },
    {
      "operation": "githubFullLastPage",
      "input_schema": {
        "type": "object",
        "properties": {
          "endpoint": {
            "type": "string"
          },
          "items": {
            "type": "array",
            "items": {
              "type": "integer"
            }
          },
          "next": {
            "type": "string"
          }
        },
        "required": [
          "endpoint",
          "items",
          "next"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "full": {
            "type": "boolean"
          }
        },
        "required": [
          "full"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "ledgers",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "name": "store",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              },
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "handle",
              "config"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "load",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              }
            },
            "required": [
              "handle"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "etag_caches",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "name": "store",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              },
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "handle",
              "config"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "load",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              }
            },
            "required": [
              "handle"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "floor_guards",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "name": "store",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              },
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "handle",
              "config"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "load",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              }
            },
            "required": [
              "handle"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "state"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "compute",
      "kind": "compute",
      "access": "read",
      "operations": [
        {
          "name": "hash_utf8",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "text": {
                "type": "string"
              }
            },
            "required": [
              "text"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string"
              }
            },
            "required": [
              "value"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "files",
      "kind": "blob",
      "access": "write",
      "operations": [
        {
          "name": "stat",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exists": {
                "type": "boolean"
              },
              "is_symlink": {
                "type": "boolean"
              },
              "size": {
                "type": "integer",
                "minimum": 0
              }
            },
            "required": [
              "exists",
              "is_symlink",
              "size"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "read",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": {
                "type": "string"
              }
            },
            "required": [
              "content"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              },
              "content": {
                "type": "string"
              }
            },
            "required": [
              "path",
              "content"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "fs",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readdir",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "entries": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "entries"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "exec",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "run",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "file": {
                "type": "string"
              },
              "args": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "cwd": {
                "type": "string"
              }
            },
            "required": [
              "file",
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              },
              "exitCode": {
                "type": "integer"
              }
            },
            "required": [
              "stdout",
              "stderr",
              "exitCode"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "clock",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "now",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "milliseconds": {
                "type": "integer"
              }
            },
            "required": [
              "milliseconds"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "cost",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "findRun",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              }
            },
            "required": [
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "runDir"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "recordGithub",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              },
              "at": {
                "type": "integer"
              }
            },
            "required": [
              "runDir",
              "at"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 64,
    "max_model_calls": 20
  },
  "conventions": [
    {
      "path": "/entries/6/result_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/7/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/8/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/9/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/17/result_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/18/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/19/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/20/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/21/result_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/22/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/23/input_schema/properties/handle",
      "convention": "handle"
    }
  ],
  "schema_version": "prompt-runtime.interface.v2",
  "instance_types": [
    {
      "name": "GithubLedger",
      "resource": "ledgers"
    },
    {
      "name": "GithubEtagCache",
      "resource": "etag_caches"
    },
    {
      "name": "GithubFloorGuard",
      "resource": "floor_guards"
    }
  ]
}
```
</details>
