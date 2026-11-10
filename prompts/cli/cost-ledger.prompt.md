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
minutes, plus outcome counts, per-account token totals and coverage. Specifically,
it joins these lines with `\n`:
- `Issue costs (local measured usage):`
- For `key` in `["day", "week"]` (`row = report[key]`):
  - `Last <key>: <describe(row.totals)>`
  - `  Per merged issue (<row.mergedIssues>): P50 <describe(row.p50)>; P90 <describe(row.p90)>`
  - For each `token` in `row.totals.tokens`:
    `  <token.account>: <token.total> tokens (input <token.input>, cached <token.cachedInput>, output <token.output>, reasoning <token.reasoningOutput>)`
  - When `row.coverage.length > 0`:
    `  Coverage: <row.coverage.join(', ')>`
- `Outcomes: running <N>, merged <N>, reverted <N>, stuck <N>, closed <N>, parked <N>`
where `describe(row)` is `'no merged issues'` when `row` is null, else
`<num(row.totalTokens)> tokens; CI <num(row.ciMinutes)> min; suite <num(row.suiteMinutes)> min; GitHub <row.githubCalls>; person Q/A/approvals <row.person.questions>/<row.person.answers>/<row.person.approvals>, active <num(row.person.activeMinutes)> min, wait <num(row.person.waitingMinutes)> min`,
and `num(v)` formats null as `'unknown'` and finite numbers as `Number(v.toFixed(2))`.


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

Through the Runtime interface:
- `files` (`blob`: `read`, `write`, `stat`) reads and writes session transcripts,
  audit JSON files, `<runDir>/github-cost.jsonl`, and `<runDir>/cost-ci-<number>.json`
  (`read` returns `{content}` or `{content: null}` when absent; `stat` returns
  `{exists, is_symlink, size}`; `write` writes UTF-8 content and returns `{}`).
- `fs` (`readdir`) lists `<runDir>/audits` and Codex session date directories
  (`<config>/sessions/YYYY/MM/DD`), returning `{entries}` or `{entries: [], code: "ENOENT"}`
  when absent.
- `exec` (`execFile`) executes `gh api repos/<repo>/actions/runs?...` for
  `captureClosedCi`, returning `{code, stdout, stderr}`.
- `clock` (`now`) returns `{ms}` for `captureCosts`.
- `compute` (`hash_utf8`) returns `{value}` (64-hex SHA-256 digest; the first 20
  lowercase hex characters form the local hash for account `<agent>:<hash20>`,
  session checkpoint key `<hash20>`, and Claude message id `<hash20>`).
- `captureCosts({before, run, options})` requires a `run` object with non-empty
  `runId` and `runDir` (otherwise throws `Error("Invalid run for cost capture")`)
  and returns `{cost}`.
- `applyCostMeasurement({run, input, at})` returns `{run}` or throws `Error`
  (`"Invalid cost measurement"` or `"Cost measurement id conflict"`).
- `recordCostGithub({runDir, entry})` requires a non-empty `runDir` string and an
  `entry` object with nonnegative finite `at` (otherwise throws
  `Error("Invalid GitHub cost entry")`), reads and appends `{"at":entry.at}\n` to
  `<runDir>/github-cost.jsonl` via `files.read` and `files.write`, and returns
  `{ok: true}`.
- `captureClosedCi({run})` requires a `run` object with non-empty `runDir`, `repo`,
  and `root` (otherwise throws `Error("Invalid run for CI capture")`), checks
  `files.stat({path: "<runDir>/cost-ci-<number>.json"})` before reserving and
  writing `<runDir>/cost-ci-<number>.json`, and returns `{ok: true}`.
- `costReport({runs, now})` requires an array `runs` and nonnegative finite `now`
  (otherwise throws `Error("Invalid cost report input")`) and returns the
  `pdd.cost-report.v1` object.
- `costStatusLines({report})` requires a `report` object with
  `schema === "pdd.cost-report.v1"` (otherwise throws `Error("Invalid cost report")`)
  and returns `{text}`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "788a95f5aa688a716d6fe478c895605f04e8eb01b6a0651772a6a7adf64aca05",
  "entries": [
    {
      "operation": "captureCosts",
      "input_schema": {
        "type": "object",
        "properties": {
          "before": {
            "oneOf": [
              {
                "type": "object",
                "properties": {},
                "required": [],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "runDir": {
                "type": "string"
              },
              "repo": {
                "type": "string"
              },
              "number": {
                "type": "integer"
              },
              "root": {
                "type": "string"
              },
              "state": {
                "type": "string"
              },
              "startedAt": {
                "type": "integer"
              },
              "updatedAt": {
                "type": "integer"
              },
              "agent": {
                "type": "string"
              },
              "configDir": {
                "type": "string"
              },
              "chats": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "agent": {
                      "type": "string"
                    },
                    "configDir": {
                      "type": "string"
                    },
                    "session": {
                      "type": "object",
                      "properties": {
                        "id": {
                          "type": "string"
                        }
                      },
                      "required": [
                        "id"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "agent",
                    "configDir",
                    "session"
                  ],
                  "additionalProperties": false
                }
              },
              "pr": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "number": {
                      "type": "integer"
                    },
                    "state": {
                      "type": "string"
                    },
                    "stage": {
                      "type": "string"
                    },
                    "branch": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "number",
                    "state",
                    "stage",
                    "branch"
                  ],
                  "additionalProperties": false
                }
              },
              "areas": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "name": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "name"
                  ],
                  "additionalProperties": false
                }
              },
              "decisions": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "decision": {
                      "type": "string"
                    },
                    "gateId": {
                      "type": "string"
                    },
                    "gateAt": {
                      "type": "integer"
                    },
                    "at": {
                      "type": "integer"
                    },
                    "stage": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "decision",
                    "gateId",
                    "gateAt",
                    "at",
                    "stage"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "runId"
            ],
            "additionalProperties": false
          },
          "options": {
            "type": "object",
            "properties": {
              "skipCostSessions": {
                "type": "boolean"
              },
              "auditRecords": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {},
                  "required": [],
                  "additionalProperties": false
                }
              },
              "env": {
                "type": "object",
                "properties": {},
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "cost": {
            "type": "object",
            "properties": {
              "schema": {
                "type": "string"
              },
              "capturedAt": {
                "type": "integer"
              },
              "outcome": {
                "type": "string"
              },
              "outcomeAt": {
                "type": "integer"
              },
              "tokens": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "account": {
                      "type": "string"
                    },
                    "agent": {
                      "type": "string"
                    },
                    "input": {
                      "type": "integer"
                    },
                    "cachedInput": {
                      "type": "integer"
                    },
                    "output": {
                      "type": "integer"
                    },
                    "reasoningOutput": {
                      "type": "integer"
                    },
                    "total": {
                      "type": "integer"
                    }
                  },
                  "required": [
                    "account",
                    "agent",
                    "input",
                    "cachedInput",
                    "output",
                    "reasoningOutput",
                    "total"
                  ],
                  "additionalProperties": false
                }
              },
              "sessions": {
                "type": "object",
                "properties": {
                  "eec414bc659da70d2567": {
                    "type": "object",
                    "properties": {
                      "account": {
                        "type": "string"
                      },
                      "agent": {
                        "type": "string"
                      },
                      "offset": {
                        "type": "integer"
                      },
                      "usage": {
                        "type": "object",
                        "properties": {
                          "input": {
                            "type": "integer"
                          },
                          "cachedInput": {
                            "type": "integer"
                          },
                          "output": {
                            "type": "integer"
                          },
                          "reasoningOutput": {
                            "type": "integer"
                          },
                          "total": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "input",
                          "cachedInput",
                          "output",
                          "reasoningOutput",
                          "total"
                        ],
                        "additionalProperties": false
                      },
                      "messages": {
                        "type": "object",
                        "properties": {
                          "3a0de37932e8b19746f2": {
                            "type": "object",
                            "properties": {
                              "input": {
                                "type": "integer"
                              },
                              "cachedInput": {
                                "type": "integer"
                              },
                              "output": {
                                "type": "integer"
                              },
                              "reasoningOutput": {
                                "type": "integer"
                              },
                              "total": {
                                "type": "integer"
                              }
                            },
                            "required": [
                              "input",
                              "cachedInput",
                              "output",
                              "reasoningOutput",
                              "total"
                            ],
                            "additionalProperties": false
                          }
                        },
                        "required": [
                          "3a0de37932e8b19746f2"
                        ],
                        "additionalProperties": false
                      },
                      "observed": {
                        "type": "boolean"
                      }
                    },
                    "required": [
                      "account",
                      "agent",
                      "offset",
                      "usage",
                      "messages",
                      "observed"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [
                  "eec414bc659da70d2567"
                ],
                "additionalProperties": false
              },
              "person": {
                "type": "object",
                "properties": {
                  "questions": {
                    "type": "integer"
                  },
                  "answers": {
                    "type": "integer"
                  },
                  "approvals": {
                    "type": "integer"
                  },
                  "waitingMinutes": {
                    "type": "integer"
                  },
                  "activeMinutes": {
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
                  "questions",
                  "answers",
                  "approvals",
                  "waitingMinutes",
                  "activeMinutes"
                ],
                "additionalProperties": false
              },
              "suiteMinutes": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "ciMinutes": {
                "type": "integer"
              },
              "githubCalls": {
                "type": "integer"
              },
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "at": {
                      "type": "integer"
                    },
                    "metric": {
                      "type": "string"
                    },
                    "value": {
                      "type": "integer"
                    },
                    "account": {
                      "type": "string"
                    },
                    "agent": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "at",
                    "metric",
                    "value"
                  ],
                  "additionalProperties": false
                }
              },
              "measurements": {
                "type": "object",
                "properties": {},
                "required": [],
                "additionalProperties": false
              },
              "coverage": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "waits": {
                "type": "object",
                "properties": {
                  "g:gate-1": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "gateId": {
                        "type": "string"
                      },
                      "at": {
                        "type": "integer"
                      },
                      "accountedAt": {
                        "type": "integer"
                      },
                      "endedAt": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "kind",
                      "gateId",
                      "at",
                      "accountedAt",
                      "endedAt"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [
                  "g:gate-1"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "schema",
              "capturedAt",
              "outcome",
              "outcomeAt",
              "tokens",
              "sessions",
              "person",
              "suiteMinutes",
              "ciMinutes",
              "githubCalls",
              "events",
              "measurements",
              "coverage",
              "waits"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "cost"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": [
        "clock.now",
        "compute.hash_utf8",
        "files.read",
        "files.stat",
        "fs.readdir"
      ]
    },
    {
      "operation": "applyCostMeasurement",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "repo": {
                "type": "string"
              },
              "number": {
                "type": "integer"
              },
              "cost": {
                "type": "object",
                "properties": {
                  "schema": {
                    "type": "string"
                  },
                  "capturedAt": {
                    "type": "integer"
                  },
                  "outcome": {
                    "type": "string"
                  },
                  "outcomeAt": {
                    "type": "integer"
                  },
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "sessions": {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
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
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  },
                  "events": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "measurements": {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  },
                  "coverage": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "waits": {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  }
                },
                "required": [
                  "schema",
                  "capturedAt",
                  "outcome",
                  "outcomeAt",
                  "tokens",
                  "sessions",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls",
                  "events",
                  "measurements",
                  "coverage",
                  "waits"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "runId"
            ],
            "additionalProperties": false
          },
          "input": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              },
              "suiteMinutes": {
                "type": "integer"
              },
              "personMinutes": {
                "type": "integer"
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
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "repo": {
                "type": "string"
              },
              "number": {
                "type": "integer"
              },
              "cost": {
                "type": "object",
                "properties": {
                  "schema": {
                    "type": "string"
                  },
                  "capturedAt": {
                    "type": "integer"
                  },
                  "outcome": {
                    "type": "string"
                  },
                  "outcomeAt": {
                    "type": "integer"
                  },
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "sessions": {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  },
                  "events": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "at": {
                          "type": "integer"
                        },
                        "metric": {
                          "type": "string"
                        },
                        "value": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "at",
                        "metric",
                        "value"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "measurements": {
                    "type": "object",
                    "properties": {
                      "suite-1": {
                        "type": "object",
                        "properties": {
                          "id": {
                            "type": "string"
                          },
                          "personMinutes": {
                            "type": "integer"
                          },
                          "suiteMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "id",
                          "personMinutes",
                          "suiteMinutes"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "suite-1"
                    ],
                    "additionalProperties": false
                  },
                  "coverage": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "waits": {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  }
                },
                "required": [
                  "schema",
                  "capturedAt",
                  "outcome",
                  "outcomeAt",
                  "tokens",
                  "sessions",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls",
                  "events",
                  "measurements",
                  "coverage",
                  "waits"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "runId",
              "repo",
              "number",
              "cost"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "run"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": []
    },
    {
      "operation": "recordCostGithub",
      "input_schema": {
        "type": "object",
        "properties": {
          "runDir": {
            "type": "string"
          },
          "entry": {
            "type": "object",
            "properties": {
              "at": {
                "type": "integer"
              }
            },
            "required": [
              "at"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "runDir",
          "entry"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "ok": {
            "type": "boolean"
          }
        },
        "required": [
          "ok"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": [
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "captureClosedCi",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              },
              "runId": {
                "type": "string"
              },
              "repo": {
                "type": "string"
              },
              "root": {
                "type": "string"
              },
              "pr": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "number": {
                      "type": "integer"
                    },
                    "state": {
                      "type": "string"
                    },
                    "branch": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "number",
                    "state",
                    "branch"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "runDir"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "ok": {
            "type": "boolean"
          }
        },
        "required": [
          "ok"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": [
        "exec.execFile",
        "files.stat",
        "files.write"
      ]
    },
    {
      "operation": "costReport",
      "input_schema": {
        "type": "object",
        "properties": {
          "runs": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "runId": {
                  "type": "string"
                },
                "repo": {
                  "type": "string"
                },
                "number": {
                  "type": "integer"
                },
                "startedAt": {
                  "type": "integer"
                },
                "cost": {
                  "type": "object",
                  "properties": {
                    "schema": {
                      "type": "string"
                    },
                    "capturedAt": {
                      "type": "integer"
                    },
                    "outcome": {
                      "type": "string"
                    },
                    "outcomeAt": {
                      "type": "integer"
                    },
                    "tokens": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "account": {
                            "type": "string"
                          },
                          "agent": {
                            "type": "string"
                          },
                          "input": {
                            "type": "integer"
                          },
                          "cachedInput": {
                            "type": "integer"
                          },
                          "output": {
                            "type": "integer"
                          },
                          "reasoningOutput": {
                            "type": "integer"
                          },
                          "total": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "account",
                          "agent",
                          "input",
                          "cachedInput",
                          "output",
                          "reasoningOutput",
                          "total"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "sessions": {
                      "type": "object",
                      "properties": {},
                      "required": [],
                      "additionalProperties": false
                    },
                    "person": {
                      "type": "object",
                      "properties": {
                        "questions": {
                          "type": "integer"
                        },
                        "answers": {
                          "type": "integer"
                        },
                        "approvals": {
                          "type": "integer"
                        },
                        "waitingMinutes": {
                          "type": "integer"
                        },
                        "activeMinutes": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "questions",
                        "answers",
                        "approvals",
                        "waitingMinutes",
                        "activeMinutes"
                      ],
                      "additionalProperties": false
                    },
                    "suiteMinutes": {
                      "type": "integer"
                    },
                    "ciMinutes": {
                      "type": "integer"
                    },
                    "githubCalls": {
                      "type": "integer"
                    },
                    "events": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "at": {
                            "type": "integer"
                          },
                          "metric": {
                            "type": "string"
                          },
                          "value": {
                            "type": "integer"
                          },
                          "account": {
                            "type": "string"
                          },
                          "agent": {
                            "type": "string"
                          }
                        },
                        "required": [
                          "at",
                          "metric",
                          "value"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "measurements": {
                      "type": "object",
                      "properties": {},
                      "required": [],
                      "additionalProperties": false
                    },
                    "coverage": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    },
                    "waits": {
                      "type": "object",
                      "properties": {},
                      "required": [],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "schema",
                    "capturedAt",
                    "outcome",
                    "outcomeAt",
                    "tokens",
                    "sessions",
                    "person",
                    "suiteMinutes",
                    "ciMinutes",
                    "githubCalls",
                    "events",
                    "measurements",
                    "coverage",
                    "waits"
                  ],
                  "additionalProperties": false
                }
              },
              "required": [
                "runId",
                "repo",
                "number",
                "startedAt",
                "cost"
              ],
              "additionalProperties": false
            }
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
          "schema": {
            "type": "string",
            "enum": [
              "pdd.cost-report.v1"
            ]
          },
          "generatedAt": {
            "type": "number"
          },
          "runs": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "repo": {
                  "type": "string"
                },
                "issue": {
                  "type": "integer"
                },
                "runId": {
                  "type": "string"
                },
                "outcome": {
                  "type": "string"
                },
                "outcomeAt": {
                  "type": "integer"
                },
                "tokens": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "account": {
                        "type": "string"
                      },
                      "agent": {
                        "type": "string"
                      },
                      "input": {
                        "type": "integer"
                      },
                      "cachedInput": {
                        "type": "integer"
                      },
                      "output": {
                        "type": "integer"
                      },
                      "reasoningOutput": {
                        "type": "integer"
                      },
                      "total": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "account",
                      "agent",
                      "input",
                      "cachedInput",
                      "output",
                      "reasoningOutput",
                      "total"
                    ],
                    "additionalProperties": false
                  }
                },
                "person": {
                  "type": "object",
                  "properties": {
                    "questions": {
                      "type": "integer"
                    },
                    "answers": {
                      "type": "integer"
                    },
                    "approvals": {
                      "type": "integer"
                    },
                    "waitingMinutes": {
                      "type": "integer"
                    },
                    "activeMinutes": {
                      "type": "integer"
                    }
                  },
                  "required": [
                    "questions",
                    "answers",
                    "approvals",
                    "waitingMinutes",
                    "activeMinutes"
                  ],
                  "additionalProperties": false
                },
                "suiteMinutes": {
                  "type": "integer"
                },
                "ciMinutes": {
                  "type": "integer"
                },
                "githubCalls": {
                  "type": "integer"
                },
                "coverage": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                }
              },
              "required": [
                "repo",
                "issue",
                "runId",
                "outcome",
                "outcomeAt",
                "tokens",
                "person",
                "suiteMinutes",
                "ciMinutes",
                "githubCalls",
                "coverage"
              ],
              "additionalProperties": false
            }
          },
          "day": {
            "type": "object",
            "properties": {
              "since": {
                "type": "integer"
              },
              "totals": {
                "type": "object",
                "properties": {
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  },
                  "totalTokens": {
                    "type": "integer"
                  }
                },
                "required": [
                  "tokens",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls",
                  "totalTokens"
                ],
                "additionalProperties": false
              },
              "coverage": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "mergedIssues": {
                "type": "integer"
              },
              "p50": {
                "type": "object",
                "properties": {
                  "totalTokens": {
                    "type": "integer"
                  },
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  }
                },
                "required": [
                  "totalTokens",
                  "tokens",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls"
                ],
                "additionalProperties": false
              },
              "p90": {
                "type": "object",
                "properties": {
                  "totalTokens": {
                    "type": "integer"
                  },
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  }
                },
                "required": [
                  "totalTokens",
                  "tokens",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "since",
              "totals",
              "coverage",
              "mergedIssues",
              "p50",
              "p90"
            ],
            "additionalProperties": false
          },
          "week": {
            "type": "object",
            "properties": {
              "since": {
                "type": "integer"
              },
              "totals": {
                "type": "object",
                "properties": {
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  },
                  "totalTokens": {
                    "type": "integer"
                  }
                },
                "required": [
                  "tokens",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls",
                  "totalTokens"
                ],
                "additionalProperties": false
              },
              "coverage": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "mergedIssues": {
                "type": "integer"
              },
              "p50": {
                "type": "object",
                "properties": {
                  "totalTokens": {
                    "type": "integer"
                  },
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  }
                },
                "required": [
                  "totalTokens",
                  "tokens",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls"
                ],
                "additionalProperties": false
              },
              "p90": {
                "type": "object",
                "properties": {
                  "totalTokens": {
                    "type": "integer"
                  },
                  "tokens": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "account": {
                          "type": "string"
                        },
                        "agent": {
                          "type": "string"
                        },
                        "input": {
                          "type": "integer"
                        },
                        "cachedInput": {
                          "type": "integer"
                        },
                        "output": {
                          "type": "integer"
                        },
                        "reasoningOutput": {
                          "type": "integer"
                        },
                        "total": {
                          "type": "integer"
                        }
                      },
                      "required": [
                        "account",
                        "agent",
                        "input",
                        "cachedInput",
                        "output",
                        "reasoningOutput",
                        "total"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "person": {
                    "type": "object",
                    "properties": {
                      "questions": {
                        "type": "integer"
                      },
                      "answers": {
                        "type": "integer"
                      },
                      "approvals": {
                        "type": "integer"
                      },
                      "waitingMinutes": {
                        "type": "integer"
                      },
                      "activeMinutes": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "questions",
                      "answers",
                      "approvals",
                      "waitingMinutes",
                      "activeMinutes"
                    ],
                    "additionalProperties": false
                  },
                  "suiteMinutes": {
                    "type": "integer"
                  },
                  "ciMinutes": {
                    "type": "integer"
                  },
                  "githubCalls": {
                    "type": "integer"
                  }
                },
                "required": [
                  "totalTokens",
                  "tokens",
                  "person",
                  "suiteMinutes",
                  "ciMinutes",
                  "githubCalls"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "since",
              "totals",
              "coverage",
              "mergedIssues",
              "p50",
              "p90"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "schema",
          "generatedAt",
          "runs",
          "day",
          "week"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": []
    },
    {
      "operation": "costStatusLines",
      "input_schema": {
        "type": "object",
        "properties": {
          "report": {
            "type": "object",
            "properties": {
              "schema": {
                "type": "string"
              },
              "generatedAt": {
                "type": "integer"
              },
              "runs": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "repo": {
                      "type": "string"
                    },
                    "issue": {
                      "type": "integer"
                    },
                    "runId": {
                      "type": "string"
                    },
                    "outcome": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "repo",
                    "issue",
                    "runId",
                    "outcome"
                  ],
                  "additionalProperties": false
                }
              },
              "day": {
                "type": "object",
                "properties": {
                  "since": {
                    "type": "integer"
                  },
                  "totals": {
                    "type": "object",
                    "properties": {
                      "tokens": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "account": {
                              "type": "string"
                            },
                            "agent": {
                              "type": "string"
                            },
                            "input": {
                              "type": "integer"
                            },
                            "cachedInput": {
                              "type": "integer"
                            },
                            "output": {
                              "type": "integer"
                            },
                            "reasoningOutput": {
                              "type": "integer"
                            },
                            "total": {
                              "type": "integer"
                            }
                          },
                          "required": [
                            "account",
                            "agent",
                            "input",
                            "cachedInput",
                            "output",
                            "reasoningOutput",
                            "total"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "person": {
                        "type": "object",
                        "properties": {
                          "questions": {
                            "type": "integer"
                          },
                          "answers": {
                            "type": "integer"
                          },
                          "approvals": {
                            "type": "integer"
                          },
                          "waitingMinutes": {
                            "type": "integer"
                          },
                          "activeMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "questions",
                          "answers",
                          "approvals",
                          "waitingMinutes",
                          "activeMinutes"
                        ],
                        "additionalProperties": false
                      },
                      "suiteMinutes": {
                        "type": "integer"
                      },
                      "ciMinutes": {
                        "type": "integer"
                      },
                      "githubCalls": {
                        "type": "integer"
                      },
                      "totalTokens": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "tokens",
                      "person",
                      "suiteMinutes",
                      "ciMinutes",
                      "githubCalls",
                      "totalTokens"
                    ],
                    "additionalProperties": false
                  },
                  "coverage": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "mergedIssues": {
                    "type": "integer"
                  },
                  "p50": {
                    "type": "object",
                    "properties": {
                      "totalTokens": {
                        "type": "integer"
                      },
                      "tokens": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "account": {
                              "type": "string"
                            },
                            "agent": {
                              "type": "string"
                            },
                            "input": {
                              "type": "integer"
                            },
                            "cachedInput": {
                              "type": "integer"
                            },
                            "output": {
                              "type": "integer"
                            },
                            "reasoningOutput": {
                              "type": "integer"
                            },
                            "total": {
                              "type": "integer"
                            }
                          },
                          "required": [
                            "account",
                            "agent",
                            "input",
                            "cachedInput",
                            "output",
                            "reasoningOutput",
                            "total"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "person": {
                        "type": "object",
                        "properties": {
                          "questions": {
                            "type": "integer"
                          },
                          "answers": {
                            "type": "integer"
                          },
                          "approvals": {
                            "type": "integer"
                          },
                          "waitingMinutes": {
                            "type": "integer"
                          },
                          "activeMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "questions",
                          "answers",
                          "approvals",
                          "waitingMinutes",
                          "activeMinutes"
                        ],
                        "additionalProperties": false
                      },
                      "suiteMinutes": {
                        "type": "integer"
                      },
                      "ciMinutes": {
                        "type": "integer"
                      },
                      "githubCalls": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "totalTokens",
                      "tokens",
                      "person",
                      "suiteMinutes",
                      "ciMinutes",
                      "githubCalls"
                    ],
                    "additionalProperties": false
                  },
                  "p90": {
                    "type": "object",
                    "properties": {
                      "totalTokens": {
                        "type": "integer"
                      },
                      "tokens": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "account": {
                              "type": "string"
                            },
                            "agent": {
                              "type": "string"
                            },
                            "input": {
                              "type": "integer"
                            },
                            "cachedInput": {
                              "type": "integer"
                            },
                            "output": {
                              "type": "integer"
                            },
                            "reasoningOutput": {
                              "type": "integer"
                            },
                            "total": {
                              "type": "integer"
                            }
                          },
                          "required": [
                            "account",
                            "agent",
                            "input",
                            "cachedInput",
                            "output",
                            "reasoningOutput",
                            "total"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "person": {
                        "type": "object",
                        "properties": {
                          "questions": {
                            "type": "integer"
                          },
                          "answers": {
                            "type": "integer"
                          },
                          "approvals": {
                            "type": "integer"
                          },
                          "waitingMinutes": {
                            "type": "integer"
                          },
                          "activeMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "questions",
                          "answers",
                          "approvals",
                          "waitingMinutes",
                          "activeMinutes"
                        ],
                        "additionalProperties": false
                      },
                      "suiteMinutes": {
                        "type": "integer"
                      },
                      "ciMinutes": {
                        "type": "integer"
                      },
                      "githubCalls": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "totalTokens",
                      "tokens",
                      "person",
                      "suiteMinutes",
                      "ciMinutes",
                      "githubCalls"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [
                  "since",
                  "totals",
                  "coverage",
                  "mergedIssues",
                  "p50",
                  "p90"
                ],
                "additionalProperties": false
              },
              "week": {
                "type": "object",
                "properties": {
                  "since": {
                    "type": "integer"
                  },
                  "totals": {
                    "type": "object",
                    "properties": {
                      "tokens": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "account": {
                              "type": "string"
                            },
                            "agent": {
                              "type": "string"
                            },
                            "input": {
                              "type": "integer"
                            },
                            "cachedInput": {
                              "type": "integer"
                            },
                            "output": {
                              "type": "integer"
                            },
                            "reasoningOutput": {
                              "type": "integer"
                            },
                            "total": {
                              "type": "integer"
                            }
                          },
                          "required": [
                            "account",
                            "agent",
                            "input",
                            "cachedInput",
                            "output",
                            "reasoningOutput",
                            "total"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "person": {
                        "type": "object",
                        "properties": {
                          "questions": {
                            "type": "integer"
                          },
                          "answers": {
                            "type": "integer"
                          },
                          "approvals": {
                            "type": "integer"
                          },
                          "waitingMinutes": {
                            "type": "integer"
                          },
                          "activeMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "questions",
                          "answers",
                          "approvals",
                          "waitingMinutes",
                          "activeMinutes"
                        ],
                        "additionalProperties": false
                      },
                      "suiteMinutes": {
                        "type": "integer"
                      },
                      "ciMinutes": {
                        "type": "integer"
                      },
                      "githubCalls": {
                        "type": "integer"
                      },
                      "totalTokens": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "tokens",
                      "person",
                      "suiteMinutes",
                      "ciMinutes",
                      "githubCalls",
                      "totalTokens"
                    ],
                    "additionalProperties": false
                  },
                  "coverage": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "mergedIssues": {
                    "type": "integer"
                  },
                  "p50": {
                    "type": "object",
                    "properties": {
                      "totalTokens": {
                        "type": "integer"
                      },
                      "tokens": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "account": {
                              "type": "string"
                            },
                            "agent": {
                              "type": "string"
                            },
                            "input": {
                              "type": "integer"
                            },
                            "cachedInput": {
                              "type": "integer"
                            },
                            "output": {
                              "type": "integer"
                            },
                            "reasoningOutput": {
                              "type": "integer"
                            },
                            "total": {
                              "type": "integer"
                            }
                          },
                          "required": [
                            "account",
                            "agent",
                            "input",
                            "cachedInput",
                            "output",
                            "reasoningOutput",
                            "total"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "person": {
                        "type": "object",
                        "properties": {
                          "questions": {
                            "type": "integer"
                          },
                          "answers": {
                            "type": "integer"
                          },
                          "approvals": {
                            "type": "integer"
                          },
                          "waitingMinutes": {
                            "type": "integer"
                          },
                          "activeMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "questions",
                          "answers",
                          "approvals",
                          "waitingMinutes",
                          "activeMinutes"
                        ],
                        "additionalProperties": false
                      },
                      "suiteMinutes": {
                        "type": "integer"
                      },
                      "ciMinutes": {
                        "type": "integer"
                      },
                      "githubCalls": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "totalTokens",
                      "tokens",
                      "person",
                      "suiteMinutes",
                      "ciMinutes",
                      "githubCalls"
                    ],
                    "additionalProperties": false
                  },
                  "p90": {
                    "type": "object",
                    "properties": {
                      "totalTokens": {
                        "type": "integer"
                      },
                      "tokens": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "account": {
                              "type": "string"
                            },
                            "agent": {
                              "type": "string"
                            },
                            "input": {
                              "type": "integer"
                            },
                            "cachedInput": {
                              "type": "integer"
                            },
                            "output": {
                              "type": "integer"
                            },
                            "reasoningOutput": {
                              "type": "integer"
                            },
                            "total": {
                              "type": "integer"
                            }
                          },
                          "required": [
                            "account",
                            "agent",
                            "input",
                            "cachedInput",
                            "output",
                            "reasoningOutput",
                            "total"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "person": {
                        "type": "object",
                        "properties": {
                          "questions": {
                            "type": "integer"
                          },
                          "answers": {
                            "type": "integer"
                          },
                          "approvals": {
                            "type": "integer"
                          },
                          "waitingMinutes": {
                            "type": "integer"
                          },
                          "activeMinutes": {
                            "type": "integer"
                          }
                        },
                        "required": [
                          "questions",
                          "answers",
                          "approvals",
                          "waitingMinutes",
                          "activeMinutes"
                        ],
                        "additionalProperties": false
                      },
                      "suiteMinutes": {
                        "type": "integer"
                      },
                      "ciMinutes": {
                        "type": "integer"
                      },
                      "githubCalls": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "totalTokens",
                      "tokens",
                      "person",
                      "suiteMinutes",
                      "ciMinutes",
                      "githubCalls"
                    ],
                    "additionalProperties": false
                  }
                },
                "required": [
                  "since",
                  "totals",
                  "coverage",
                  "mergedIssues",
                  "p50",
                  "p90"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "schema"
            ],
            "additionalProperties": false
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
          "text": {
            "type": "string"
          }
        },
        "required": [
          "text"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "clock",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "now",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ms": {
                "type": "integer"
              }
            },
            "required": [
              "ms"
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
              "value"
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
          "name": "execFile",
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
              "args",
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "code": {
                "type": "integer"
              },
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              }
            },
            "required": [
              "code",
              "stdout",
              "stderr"
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
              "content"
            ],
            "additionalProperties": false
          }
        },
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
                "type": "integer"
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
              },
              "code": {
                "type": "string"
              }
            },
            "required": [
              "entries"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 64,
    "max_model_calls": 16
  },
  "conventions": []
}
```
</details>
