# Metrics report command

`src/metrics-command.mjs` exports module function `runMetrics({argv, cwd, stdout, stderr, ports})`, returning an exit code. The PDD CLI invokes it for `pdd metrics`. It uses the [calculator](metrics-model.prompt.md) and [ledger](metrics-store.prompt.md); it does not duplicate their policy. It obtains repository, selector, GitHub, clock, and storage observations through supplied ports. It never creates a second scheduler or dependency analyzer. Preserve invocation and observable effects; implementation details may vary.

`pdd metrics` displays the current queue. `--date YYYY-MM-DD` selects activity on that date; `--snapshot ID` selects a fixed issue group; `--timezone IANA` declares the report timezone; `--json` emits the same calculation as terminal text. The report identifies its repository, selection, timezone, cutoff, sources and gaps and includes issue lists and reasons. `export FILE` writes a shareable ledger bundle; `import FILE` unions a compatible bundle. `record FILE` appends explicit sourced events, including human reports, outcome and recovery facts. Reject invalid options, date/timezone, missing input or inaccessible storage with a nonzero result and explanatory stderr. Do not imply absent machines are covered or that local facts prove all users' starts. Sharing occurs only through explicit export.

Runtime wraps the native numeric exit code as `{exitCode}`. `runMetrics` catches errors, writes a diagnostic to stderr and returns 1; it does not raise `storage-unavailable`. Bind actual Git/GitHub subprocess observations through `process.execFile`, historical directory and file observations through `fs.readdir` and `fs.readFile`, clock through `clock.now`, output through `output.stdout` and `output.stderr`, and import/export files through `files.read` and `files.write`. Call the shared metrics-store and metrics-model owners for persistence and calculation. Existing high-level optional ports remain native caller/test seams; they are not Runtime substitutes for those decisions. Native process termination, Git patch-id and filesystem journal details remain obligations (`test/metrics-command.test.mjs`).

## Dependencies

- [GitHub calls](github-calls.prompt.md): native generation and verification context for counting `gh` calls.

[Metrics calculator](metrics-model.prompt.md): required for calculation in authoring, generation and native testing. [Metrics ledger](metrics-store.prompt.md): required for record import/export in authoring, generation and native testing.


Backfill never treats workflow creation time as a confirmed worker start. A live queue without a current selector observation has unknown selector state; do not copy prior state into a new observation. Fetch explicitly mapped PRs and retain observed current heads only for code mappings, and merged delivery evidence, without converting a prompt-only PR into code delivery. Checker comments are observations, not proof of acceptance merely because their head matches. Pass participating source metadata to the calculator. Export uses the installed CLI version.

Terminal output presents stage and transition fractions with percentages and unknowns, activity, origins, assistance, readiness, PR creation, waits, follow-up, coverage and evidence links from the same calculation as JSON. Fetch current-head CI check runs independently of checker verdicts and represent failed, missing and unknown observations distinctly without adding a gate.

A structured pdd-check comment supplies verdict, head, risk, family, session, checker mode and evidence. Recognize supported checker modes `same-family` and `different-family`, with substantive evidence in a string, array or object; empty, boolean or meaningless evidence is not proof. Preserve checker family and mode alongside complete safe session identifiers, including slash-separated IDs in a reversible path-safe encoding; do not export a local path or raw comment. For high risk, split results and check/merge/approval changes, require two agreeing fresh sessions on the exact head. Reused or ambiguous session identity is unknown; Compare family identities case-insensitively while preserving the original recorded identity; two checks of the same family require the same-family fallback label. Preserve an explicit supported equivalence assessment; missing facts remain unknown. Setup success is not a check.

When no GitHub origin is configured, a repository can be identified offline from an unambiguous local ledger repository; ambiguous or absent identity is an error. Unavailable GitHub observations are an explicit source gap.

`--at UTC-TIMESTAMP` sets the report observation cutoff; use `--expected-source ID...` to declare expected sources, including absent machines. Reject malformed IDs and timestamps.

A stale-head checker PASS can support an equivalent current head only when local Git computes equal nonempty patch IDs for both heads and GitHub reports a completed green full-suite check on that exact current SHA. Retain the original observation and the equivalent assessment separately; unavailable proof remains unknown.

Replay durable launcher decision journals after checking their file identity, repository, issue and event envelopes, even when no run directory exists. Surface recorded capture gaps.

A historical cutoff requires `--snapshot` or `--date`; a present-day GitHub queue cannot establish historical membership. Remote observations retain their actual observation time and are filtered at the cutoff.

Live reports and exports retain normalized GitHub observations in the ledger before export, including current candidate heads, public checker references, CI and explicit deliveries. A later observation may refine acceptance of the same comment without changing the underlying comment identity; preserve contradictory claims. Export remains useful offline and reveals unavailable GitHub coverage. Current queue reports open issue readiness as unknown when validity is unavailable. Present the latest saved selector snapshot separately with its identity, observation time, membership, state, reasons and current-validity limit, including empty snapshots.

Only trusted checker comments may establish acceptance: repository owner, write-access collaborator, or a person explicitly trusted in pdd.json. Unknown author trust remains unknown. Do not export author names or raw comment text.

Replay complete published selector snapshots and fallback capture-gap records in addition to run journals and compatible decision records. Ignore uncommitted partial snapshots; report incomplete coverage.

When a GitHub read fails, retain an incomplete coverage observation for known issues at that observation time. A later successful read does not erase the earlier gap.

Historical saved-step backfill is a fallback: do not generate a completion already represented by the same run journal fact with matching repository, issue, attempt, step, done status and saved time. Match known areas when both exist; missing area does not prove a difference. Preserve all journal and ledger observations, other statuses and times, and uncovered saved facts. For queue and cohort reports, omit activity counts and direct people to --date for daily activity.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "fd9ae7755680a14e138c17bd1736e2425c9802ecd807c89acd37917115aeaf46",
  "entries": [
    {
      "operation": "runMetrics",
      "input_schema": {
        "type": "object",
        "properties": {
          "argv": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "cwd": {
            "type": "string"
          }
        },
        "required": [],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "exitCode": {
            "type": "integer"
          }
        },
        "required": [
          "exitCode"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "process.execFile",
        "fs.readdir",
        "fs.readFile",
        "clock.now",
        "files.read",
        "files.write",
        "output.stdout",
        "output.stderr"
      ]
    }
  ],
  "calls": [
    {
      "operation": "runMetrics",
      "target": "prompts/cli/metrics-store.prompt.md",
      "target_operation": "readEvents",
      "max_calls": 1
    },
    {
      "operation": "runMetrics",
      "target": "prompts/cli/metrics-store.prompt.md",
      "target_operation": "appendEvents",
      "max_calls": 3
    },
    {
      "operation": "runMetrics",
      "target": "prompts/cli/metrics-store.prompt.md",
      "target_operation": "exportMetrics",
      "max_calls": 1
    },
    {
      "operation": "runMetrics",
      "target": "prompts/cli/metrics-store.prompt.md",
      "target_operation": "importMetrics",
      "max_calls": 1
    },
    {
      "operation": "runMetrics",
      "target": "prompts/cli/metrics-model.prompt.md",
      "target_operation": "calculateMetrics",
      "max_calls": 2
    }
  ],
  "resources": [
    {
      "name": "process",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "execFile",
          "access": "write",
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
              },
              "maxBuffer": {
                "type": "integer",
                "minimum": 0
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
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              },
              "error": {
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
              "stdout",
              "stderr",
              "error"
            ],
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
              "error": {
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
              "entries",
              "error"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "readFile",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              },
              "encoding": {
                "type": "string"
              }
            },
            "required": [
              "path",
              "encoding"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": {
                "type": "string"
              },
              "error": {
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
              "content",
              "error"
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
                "type": "number"
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
      "name": "output",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "stdout",
          "access": "write",
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
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        },
        {
          "name": "stderr",
          "access": "write",
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
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 32,
    "max_model_calls": 16
  },
  "conventions": []
}
```
</details>
