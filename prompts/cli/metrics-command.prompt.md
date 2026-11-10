# Metrics report command

`src/metrics-command.mjs` exports module function `runMetrics({argv, cwd, stdout, stderr, ports})`, returning an exit code. The PDD CLI invokes it for `pdd metrics`. It uses the [calculator](metrics-model.prompt.md) and [ledger](metrics-store.prompt.md); it does not duplicate their policy. It obtains repository, selector, GitHub, clock, and storage observations through supplied ports. It never creates a second scheduler or dependency analyzer. Preserve invocation and observable effects; implementation details may vary.

`pdd metrics` displays the current queue. `--date YYYY-MM-DD` selects activity on that date; `--snapshot ID` selects a fixed issue group; `--timezone IANA` declares the report timezone; `--json` emits the same calculation as terminal text. The report identifies its repository, selection, timezone, cutoff, sources and gaps and includes issue lists and reasons. `export FILE` writes a shareable ledger bundle; `import FILE` unions a compatible bundle. `record FILE` appends explicit sourced events, including human reports, outcome and recovery facts. Reject invalid options, date/timezone, missing input or inaccessible storage with a nonzero result and explanatory stderr. Do not imply absent machines are covered or that local facts prove all users' starts. Sharing occurs only through explicit export.

Bind repository discovery through `repository.identify({cwd})`, observation time through `clock.now({})`, live queue selection through `selector.observe({cwd, repo})`, GitHub PR/comment/CI inspection through `github.observe({cwd, repo})`, ledger persistence through `store.loadLedger`, `store.saveEvents`, `store.createBundle` and `store.applyBundle`, metric calculation through `calculate.buildReport`, bundle/record file I/O through `files.read` and `files.write`, and terminal output through `output.stdout` and `output.stderr`. `runMetrics({argv, cwd})` returns `{exitCode}` (`0` on success, `1` with explanatory `output.stderr` on invalid options, historical `--at` without `--snapshot` or `--date`, or ambiguous repository identity) and raises `storage-unavailable` when `cwd` is blank. Native `gh`/`git` subprocess execution and filesystem journal scanning remain native obligations (`test/metrics-command.test.mjs`).

The native gh runner records each `gh` call in the GitHub call ledger of the repository that the call names, through `nativeGithubCounter` of [GitHub calls](github-calls.prompt.md#ledger), with the purpose `other`. Counting never changes a call or its result; an injected `execFile` is not wrapped.

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
  "prose_sha256": "5d408f66078f30659ce42b6119f7171561e3b82a2438b978d25e0efe46a1533f",
  "entries": [
    {
      "operation": "runMetrics",
      "input_schema": {
        "type": "object",
        "properties": {
          "argv": {
            "type": "array",
            "items": { "type": "string" }
          },
          "cwd": { "type": "string" }
        },
        "required": ["argv", "cwd"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "exitCode": { "type": "integer" }
        },
        "required": ["exitCode"],
        "additionalProperties": false
      },
      "errors": ["storage-unavailable"],
      "resource_operations": [
        "repository.identify",
        "clock.now",
        "selector.observe",
        "github.observe",
        "store.loadLedger",
        "store.saveEvents",
        "store.createBundle",
        "store.applyBundle",
        "calculate.buildReport",
        "files.read",
        "files.write",
        "output.stdout",
        "output.stderr"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "repository",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "identify",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": { "type": "string" }
            },
            "required": ["cwd"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "repo": {
                "oneOf": [
                  { "type": "string" },
                  { "type": "null" }
                ]
              }
            },
            "required": ["repo"],
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
              "now": { "type": "string" }
            },
            "required": ["now"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "selector",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "observe",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": { "type": "string" },
              "repo": { "type": "string" }
            },
            "required": ["cwd", "repo"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "available": { "type": "boolean" },
              "issues": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "number": { "type": "integer" },
                    "state": { "type": "string" },
                    "reasons": {
                      "type": "array",
                      "items": { "type": "string" }
                    }
                  },
                  "required": ["number", "state", "reasons"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["available", "issues"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "github",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "observe",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": { "type": "string" },
              "repo": { "type": "string" }
            },
            "required": ["cwd", "repo"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "available": { "type": "boolean" },
              "prs": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "number": { "type": "integer" },
                    "issue": { "type": "integer" },
                    "head": { "type": "string" },
                    "merged": { "type": "boolean" }
                  },
                  "required": ["number", "issue", "head", "merged"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["available", "prs"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "store",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "loadLedger",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": { "type": "string" }
            },
            "required": ["root"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "issue": { "type": "integer" },
                    "type": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" }
                  },
                  "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source"],
                  "additionalProperties": false
                }
              },
              "sources": {
                "type": "array",
                "items": { "type": "string" }
              }
            },
            "required": ["events", "sources"],
            "additionalProperties": false
          }
        },
        {
          "name": "saveEvents",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": { "type": "string" },
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "issue": { "type": "integer" },
                    "type": { "type": "string" }
                  },
                  "required": ["id", "repo", "issue", "type"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["root", "events"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" }
            },
            "required": ["ok"],
            "additionalProperties": false
          }
        },
        {
          "name": "createBundle",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": { "type": "string" },
              "metadata": {
                "type": "object",
                "properties": {
                  "repo": { "type": "string" },
                  "timezone": { "type": "string" },
                  "exportedAt": { "type": "string" }
                },
                "required": ["repo", "timezone", "exportedAt"],
                "additionalProperties": false
              }
            },
            "required": ["root", "metadata"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "bundle": {
                "type": "object",
                "properties": {
                  "schema": { "type": "string" },
                  "scope": { "type": "string" },
                  "repo": { "type": "string" },
                  "timezone": { "type": "string" },
                  "exportedAt": { "type": "string" }
                },
                "required": ["schema", "scope", "repo", "timezone", "exportedAt"],
                "additionalProperties": false
              }
            },
            "required": ["bundle"],
            "additionalProperties": false
          }
        },
        {
          "name": "applyBundle",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": { "type": "string" },
              "bundle": {
                "type": "object",
                "properties": {
                  "schema": { "type": "string" },
                  "repo": { "type": "string" }
                },
                "required": ["schema", "repo"],
                "additionalProperties": false
              }
            },
            "required": ["root", "bundle"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" }
            },
            "required": ["ok"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "calculate",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "buildReport",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "repo": { "type": "string" },
              "timezone": { "type": "string" },
              "observedAt": { "type": "string" }
            },
            "required": ["repo", "timezone", "observedAt"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "report": {
                "type": "object",
                "properties": {
                  "repo": { "type": "string" },
                  "timezone": { "type": "string" },
                  "observedAt": { "type": "string" },
                  "issueCount": { "type": "integer" },
                  "readyCount": { "type": "integer" }
                },
                "required": ["repo", "timezone", "observedAt", "issueCount", "readyCount"],
                "additionalProperties": false
              }
            },
            "required": ["report"],
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
              "path": { "type": "string" }
            },
            "required": ["path"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": { "type": "string" }
            },
            "required": ["content"],
            "additionalProperties": false
          }
        },
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" },
              "content": { "type": "string" }
            },
            "required": ["path", "content"],
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
              "text": { "type": "string" }
            },
            "required": ["text"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" }
            },
            "required": ["ok"],
            "additionalProperties": false
          }
        },
        {
          "name": "stderr",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "text": { "type": "string" }
            },
            "required": ["text"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" }
            },
            "required": ["ok"],
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
