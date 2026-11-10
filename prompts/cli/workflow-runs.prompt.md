# Run records

Own `src/workflow-runs.mjs`. A run is one workflow for one issue. Its record is `status.json` in the run folder `<git common dir>/pdd/runs/<issue number>/`. The record is the run state and also the status shape that phone clients read (C3, `v:1`).

## Owner and projections

The run record is the sole durable workflow/chat owner. The run index, stageAgent, phone view, process lock and assignments are lookup, observation or exclusion views; none can override its chat custody. Persist run-level `layout` custody with repository/run workspace IDs and their initial root tab/pane/terminal IDs, alongside chat IDs; its IDs are live-checked lookup hints and cleanup custody, never authority over contradictory live Herdr identity. Preserve the [runner lifecycle](workflow-runner.prompt.md#chat-lifecycle) fields and positive evidence on every write, deriving index and stageAgent consistently. Missing state on legacy chats is unknown unless explicit saved launch custody derives starting; absence never creates ended evidence. Index repair never changes runId, commonDir, root, native session or workflow progress.

## Record

Saved fields: `runId`, `workflow`, `repo`, `issue {number,title,url,asked?}`, `number`, `root` (worktree), `branch`, `baseBranch`, `sourceRoot`, `commonDir`, `runDir`, `agent`, `configDir`, `startedAt`, `state` (running, waiting, completed, cancelled), `areas`, `area` (index), `done` (step → `{at, summary, area}`), `gate` (`{area, at, kind, id, promptSnapshot?, storySnapshot?, storyChanges?}` or null; kind `approve`, `approve-pr` (Try before PR 1) or `ask-code`), `question` (`{text, at, area}` or null, from `pdd workflow ask`), `chats` (one per area chat: `{area, tabId, paneId, workspaceId, label, startedAt, session, configDir, state, evidence?, code?}`), `decisions`, `changes`, `approvalRecord`, `pr` (one entry per PR: `{stage, number, url, branch, base, state, ci}`), `prBase`, `doneAt`, `prState`, `cancelled`, `warnings`, optional `productMarker` (string), optional `replayAdoption` (immutable declaration copy/digest and origin provenance, owned by the [runner](workflow-runner.prompt.md#adopt-an-existing-approved-corpus)), optional `chatFailure {area, phase, code, message, at}`, optional `through` (`prompt-pr` or `code`) and optional `storyApproval {gateId, evidenceId, at, fingerprint, prompts}` (both owned by the [runner](workflow-runner.prompt.md#normal-run-gates)). The runner owns failure/recovery policy; chat records may retain `startUnconfirmed: true` for an uncertain pane launch.

`draft` is an optional saved Boolean publication policy owned by the
[runner](workflow-runner.prompt.md#draft-publication-policy). New runs save it
explicitly; a legacy missing field means false. A present nonboolean value is
invalid, never a truthy publication request. Preserve it across ordinary writes,
reloads and area transitions; storage never infers or changes policy from PR state.

`writeRun(record, ports)` adds the C3 view, increments `journalSeq`, sets `updatedAt`, and writes the file atomically (temporary file, then rename). It also updates the index of known runs in `<stateDir>/runs.json` (default `~/.local/state/pdd`). An index failure is ignored. `readRun(runDir)` returns the record or null.

## Concurrent record updates

Module function `updateRun(runDir, update, ports = {})` synchronously returns the
committed record. `update` is a synchronous callback receiving the latest durable
record and returning the record to save. Reading that record, applying the
callback and publishing its result form one indivisible update for this run,
including across processes. Successful updates of unrelated fields retain both
writers' effects. The callback owns its intended changes; storage does not infer
them from an arbitrary old snapshot.
Ordinary ownership uses `<run folder>/.ordinary-owner` and publishes complete owner
PID, hostname and a unique token atomically. Reclaim only a confirmed dead owner
on the same host. Live, foreign-host, malformed and unverifiable ownership,
including permission-check failures, stays protected; age alone proves nothing.
Release or reclaim only the observed token, so an older owner cannot remove its
replacement. A dead owner's leftover ownership must not prevent cancellation.
Keep the private ownership algorithm free.

Module function `readRunOwnership(runDir, ports = {})` returns `null` when ordinary
ownership is absent, otherwise a snapshot `{path, pid, hostname, token, warning}`.
`path` names `.ordinary-owner`; unavailable PID, hostname or token fields are
`null`. A complete readable owner has `warning: null`; unreadable or malformed
ownership has a finite diagnostic string in `warning`, retaining available facts.
This public read performs no acquisition, recovery, release or durable write.

The callback may mutate its supplied record, but must preserve its run identity
and perform only local state changes. A missing or unreadable existing record,
callback failure or failed publication fails finitely without claiming a commit;
never create an existing run from a stale fallback. Before publication, retain the
previous durable bytes on failure. Always release only this invocation's ownership.
Ownership covers no external Git, GitHub, Herdr or model effects, readiness waits,
journal claim acquisition or nested ordinary save. Storage/ownership effects have
injectable native boundaries with production defaults. Contention fails with a
finite diagnostic naming the ownership path and available owner details, with one retry instruction. Ordinary acquisition while a delivery
journal claim is held must wait less than its 250 ms claim budget, never block the
main thread there for five seconds. Retain journal-before-ordinary ordering.

`writeRun(record, ports)` retains its synchronous signature, supplied-object
mutation and returned record, and its explicit whole-record save capability. Its
publication participates in the same ownership boundary; it cannot interrupt an
`updateRun` between read and commit. It does not infer an untracked caller's intent.
`updateRun` uses the same C3 derivation, sequence, timestamp and best-effort index
semantics as `writeRun`, applied to the record being committed. An index failure
does not undo or misreport that commit.
Neither function reads or writes the delivery journal.

Preserve optional `productMarker` when the runner supplies it. Its capture and
PR propagation belong to [the workflow runner](workflow-runner.prompt.md#product-run-association).
An older record without the field stays valid; this module does not infer one.

An active current-area `chatFailure` takes precedence in `waitingFor`: no approval decisions, a finite reason with the error code, and `pdd workflow open N`. It does not create or clear a gate. Cancelled/completed records ignore stale failure data; normal waiting views return after the runner clears the failure.

C3 view: `stage` (current step, or `approve` at a gate, or `merge` after the last PR), `steps` (each step with area, state done/current/next, times, agent, session and summary), `waitingFor` (`{decisions:['changes'], what: QUESTION}` while a question waits; `{decisions:['approve','changes'], what}` at a gate, with what "Make the code PR now, or stop here and merge PR 1" at the code-or-stop gate, also after PR 1 merged, `{decisions:[], what:'Review and merge the PR on GitHub'}` after the PR, else `{decisions:[], what:null}`), `resumeDecisions`, `waitingDecision`, `herdr`, `stageAgent`, `links:[]`, `controller:null`, `message`.

`updateRunCosts(runDir, update, ports={})` uses the same local ownership,
latest-record validation, synchronous callback and attempt-identity checks as
`updateRun`. It commits only the callback's `cost`, refreshed through the cost
ledger; other callback changes are discarded. Cost capture failure retains prior
cost data with incomplete coverage. Preserve workflow fields, `updatedAt`,
`journalSeq`, index and completion journal. Do not deliver metrics on this route.
Save optional `progressAt` (milliseconds) as the prior status file's mtime on the
first cost-only publication; later cost publications retain it. Ordinary
`writeRun` and ordinary `updateRun` clear `progressAt`, so the newly published file's mtime
again marks workflow activity. Read the prior mtime through the injected run
filesystem. Publish cost data atomically; a failed callback or publication leaves
the prior record intact. This keeps cost polling from postponing stalled-run
warnings, including for legacy records.

## Approval history

Keep legacy decisions and approvalRecord readable. New gates have a nonempty string `id`, stable through save/reload and publication retry and distinct for each new or changed/reopened gate independently of clock, area or kind. Legacy gates without id remain readable. Preserve optional `gate.promptSnapshot` as an ordered array of `{path,proseSha256,reviewSha256?}` rows, including an empty array. Absence means unbound, not an empty selection. The runner owns capture, invalidation and comparison; storage must preserve these distinctions through reload and projection. Each new approval decision and approvalRecord adds nonempty string `gateId` identifying its gate. Each new approval decision retains `gateAt` (the approved gate's original at value) and adds `evidence` with the exact shared [evidence shape](approval-policy.prompt.md#actor-and-evidence), alongside existing stage/decision/via/at/text fields; `approvalRecord` retains its legacy fields and the same evidence. Decisions are the complete gate history, not only the latest approvalRecord. The runner supplies the facts; this storage module never invents actors, words or approval. Preserve every record through atomic write/read and C3 projection; old records lacking evidence stay valid and must not gain invented provenance. The shared prompt journal remains separate from status.json.

Before every publication, capture the local [cost ledger](cost-ledger.prompt.md) from the previous durable run and the current record. Keep its cumulative numeric checkpoints in `cost`. Capture failure retains prior cost data with incomplete coverage and never blocks workflow progress.

## Archived run lookup

Include archived ended runs when resolving a run by its invoking worktree,
before selecting a current issue record or any other active run. Use the actual
archive directory as runDir even for a legacy record with a stale saved path.
Preserve the runner's replacedBy, chat closed, endedAt and openedAt fields through
storage. An archived worktree must never resolve to the replacement run.

For workflow session observations and cleanup only, updateRun accepts ports.preserveProgress=true. Preserve the callback's progressAt across publication while still advancing updatedAt, journalSeq, derived view and the index. The runner initializes missing progressAt from the pre-maintenance updatedAt, then startedAt, then 0. Ordinary worker mutations retain the default clearing rule, so actual progress restarts idle grace. This is not the cost-only route and cannot suppress journal capture or ordinary ownership checks.

## Dependencies

- [Cost ledger](cost-ledger.prompt.md): required native generation and verification context for local cost capture and reports.

- [Metrics hooks](metrics-hooks.prompt.md): required native generation/verification context for journal construction and retained delivery. [Metrics gaps](metrics-gap.prompt.md) owns fallback coverage events.

- [Approval policy and journal](approval-policy.prompt.md): required authoring/generation/native-production/verification/testing context for the evidence value schema; no reverse dependency on runner.

## Selection

- `gitContext(cwd, ports)` returns `{toplevel, commonDir}` (real paths) or null.
- `runForWorktree(cwd, ports)` returns the run whose `root` is the current worktree.
- `resolveRun(ref, {cwd}, ports)` returns `{run}` or `{error}`. `N` looks in the current repository, worktrees included. Outside a repository it uses the index; when several repositories have issue N, it asks for `owner/repo#N`. `owner/repo#N` and issue URLs pick that repository. Without ref: the run of the current worktree, else the only run of this repository that waits for a person, else the only active run; otherwise list the choices.
- `listRuns({cwd}, ports)` returns the runs of the current repository, or all indexed runs outside a repository.
- `allRuns({cancelled}, ports)` returns every run on this machine. It finds the repositories only from the run index (`<stateDir>/runs.json`), never from a Herdr layout registry, then reads each `<commonDir>/pdd/runs/<N>/status.json`. With `cancelled` it also reads the renamed `<N>-cancelled-<id>` folders. Deduplicate by saved run directory, runId and startedAt together; an archived attempt can retain the same runDir as its replacement and must remain distinct. A repository or file that is gone or unreadable is skipped without an error.

Before each atomic run publication, journal retained completion facts with stable installation identity and unique transition identity in the same status record. Initialize installation identity and capture-start time on first capture. On capture failure retain a visible incomplete-coverage warning and preserve ordinary progress. After publication retry delivery of the retained journal; a failure is visible and never gates execution.

Capture journal construction consumes pending observations only on success; preserve them and a coverage gap for later retry on failure. Optional metrics syncing never gates the original atomic status publication.

Retain the ordinary injected pathname-write and atomic-rename publication behavior. Capture, delivery, coverage-gap and warning callbacks are best effort; even a throwing warning must not stop ordinary progress or turn a committed rename into failure. Asynchronous drain rejection must be contained. Native status write and rename failures retain their ordinary errors. Optional identity and gap storage use injected filesystem ports for controlled failure verification.

- In Runtime checks, `files.stat({path})`, `files.read({path})` and `files.write({path, content})` read and write `<runDir>/status.json`, `<runDir>/.ordinary-owner` and `<stateDir>/runs.json`; `fs.readdir({path})` lists `<commonDir>/pdd/runs`; `fs.realpath({path})` resolves canonical paths; `fs.mtime({path})` reads the prior status file modification timestamp (`mtimeMs`) for `updateRunCosts`; `ownership.acquire({runDir})` and `ownership.release({runDir, token})` bind `.ordinary-owner` acquisition and token release; `clock.now({})` supplies `{iso}`; `git.revParse({cwd})` returns `{status, toplevel, commonDir}`; `cost.captureCosts({runDir})` and `metrics.journalRunMutation({runDir})` bind cost and metrics hooks. `writeRun` fails with `invalid_run_record` when `record.runDir` or `record.runId` is empty; `readRun` and `readRunOwnership` fail with `invalid_run_dir` when `runDir` is empty; `updateRun` and `updateRunCosts` fail with `run_ownership_busy` when ownership is held or `run_missing` when `status.json` is absent; `gitContext`, `runForWorktree`, `resolveRun` and `listRuns` fail with `invalid_cwd` when `cwd` is empty; `allRuns` fails with `invalid_state_dir` when `stateDir` is empty. Native cross-process rename atomicity and PID liveness probes stay in `test/approval-merge-races.test.mjs` and `test/autopilot-claim-expiry.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "dca8bcb6a33bcb01d66edde4448d3fcd6b092c6519d5ac9e54f1e2217909a9b3",
  "entries": [
    {
      "operation": "writeRun",
      "input_schema": {
        "type": "object",
        "properties": {
          "record": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "runDir": {
                "type": "string"
              },
              "commonDir": {
                "type": "string"
              },
              "root": {
                "type": "string"
              },
              "repo": {
                "type": "string"
              },
              "number": {
                "type": "integer"
              },
              "workflow": {
                "type": "string"
              },
              "state": {
                "type": "string"
              },
              "journalSeq": {
                "type": "integer"
              },
              "draft": {
                "type": "boolean"
              },
              "chatFailure": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "area": {
                        "type": "string"
                      },
                      "phase": {
                        "type": "string"
                      },
                      "code": {
                        "type": "string"
                      },
                      "message": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "area",
                      "phase",
                      "code",
                      "message",
                      "at"
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
              "runId",
              "runDir",
              "commonDir",
              "root",
              "repo",
              "number",
              "workflow",
              "state"
            ],
            "additionalProperties": false
          },
          "stateDir": {
            "type": "string"
          }
        },
        "required": [
          "record",
          "stateDir"
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
              "runDir": {
                "type": "string"
              },
              "state": {
                "type": "string"
              },
              "journalSeq": {
                "type": "integer"
              },
              "updatedAt": {
                "type": "string"
              },
              "draft": {
                "type": "boolean"
              }
            },
            "required": [
              "runId",
              "runDir",
              "state",
              "journalSeq",
              "updatedAt",
              "draft"
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
        "invalid_run_record",
        "run_ownership_busy"
      ],
      "resource_operations": [
        "ownership.acquire",
        "ownership.release",
        "clock.now",
        "cost.captureCosts",
        "metrics.journalRunMutation",
        "files.stat",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "readRun",
      "input_schema": {
        "type": "object",
        "properties": {
          "runDir": {
            "type": "string"
          }
        },
        "required": [
          "runDir"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "run": {
            "oneOf": [
              {
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
                  "state": {
                    "type": "string"
                  },
                  "journalSeq": {
                    "type": "integer"
                  }
                },
                "required": [
                  "runId",
                  "runDir",
                  "repo",
                  "number",
                  "state",
                  "journalSeq"
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
          "run"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_run_dir"
      ],
      "resource_operations": [
        "files.stat",
        "files.read"
      ]
    },
    {
      "operation": "updateRun",
      "input_schema": {
        "type": "object",
        "properties": {
          "runDir": {
            "type": "string"
          },
          "state": {
            "type": "string"
          },
          "preserveProgress": {
            "type": "boolean"
          },
          "stateDir": {
            "type": "string"
          }
        },
        "required": [
          "runDir",
          "state",
          "stateDir"
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
              "runDir": {
                "type": "string"
              },
              "state": {
                "type": "string"
              },
              "journalSeq": {
                "type": "integer"
              },
              "updatedAt": {
                "type": "string"
              },
              "progressAt": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "runId",
              "runDir",
              "state",
              "journalSeq",
              "updatedAt",
              "progressAt"
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
        "run_ownership_busy",
        "run_missing"
      ],
      "resource_operations": [
        "ownership.acquire",
        "ownership.release",
        "clock.now",
        "cost.captureCosts",
        "metrics.journalRunMutation",
        "files.stat",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "readRunOwnership",
      "input_schema": {
        "type": "object",
        "properties": {
          "runDir": {
            "type": "string"
          }
        },
        "required": [
          "runDir"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "snapshot": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "path": {
                    "type": "string"
                  },
                  "pid": {
                    "oneOf": [
                      {
                        "type": "integer"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "hostname": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "token": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "warning": {
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
                  "path",
                  "pid",
                  "hostname",
                  "token",
                  "warning"
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
          "snapshot"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_run_dir"
      ],
      "resource_operations": [
        "files.stat",
        "files.read"
      ]
    },
    {
      "operation": "updateRunCosts",
      "input_schema": {
        "type": "object",
        "properties": {
          "runDir": {
            "type": "string"
          },
          "suiteMinutes": {
            "type": "number"
          }
        },
        "required": [
          "runDir",
          "suiteMinutes"
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
              "journalSeq": {
                "type": "integer"
              },
              "updatedAt": {
                "type": "string"
              },
              "progressAt": {
                "type": "integer"
              },
              "suiteMinutes": {
                "type": "number"
              }
            },
            "required": [
              "runId",
              "journalSeq",
              "updatedAt",
              "progressAt",
              "suiteMinutes"
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
        "run_missing",
        "run_ownership_busy"
      ],
      "resource_operations": [
        "ownership.acquire",
        "ownership.release",
        "fs.mtime",
        "cost.captureCosts",
        "files.stat",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "gitContext",
      "input_schema": {
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
          "context": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "toplevel": {
                    "type": "string"
                  },
                  "commonDir": {
                    "type": "string"
                  }
                },
                "required": [
                  "toplevel",
                  "commonDir"
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
          "context"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_cwd"
      ],
      "resource_operations": [
        "git.revParse",
        "fs.realpath"
      ]
    },
    {
      "operation": "runForWorktree",
      "input_schema": {
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
          "run": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "runId": {
                    "type": "string"
                  },
                  "runDir": {
                    "type": "string"
                  },
                  "root": {
                    "type": "string"
                  },
                  "state": {
                    "type": "string"
                  }
                },
                "required": [
                  "runId",
                  "runDir",
                  "root",
                  "state"
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
          "run"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_cwd"
      ],
      "resource_operations": [
        "git.revParse",
        "fs.realpath",
        "fs.readdir",
        "files.stat",
        "files.read"
      ]
    },
    {
      "operation": "resolveRun",
      "input_schema": {
        "type": "object",
        "properties": {
          "ref": {
            "type": "string"
          },
          "cwd": {
            "type": "string"
          },
          "stateDir": {
            "type": "string"
          }
        },
        "required": [
          "ref",
          "cwd",
          "stateDir"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "runId": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
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
          "runId",
          "error"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_cwd"
      ],
      "resource_operations": [
        "git.revParse",
        "fs.realpath",
        "fs.readdir",
        "files.stat",
        "files.read"
      ]
    },
    {
      "operation": "listRuns",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "stateDir": {
            "type": "string"
          }
        },
        "required": [
          "cwd",
          "stateDir"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "runIds": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "runIds"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_cwd"
      ],
      "resource_operations": [
        "git.revParse",
        "fs.realpath",
        "fs.readdir",
        "files.stat",
        "files.read"
      ]
    },
    {
      "operation": "allRuns",
      "input_schema": {
        "type": "object",
        "properties": {
          "cancelled": {
            "type": "boolean"
          },
          "stateDir": {
            "type": "string"
          }
        },
        "required": [
          "cancelled",
          "stateDir"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "runIds": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "runIds"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_state_dir"
      ],
      "resource_operations": [
        "fs.readdir",
        "files.stat",
        "files.read"
      ]
    }
  ],
  "calls": [],
  "resources": [
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
        },
        {
          "name": "realpath",
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
              "realpath": {
                "type": "string"
              }
            },
            "required": [
              "realpath"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "mtime",
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
              "mtimeMs": {
                "type": "integer"
              }
            },
            "required": [
              "mtimeMs"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "ownership",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "acquire",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              }
            },
            "required": [
              "runDir"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "acquired": {
                "type": "boolean"
              },
              "token": {
                "type": "string"
              }
            },
            "required": [
              "acquired",
              "token"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "release",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              },
              "token": {
                "type": "string"
              }
            },
            "required": [
              "runDir",
              "token"
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
              "iso": {
                "type": "string"
              }
            },
            "required": [
              "iso"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "git",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "revParse",
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
              "status": {
                "type": "integer"
              },
              "toplevel": {
                "type": "string"
              },
              "commonDir": {
                "type": "string"
              }
            },
            "required": [
              "status",
              "toplevel",
              "commonDir"
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
          "name": "captureCosts",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              }
            },
            "required": [
              "runDir"
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
      "name": "metrics",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "journalRunMutation",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              }
            },
            "required": [
              "runDir"
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
    "max_steps": 48,
    "max_model_calls": 16
  },
  "conventions": []
}
```
</details>
