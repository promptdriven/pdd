# Machine interpreter queue

Own `src/interpreter-queue.mjs`. Bound simultaneous lint and check requests across
repositories, worktrees, runtime hosts and agent profiles of one OS user. This
queue owns machine capacity and request measurements. Existing runtime slots own
profile leases; the runtime client alone owns dispatch and safe retry authority.

Use the shared full-suite queue design: ordered persistent tickets, atomic record
replacement and the native PID/token admission lock. Never hold the lock across
network work or sleep. Default directory is `/tmp/pdd-interpreter-UID`; an absolute
`PDD_INTERPRETER_QUEUE` overrides it. `PDD_INTERPRETER_CONCURRENCY` is a positive safe
integer, default 2. Invalid capacity uses 2 with a warning. A relative directory
or unreadable queue fails closed before POST. An admission lock with malformed,
non-regular, unreadable or unverifiable PID/token ownership fails immediately with
`local-state-unavailable`; never steal it. Only verified live contention may wait.
Lock creation or storage failure fails promptly with `local-state-unavailable`.
An absent lock after contention can mean that its holder released it: retry only
while the root is still a regular directory. Every lock retry yields and checks
interruption and the caller deadline; each admission-lock wait is bounded by five
seconds, including repeated release races. Capacity waiting keeps its own caller
deadline and is not limited to five seconds.
Dispatch marking and observation try an uncontended update even during cleanup,
but stop waiting on interruption or deadline, and within five seconds otherwise.
A cancelled dispatch mark forbids POST. A failed observation keeps the prior
dispatch evidence and capacity for later same-ID recovery. Keep state outside
the checkout,
private to the OS user; never save credentials, request bodies or response prose.

Export `interpreterQueueEnvironment(env)` returning the effective
`PDD_INTERPRETER_QUEUE` and `PDD_INTERPRETER_CONCURRENCY` as strings under the
settings above, so workflow launch and status use the same queue.

Export `acquireInterpreterSlot({cwd, origin, requestId, kind, env, deadline}, ports)`
for lint/check only. Return `{root,ticket}` after admission, or null at deadline or
interruption. `deadline` is absolute epoch milliseconds, Infinity by default.
Register a waiting ticket, then admit the oldest live waiter when active count is
below capacity and the shared busy pause has ended. Position counts waiting tickets
including this one, from 1. Report changed positions as
`waiting for an interpreter slot (position N)`. End and retain unsent waiters on
cancellation. At every admission attempt, under the admission lock, check PID
liveness for all waiting and running tickets. Finish and persist tickets with a
confirmed dead owner, including dispatched holders, before counting capacity or
FIFO position. Set `releaseReason: "owner-dead"`, `endedAt` to the cleanup time,
and `activeAtEnd` to the running count before that release. Keep ticket identity,
dispatch evidence, start measurements and any observed outcome. Without an
observed outcome, use `unknown` for dispatched tickets and `not_sent` for unsent
tickets. PID permission errors or uncertain liveness do not prove death.
A live dispatched request without a terminal receipt retains capacity after
interruption. Releasing a dead owner's local capacity never authorizes a resend
or infers a verdict. Duplicate request identities remain refused. Later terminal
same-ID evidence may replace a reclaimed dispatched ticket's unknown outcome once, without releasing
capacity again or replacing its release reason and measurements.

Export `observeInterpreterRequest({env,origin,requestId,outcome,terminal,busy,waitMs}, ports)`.
Outcomes are `verdict`, `unknown`, `refused`, `busy`, or `not_sent`. Record each
observation for that exact request only. Terminal evidence releases its machine
slot; lost responses and stopped polling record unknown and retain it. Recovery
by the same saved ID can finish a retained ticket. Repeated terminal observations
are idempotent. Busy feedback (`busy:true`, including uncertain capacity replies) halves the
shared effective cap, minimum 1, for 60 seconds and pauses new admissions for the
server wait clamped to 1 through 60 seconds (default 5 seconds). Uncertain feedback
never authorizes replay or releases capacity. After the 60-second window, each
successful verdict increases capacity by one up to the configured limit. A refusal
or unknown never increases it. Each caller's configured limit is also a hard cap.

Persist one request ledger row per ticket. Fields are `ticket` (positive sequence),
`pid`, `cwd` (absolute worktree), `origin`, `requestId`, `kind` (lint/check), `state`
(waiting/running/finished), `queuedAt`, `startedAt`, `endedAt` (epoch milliseconds;
start/end null until observed), `outcome` (above or null), `activeAtStart`,
`activeAtEnd` (nonnegative request counts, start includes this request; end counts
before releasing it), and `dispatched` (whether POST may have started). An optional `releaseReason`
is `owner-dead` only when admission reclaimed a dead owner; older rows omit it. Expose
`markInterpreterDispatch({root,ticket}, ports)` before POST. A failed mark forbids
POST. Preserve unknown observations and permit later confirmed completion to
replace them. Admission and all terminal ledger writes are serialized. An error
before dispatch finishes an unsent ticket. No durable dispatch record is retried.

Export `readInterpreterProgress({cwd,since=0,env}, ports)` returning null without
records, else `{state,position,pausedMs,requests}`. `requests` are ledger rows for
that cwd in ticket order. `state` and `position` describe the earliest waiting ticket, otherwise the earliest unfinished
ticket (position null unless waiting), else finished. `pausedMs` is the union of
waiting intervals clipped to since/now; running time is excluded. A dead waiter
ends at its record mtime. Observation is read-only. Unreadable state returns
`{state:"unavailable",reason,pausedMs:0,requests:[]}`. Unknown state never proves
inactivity. Export `interpreterStatusWords(progress)` for waiting, running,
finished or unavailable status. Stuck detection excludes saved wait intervals and
never declares an actively waiting or unreadable queue stuck. Workflow status
shows the waiting words in text and its `words` JSON field without waking a chat.

## Autopilot test mode

Export configureInterpreterTestMode({env,owner,enabled},ports). Use the same queue admission lock and capacity file. Keep a map testOwners of owner paths to lease expiry timestamps; enabling renews a one-hour lease and disabling removes only this owner. Admission has limit one while any lease is current. A terminal verdict clears the leases so ordinary interpreter capacity returns immediately. Preserve the busy cooldown and unknown-result ownership. The tick calls this only after its three-no-verdict pattern, never after one failure. Reuse injected filesystem, clock, PID and lock ports. No second queue.

## Dependencies

- [Native admission lock](workflow-runner.prompt.md#native-admission-lock): required
  independent binding for `acquireRunLock(directory, filename)`; no workflow
  execution policy is required.
- Native Node filesystem, path, PID liveness, clock and UUID facilities supply
  defaults. Inject `fs`, `now`, `sleep`, `alive`, `pid`, `uuid`, `acquireLock`,
  `interrupted` and `say` for controlled local behavior. Admission checks the
  deadline and interruption before each update and after lock acquisition.

In the Runtime interface, `interpreterQueueEnvironment`, `acquireInterpreterSlot`, `markInterpreterDispatch`, `observeInterpreterRequest`, `readInterpreterProgress`, `interpreterStatusWords` and `configureInterpreterTestMode` use the `files` blob resource (`read`, `write`, `stat` for `<root>/ticket-<N>.json` and `<root>/capacity.json`), `fs` port (`readdir`, `mkdir`), `lock.acquire({directory, filename})`, `process` port (`pid`, `alive`, `interrupted`), `clock.now()` and `output.say({text})`. `readInterpreterProgress` returns `{state: null, position: null, pausedMs: 0, requests: []}` when no records exist for `cwd`. Invalid queue configuration, invalid request kind, duplicate request identity, dispatch ownership mismatch or missing test-mode owner raise `local-state-unavailable`. Native atomic temp-file rename (`wx` + `renameSync`), lock contention sleep loops and cross-process races stay a native obligation covered by `test/interpreter-queue.test.mjs`, `test/interpreter-queue-runtime.test.mjs`, `test/interpreter-queue-storage.test.mjs` and `test/interpreter-queue-repair.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "dd90908901d69308da646c7e53fca12fa4f3be7a01beda78d2d5d2dd7ff0fa6c",
  "entries": [
    {
      "operation": "interpreterQueueEnvironment",
      "input_schema": {
        "type": "object",
        "properties": {
          "env": {
            "type": "object",
            "properties": {
              "PDD_INTERPRETER_QUEUE": {
                "type": "string"
              },
              "PDD_INTERPRETER_CONCURRENCY": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
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
          "PDD_INTERPRETER_QUEUE": {
            "type": "string"
          },
          "PDD_INTERPRETER_CONCURRENCY": {
            "type": "string"
          }
        },
        "required": [
          "PDD_INTERPRETER_QUEUE",
          "PDD_INTERPRETER_CONCURRENCY"
        ],
        "additionalProperties": false
      },
      "errors": [
        "local-state-unavailable"
      ],
      "resource_operations": [
        "output.say"
      ]
    },
    {
      "operation": "acquireInterpreterSlot",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "origin": {
            "type": "string"
          },
          "requestId": {
            "type": "string"
          },
          "kind": {
            "type": "string"
          },
          "env": {
            "type": "object",
            "properties": {
              "PDD_INTERPRETER_QUEUE": {
                "type": "string"
              },
              "PDD_INTERPRETER_CONCURRENCY": {
                "type": "string"
              }
            },
            "required": [
              "PDD_INTERPRETER_QUEUE"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "cwd",
          "origin",
          "requestId",
          "kind",
          "env"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "root": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "ticket": {
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
          "root",
          "ticket"
        ],
        "additionalProperties": false
      },
      "errors": [
        "local-state-unavailable"
      ],
      "resource_operations": [
        "files.read",
        "files.write",
        "files.stat",
        "fs.readdir",
        "fs.mkdir",
        "lock.acquire",
        "process.pid",
        "process.alive",
        "process.interrupted",
        "clock.now",
        "output.say"
      ]
    },
    {
      "operation": "markInterpreterDispatch",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          },
          "ticket": {
            "type": "integer"
          }
        },
        "required": [
          "root",
          "ticket"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [
        "local-state-unavailable"
      ],
      "resource_operations": [
        "files.read",
        "files.write",
        "files.stat",
        "lock.acquire",
        "process.pid",
        "process.interrupted",
        "clock.now"
      ]
    },
    {
      "operation": "observeInterpreterRequest",
      "input_schema": {
        "type": "object",
        "properties": {
          "env": {
            "type": "object",
            "properties": {
              "PDD_INTERPRETER_QUEUE": {
                "type": "string"
              },
              "PDD_INTERPRETER_CONCURRENCY": {
                "type": "string"
              }
            },
            "required": [
              "PDD_INTERPRETER_QUEUE"
            ],
            "additionalProperties": false
          },
          "origin": {
            "type": "string"
          },
          "requestId": {
            "type": "string"
          },
          "outcome": {
            "type": "string"
          },
          "terminal": {
            "type": "boolean"
          },
          "busy": {
            "type": "boolean"
          },
          "waitMs": {
            "type": "integer"
          }
        },
        "required": [
          "env",
          "origin",
          "requestId",
          "outcome",
          "terminal"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [
        "local-state-unavailable"
      ],
      "resource_operations": [
        "files.read",
        "files.write",
        "files.stat",
        "fs.readdir",
        "lock.acquire",
        "process.alive",
        "process.interrupted",
        "clock.now"
      ]
    },
    {
      "operation": "readInterpreterProgress",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "since": {
            "type": "integer"
          },
          "env": {
            "type": "object",
            "properties": {
              "PDD_INTERPRETER_QUEUE": {
                "type": "string"
              }
            },
            "required": [
              "PDD_INTERPRETER_QUEUE"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "cwd",
          "env"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "state": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "position": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          },
          "pausedMs": {
            "type": "integer"
          },
          "reason": {
            "type": "string"
          },
          "requests": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "ticket": {
                  "type": "integer"
                },
                "pid": {
                  "type": "integer"
                },
                "cwd": {
                  "type": "string"
                },
                "origin": {
                  "type": "string"
                },
                "requestId": {
                  "type": "string"
                },
                "kind": {
                  "type": "string"
                },
                "state": {
                  "type": "string"
                },
                "queuedAt": {
                  "type": "integer"
                },
                "startedAt": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "endedAt": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "outcome": {
                  "oneOf": [
                    {
                      "type": "string"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "activeAtStart": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "activeAtEnd": {
                  "oneOf": [
                    {
                      "type": "integer"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "dispatched": {
                  "type": "boolean"
                }
              },
              "required": [
                "ticket",
                "pid",
                "cwd",
                "origin",
                "requestId",
                "kind",
                "state",
                "queuedAt",
                "startedAt",
                "endedAt",
                "outcome",
                "activeAtStart",
                "activeAtEnd",
                "dispatched"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "state",
          "pausedMs",
          "requests"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "files.read",
        "files.stat",
        "fs.readdir",
        "process.alive",
        "clock.now"
      ]
    },
    {
      "operation": "interpreterStatusWords",
      "input_schema": {
        "type": "object",
        "properties": {
          "progress": {
            "type": "object",
            "properties": {
              "state": {
                "type": "string"
              },
              "position": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "reason": {
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
          "progress"
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
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "configureInterpreterTestMode",
      "input_schema": {
        "type": "object",
        "properties": {
          "env": {
            "type": "object",
            "properties": {
              "PDD_INTERPRETER_QUEUE": {
                "type": "string"
              }
            },
            "required": [
              "PDD_INTERPRETER_QUEUE"
            ],
            "additionalProperties": false
          },
          "owner": {
            "type": "string"
          },
          "enabled": {
            "type": "boolean"
          }
        },
        "required": [
          "env",
          "owner",
          "enabled"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {},
        "required": [],
        "additionalProperties": false
      },
      "errors": [
        "local-state-unavailable"
      ],
      "resource_operations": [
        "files.read",
        "files.write",
        "files.stat",
        "fs.mkdir",
        "lock.acquire",
        "process.interrupted",
        "clock.now"
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
        }
      ]
    },
    {
      "name": "fs",
      "kind": "port",
      "access": "write",
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
              "exists": {
                "type": "boolean"
              },
              "isDirectory": {
                "type": "boolean"
              },
              "entries": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "exists",
              "isDirectory",
              "entries"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "mkdir",
          "access": "write",
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
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "lock",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "acquire",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "directory": {
                "type": "string"
              },
              "filename": {
                "type": "string"
              }
            },
            "required": [
              "directory",
              "filename"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "acquired": {
                "type": "boolean"
              }
            },
            "required": [
              "acquired"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "process",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "pid",
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
              "pid": {
                "type": "integer"
              }
            },
            "required": [
              "pid"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "alive",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "pid": {
                "type": "integer"
              }
            },
            "required": [
              "pid"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "alive": {
                "type": "boolean"
              }
            },
            "required": [
              "alive"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "interrupted",
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
              "interrupted": {
                "type": "boolean"
              }
            },
            "required": [
              "interrupted"
            ],
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
      "name": "output",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "say",
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
    "max_steps": 64,
    "max_model_calls": 16
  },
  "conventions": []
}
```
</details>
